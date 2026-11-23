#!/usr/bin/env python3
"""
Fit Insights - a personal, injury-aware health app.

What it does
  - Pulls Fitbit data (sleep, steps, heart rate, HRV, calories) from the Google Health API (v4)
  - Workout log with an exercise directory, training splits and back-safe exercise picks
  - Food logging by voice note or text (Gemini estimates calories), water and supplements
  - Weight, calorie deficit and cardio load tracking
  - Blood report analysis (Gemini reads a PDF or photo)
  - A mind coach for the slip -> anxiety -> avoidance loop, with "comeback" gamification
  - Weekly summary

Run on your own computer:   python3 api/index.py   then open http://localhost:8080
Run online (so it works on your phone): this same file is the Vercel function (api/index.py).
On Vercel nothing can be saved to disk, so it stores everything in a Postgres database whose
address Vercel passes in as DATABASE_URL. README.md has click-by-click steps.

On your own computer it uses only Python's standard library (no pip installs). Everything you log is stored
next to this file in fit.db. Keys live in config.json. Never upload config.json,
token.json or fit.db anywhere.
"""
import base64
import hashlib
import hmac
import json
import os
import re
import secrets
import socket
import sqlite3
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import webbrowser
from datetime import date, datetime, timedelta, timezone
from http import HTTPStatus
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

HERE = os.path.dirname(os.path.abspath(__file__))
CONFIG_FILE = os.path.join(HERE, "config.json")
TOKEN_FILE = os.path.join(HERE, "token.json")
DB_FILE = os.path.join(HERE, "fit.db")
PORT = int(os.environ.get("PORT", "8080"))
# Online: where the data lives, and whether we are on a host that cannot keep files (Vercel).
DATABASE_URL = os.environ.get("DATABASE_URL") or os.environ.get("POSTGRES_URL") or ""
SERVERLESS = bool(os.environ.get("VERCEL") or os.environ.get("VERCEL_URL") or os.environ.get("AWS_LAMBDA_FUNCTION_NAME"))
MAX_UPLOAD = 3_000_000 if SERVERLESS else 15 * 1024 * 1024  # Vercel refuses requests over 4.5 MB

AUTH_URL = os.environ.get("AUTH_URL", "https://accounts.google.com/o/oauth2/v2/auth")
TOKEN_URL = os.environ.get("TOKEN_URL", "https://oauth2.googleapis.com/token")
API_BASE = os.environ.get("API_BASE", "https://health.googleapis.com/v4/users/me")
GEMINI_BASE = os.environ.get("GEMINI_BASE", "https://generativelanguage.googleapis.com/v1beta")
GEMINI_FALLBACK_MODEL = "gemini-3.8-flash"

SCOPES = [
    "https://www.googleapis.com/auth/googlehealth.sleep.readonly",
    "https://www.googleapis.com/auth/googlehealth.activity_and_fitness.readonly",
    "https://www.googleapis.com/auth/googlehealth.health_metrics_and_measurements.readonly",
]

RAW_TYPES = [
    "steps", "sleep", "heart-rate", "daily-resting-heart-rate",
    "heart-rate-variability", "daily-heart-rate-variability",
    "oxygen-saturation", "daily-oxygen-saturation", "daily-respiratory-rate",
    "distance", "active-minutes", "active-zone-minutes", "total-calories",
    "exercise", "daily-vo2-max", "floors",
]

# ------------------------------------------------------------ exercise directory
SPLITS = {
    "Back + Biceps": ["back", "biceps"],
    "Chest + Triceps + Shoulders": ["chest", "triceps", "shoulders"],
    "Legs": ["legs"],
    "Core": ["core"],
    "Cardio + Mobility": ["cardio", "mobility"],
}
ROTATION = ["Back + Biceps", "Chest + Triceps + Shoulders", "Legs", "Core"]

# name | muscle group | equipment | spinal load (1 low, 2 medium, 3 high) | neck load (0/1) | safer swap
# Spinal-load ratings are general gym guidance for a sensitive lower back, not medical advice.
_EXERCISES = """
Lat Pulldown (wide grip)|back|cable|1|0|
Lat Pulldown (neutral close grip)|back|cable|1|0|
Lat Pulldown (reverse grip)|back|cable|1|0|
Single-Arm Lat Pulldown|back|cable|1|0|
Behind-the-Neck Lat Pulldown|back|cable|2|1|Lat Pulldown (wide grip)
Straight-Arm Cable Pulldown|back|cable|1|0|
Chest-Supported Machine Row|back|machine|1|0|
Chest-Supported Dumbbell Row (incline bench)|back|dumbbell|1|0|
Chest-Supported T-Bar Row|back|machine|1|0|
Hammer Strength Row (seated)|back|machine|1|0|
Seated Cable Row|back|cable|2|0|Chest-Supported Machine Row
Single-Arm Cable Row (seated)|back|cable|2|0|Chest-Supported Machine Row
Single-Arm Dumbbell Row (bench supported)|back|dumbbell|2|0|Chest-Supported Dumbbell Row (incline bench)
Standing T-Bar Row|back|barbell|3|0|Chest-Supported T-Bar Row
Bent-Over Barbell Row|back|barbell|3|0|Chest-Supported Dumbbell Row (incline bench)
Pendlay Row|back|barbell|3|0|Chest-Supported Machine Row
Assisted Pull-Up (machine)|back|machine|1|0|
Pull-Up|back|bodyweight|1|0|
Chin-Up|back|bodyweight|1|0|
Inverted Row|back|bodyweight|1|0|
Face Pull|back|cable|1|0|
Dumbbell Pullover|back|dumbbell|2|0|Straight-Arm Cable Pulldown
Back Extension (45 degree)|back|bodyweight|2|0|Bird-Dog
Conventional Deadlift|back|barbell|3|0|Cable Pull-Through
Rack Pull|back|barbell|3|0|Chest-Supported Machine Row
Dumbbell Shrug|back|dumbbell|2|1|Face Pull
Barbell Shrug|back|barbell|2|1|Face Pull
Dumbbell Bicep Curl (seated)|biceps|dumbbell|1|0|
Dumbbell Bicep Curl (standing)|biceps|dumbbell|1|0|
Hammer Curl|biceps|dumbbell|1|0|
Incline Dumbbell Curl|biceps|dumbbell|1|0|
Concentration Curl|biceps|dumbbell|1|0|
Spider Curl|biceps|dumbbell|1|0|
EZ-Bar Curl|biceps|barbell|1|0|
Barbell Curl (standing)|biceps|barbell|2|0|EZ-Bar Curl
Preacher Curl (machine)|biceps|machine|1|0|
Preacher Curl (EZ-bar)|biceps|barbell|1|0|
Machine Bicep Curl|biceps|machine|1|0|
Cable Curl (straight bar)|biceps|cable|1|0|
Rope Hammer Curl (cable)|biceps|cable|1|0|
Bayesian Cable Curl|biceps|cable|1|0|
Dumbbell Chest Press (flat)|chest|dumbbell|1|0|
Incline Dumbbell Press|chest|dumbbell|1|0|
Machine Chest Press (seated)|chest|machine|1|0|
Incline Machine Press|chest|machine|1|0|
Smith Machine Bench Press|chest|machine|1|0|
Cable Chest Press (seated)|chest|cable|1|0|
Cable Chest Press (standing)|chest|cable|2|0|Cable Chest Press (seated)
Barbell Bench Press|chest|barbell|2|0|Dumbbell Chest Press (flat)
Incline Barbell Bench Press|chest|barbell|2|0|Incline Dumbbell Press
Decline Bench Press|chest|barbell|2|0|Machine Chest Press (seated)
Pec Deck Fly|chest|machine|1|0|
Cable Crossover (high to low)|chest|cable|1|0|
Cable Fly (low to high)|chest|cable|1|0|
Dumbbell Fly|chest|dumbbell|1|0|
Push-Up|chest|bodyweight|1|0|
Incline Push-Up|chest|bodyweight|1|0|
Chest Dip|chest|bodyweight|2|0|Machine Chest Press (seated)
Tricep Rope Pushdown|triceps|cable|1|0|
Straight-Bar Pushdown|triceps|cable|1|0|
Single-Arm Cable Pushdown|triceps|cable|1|0|
Overhead Dumbbell Tricep Extension (seated, back supported)|triceps|dumbbell|1|0|
Overhead Cable Tricep Extension (standing)|triceps|cable|2|0|Tricep Rope Pushdown
Skull Crusher (EZ-bar)|triceps|barbell|1|0|
Machine Tricep Extension|triceps|machine|1|0|
Tricep Dip Machine|triceps|machine|1|0|
Bench Dip|triceps|bodyweight|1|0|
Close-Grip Bench Press|triceps|barbell|2|0|Skull Crusher (EZ-bar)
Dumbbell Kickback|triceps|dumbbell|2|0|Single-Arm Cable Pushdown
Machine Shoulder Press|shoulders|machine|2|0|Landmine Press (half-kneeling)
Seated Dumbbell Shoulder Press (back supported)|shoulders|dumbbell|2|0|Landmine Press (half-kneeling)
Arnold Press (seated)|shoulders|dumbbell|2|0|Landmine Press (half-kneeling)
Landmine Press (half-kneeling)|shoulders|barbell|1|0|
Standing Barbell Overhead Press|shoulders|barbell|3|0|Machine Shoulder Press
Behind-the-Neck Press|shoulders|barbell|3|1|Machine Shoulder Press
Dumbbell Lateral Raise|shoulders|dumbbell|1|0|
Cable Lateral Raise|shoulders|cable|1|0|
Machine Lateral Raise|shoulders|machine|1|0|
Dumbbell Front Raise|shoulders|dumbbell|1|0|
Reverse Pec Deck (rear delt)|shoulders|machine|1|0|
Chest-Supported Rear Delt Raise|shoulders|dumbbell|1|0|
Bent-Over Rear Delt Raise|shoulders|dumbbell|2|0|Reverse Pec Deck (rear delt)
Upright Row|shoulders|barbell|2|1|Cable Lateral Raise
Leg Extension|legs|machine|1|0|
Seated Leg Curl|legs|machine|1|0|
Lying Leg Curl|legs|machine|1|0|
Hip Abduction Machine|legs|machine|1|0|
Hip Adduction Machine|legs|machine|1|0|
Glute Bridge|legs|bodyweight|1|0|
Glute Kickback (cable or machine)|legs|cable|1|0|
Belt Squat|legs|machine|1|0|
Step-Up|legs|dumbbell|1|0|
Wall Sit|legs|bodyweight|1|0|
Seated Calf Raise|legs|machine|1|0|
Leg Press Calf Raise|legs|machine|1|0|
Leg Press (limited depth, back flat on pad)|legs|machine|2|0|Belt Squat
Hack Squat Machine|legs|machine|2|0|Belt Squat
Goblet Squat|legs|dumbbell|2|0|Belt Squat
Smith Machine Squat|legs|machine|2|0|Belt Squat
Bulgarian Split Squat|legs|dumbbell|2|0|Step-Up
Reverse Lunge|legs|dumbbell|2|0|Step-Up
Walking Lunge|legs|dumbbell|2|0|Step-Up
Hip Thrust (barbell)|legs|barbell|2|0|Glute Bridge
Cable Pull-Through|legs|cable|2|0|Glute Bridge
Standing Calf Raise (machine)|legs|machine|2|0|Seated Calf Raise
Barbell Back Squat|legs|barbell|3|0|Belt Squat
Front Squat|legs|barbell|3|0|Belt Squat
Romanian Deadlift|legs|barbell|3|0|Seated Leg Curl
Stiff-Leg Deadlift|legs|barbell|3|0|Lying Leg Curl
Good Morning|legs|barbell|3|0|Glute Bridge
McGill Curl-Up|core|bodyweight|1|0|
Bird-Dog|core|bodyweight|1|0|
Dead Bug|core|bodyweight|1|0|
Front Plank|core|bodyweight|1|0|
Side Plank|core|bodyweight|1|0|
Pallof Press|core|cable|1|0|
Stir-the-Pot (Swiss ball)|core|bodyweight|1|0|
Bear Crawl Hold|core|bodyweight|1|0|
Glute Bridge March|core|bodyweight|1|0|
Suitcase Carry|core|dumbbell|2|0|Side Plank
Farmer's Carry|core|dumbbell|2|0|Front Plank
Cable Woodchop|core|cable|2|0|Pallof Press
Hanging Knee Raise|core|bodyweight|2|0|Dead Bug
Lying Leg Raise|core|bodyweight|2|0|Dead Bug
Crunch|core|bodyweight|2|0|McGill Curl-Up
Mountain Climber|core|bodyweight|2|0|Bear Crawl Hold
Sit-Up|core|bodyweight|3|0|McGill Curl-Up
Russian Twist|core|bodyweight|3|0|Pallof Press
Cable Crunch|core|cable|3|0|McGill Curl-Up
Ab Wheel Rollout|core|bodyweight|3|0|Stir-the-Pot (Swiss ball)
Walking (flat)|cardio|none|1|0|
Incline Treadmill Walk|cardio|machine|1|0|
Elliptical|cardio|machine|1|0|
Recumbent Bike|cardio|machine|1|0|
Swimming|cardio|none|1|0|
Stationary Bike (upright)|cardio|machine|2|0|Recumbent Bike
Stair Climber|cardio|machine|2|0|Incline Treadmill Walk
Jogging / Running|cardio|none|2|0|Incline Treadmill Walk
Outdoor Cycling|cardio|none|2|0|Recumbent Bike
Rowing Machine|cardio|machine|3|0|Elliptical
Skipping Rope|cardio|none|3|0|Elliptical
Cat-Cow|mobility|bodyweight|1|0|
Prone Press-Up (McKenzie extension)|mobility|bodyweight|1|0|
Sciatic Nerve Floss|mobility|bodyweight|1|0|
Hip Flexor Stretch (half-kneeling)|mobility|bodyweight|1|0|
Piriformis Stretch (figure-4)|mobility|bodyweight|1|0|
Thoracic Extension on Foam Roller|mobility|bodyweight|1|0|
Chin Tuck (neck)|mobility|bodyweight|1|0|
Hamstring Stretch (lying, strap)|mobility|bodyweight|1|0|
"""


def _parse_exercises():
    out = []
    for line in _EXERCISES.strip().splitlines():
        name, group, equip, spine, neck, alt = line.split("|")
        out.append({"name": name, "group": group, "equipment": equip,
                    "spine": int(spine), "neck": int(neck), "alt": alt})
    return out


EXERCISES = _parse_exercises()


def is_safe(ex, back, neck):
    """Deterministic safety layer. The AI coach may only choose from what this allows."""
    if ex["neck"] or ex["spine"] >= 3:
        return False
    if back >= 7 or neck >= 7:
        return ex["spine"] == 1 and (ex["group"] == "mobility" or ex["name"].startswith("Walking"))
    if back >= 4:
        return ex["spine"] == 1
    return True


# ---------------------------------------------------------------- small helpers
def load_json(path):
    if DATABASE_URL:
        return kv_get("file:" + os.path.basename(path))
    try:
        with open(path) as f:
            return json.load(f)
    except (OSError, ValueError):
        return None


def save_json(path, data):
    if DATABASE_URL:
        return kv_put("file:" + os.path.basename(path), data)
    with open(path, "w") as f:
        json.dump(data, f, indent=2)
    try:
        os.chmod(path, 0o600)
    except OSError:
        pass


def delete_json(path):
    if DATABASE_URL:
        return kv_del("file:" + os.path.basename(path))
    if os.path.exists(path):
        os.remove(path)


CONFIG = {}


def load_config():
    """Keys, passcode hash and sign-in sessions. Online this is re-read on every request, because
    each request may land on a different copy of the app."""
    global CONFIG
    CONFIG = load_json(CONFIG_FILE) or {}  # swapped in one step, so no request ever sees it half-loaded
# "hosted" = running on a web server on the internet, not on your own computer. Then every visitor
# must enter the passcode, and Google sign-in comes back to the server's own https address.
_state = {"hosted": bool(os.environ.get("HOSTED")) or SERVERLESS, "ready": False, "pg": None}
_lock = threading.Lock()


def http_json(url, data=None, headers=None, method=None, form=False, timeout=30):
    headers = dict(headers or {})
    body = None
    if data is not None:
        if form:
            body = urllib.parse.urlencode(data).encode()
            headers["Content-Type"] = "application/x-www-form-urlencoded"
        else:
            body = json.dumps(data).encode()
            headers["Content-Type"] = "application/json"
    headers.setdefault("Accept", "application/json")
    req = urllib.request.Request(url, data=body, headers=headers, method=method)
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            return json.loads(r.read().decode() or "{}")
    except urllib.error.HTTPError as e:
        detail = e.read().decode(errors="replace")[:600]
        raise RuntimeError(f"HTTP {e.code}: {detail}") from None
    except urllib.error.URLError as e:
        if "Tunnel connection failed" in str(e.reason):
            host = urllib.parse.urlparse(url).netloc
            raise RuntimeError(f"Your web host's free plan is blocking {host}. See README, 'If a connection is blocked'.") from None
        raise RuntimeError(f"Could not connect ({e.reason}). Check your internet.") from None


def today():
    """Today's date where the user is. A web server's clock is usually UTC, so the browser tells us its offset."""
    off = CONFIG.get("tz_min")
    if isinstance(off, int):
        return (datetime.now(timezone.utc) + timedelta(minutes=off)).date()
    return date.today()


def hosted_init():
    """Free PythonAnywhere accounts reach the internet only through their proxy. Use it when it exists."""
    if SERVERLESS or any(os.environ.get(k) for k in ("https_proxy", "HTTPS_PROXY")):
        return
    try:
        socket.gethostbyname("proxy.server")
        os.environ["https_proxy"] = "http://proxy.server:3128"
    except OSError:
        pass


def _secret():
    if not CONFIG.get("secret"):
        CONFIG["secret"] = secrets.token_hex(32)
        save_json(CONFIG_FILE, CONFIG)
    return CONFIG["secret"].encode()


def make_state():
    ts = str(int(time.time()))
    return ts + "." + hmac.new(_secret(), ts.encode(), "sha256").hexdigest()[:32]


def state_ok(value):
    ts, _, sig = str(value or "").partition(".")
    good = hmac.new(_secret(), ts.encode(), "sha256").hexdigest()[:32]
    return ts.isdigit() and time.time() - int(ts) < 900 and hmac.compare_digest(sig, good)


def to_num(v):
    try:
        return float(v)
    except (TypeError, ValueError):
        return None


def parse_day(s):
    if not s or not re.fullmatch(r"\d{4}-\d{2}-\d{2}", s):
        return today()
    return date.fromisoformat(s)


# ---------------------------------------------------------------- Google sign-in
def has_oauth():
    return bool(CONFIG.get("client_id") and CONFIG.get("client_secret"))


def exchange_code(code, redirect_uri):
    tok = http_json(TOKEN_URL, form=True, data={
        "code": code,
        "client_id": CONFIG["client_id"],
        "client_secret": CONFIG["client_secret"],
        "redirect_uri": redirect_uri,
        "grant_type": "authorization_code",
    })
    tok["expires_at"] = time.time() + int(tok.get("expires_in", 3600)) - 60
    save_json(TOKEN_FILE, tok)


def access_token():
    with _lock:
        tok = load_json(TOKEN_FILE)
        if not tok or not has_oauth():
            return None
        if time.time() < tok.get("expires_at", 0):
            return tok["access_token"]
        if not tok.get("refresh_token"):
            return None
        try:
            new = http_json(TOKEN_URL, form=True, data={
                "refresh_token": tok["refresh_token"],
                "client_id": CONFIG["client_id"],
                "client_secret": CONFIG["client_secret"],
                "grant_type": "refresh_token",
            })
        except RuntimeError:
            # Refresh tokens expire after 7 days while the Google app is in "Testing". Sign in again.
            delete_json(TOKEN_FILE)
            return None
        tok["access_token"] = new["access_token"]
        tok["expires_at"] = time.time() + int(new.get("expires_in", 3600)) - 60
        save_json(TOKEN_FILE, tok)
        return tok["access_token"]


def check_connections():
    """Can this machine reach the three Google addresses the app needs? Any answer from Google counts as yes."""
    out = []
    for name, url in (("Google sign-in", TOKEN_URL), ("Fitbit data (Google Health)", API_BASE + "/identity"),
                      ("AI coach (Gemini)", GEMINI_BASE + "/models")):
        host = urllib.parse.urlparse(url).netloc
        try:
            urllib.request.urlopen(urllib.request.Request(url, headers={"Accept": "application/json"}), timeout=15).close()
            out.append({"name": name, "host": host, "ok": True})
        except urllib.error.HTTPError:
            out.append({"name": name, "host": host, "ok": True})  # Google answered (it just wants a key): reachable
        except (urllib.error.URLError, OSError) as e:
            out.append({"name": name, "host": host, "ok": False, "detail": str(getattr(e, "reason", e))[:160]})
    return out


# ---------------------------------------------------------------- Google Health API
def api_get(path, params=None):
    url = f"{API_BASE}/{path}"
    if params:
        url += "?" + urllib.parse.urlencode(params)
    return http_json(url, headers={"Authorization": f"Bearer {access_token()}"})


def api_post(path, body):
    return http_json(f"{API_BASE}/{path}", data=body,
                     headers={"Authorization": f"Bearer {access_token()}"}, method="POST")


def list_all(data_type, params, endpoint="dataPoints", max_pages=5):
    points, token = [], None
    for _ in range(max_pages):
        p = dict(params)
        if token:
            p["pageToken"] = token
        res = api_get(f"dataTypes/{data_type}/{endpoint}", p)
        points += res.get("dataPoints", [])
        token = res.get("nextPageToken")
        if not token:
            break
    return points


def civil_date(obj):
    if isinstance(obj, dict) and "year" in obj:
        return f"{obj['year']:04d}-{obj.get('month', 1):02d}-{obj.get('day', 1):02d}"
    if isinstance(obj, str) and len(obj) >= 10:
        return obj[:10]
    return None


def local_date(ts, offset):
    t = datetime.fromisoformat(ts.replace("Z", "+00:00"))
    secs = int(float(str(offset or "0s").rstrip("s") or 0))
    return (t + timedelta(seconds=secs)).date().isoformat()


def payload_of(dp, skip=("name", "dataPointName", "dataSource")):
    for k, v in dp.items():
        if k not in skip and isinstance(v, dict):
            return v
    return {}


PREFERRED_KEYS = ("beatsPerMinute", "rmssd", "averageRmssd", "rmssdMilliseconds",
                  "percentage", "averagePercentage", "breathsPerMinute", "value", "average")
SKIP_KEYS = ("date", "year", "month", "day", "utcOffset", "createTime", "updateTime")


def first_number(obj, depth=0):
    """Find the main numeric value in a data point, whatever its exact field names are."""
    if depth > 4 or not isinstance(obj, dict):
        return None
    for k in PREFERRED_KEYS:
        if k in obj and to_num(obj[k]) is not None:
            return to_num(obj[k])
    for k, v in obj.items():
        if k not in SKIP_KEYS and not isinstance(v, (dict, list, bool)) and to_num(v) is not None:
            return to_num(v)
    for k, v in obj.items():
        if isinstance(v, dict) and k not in ("date", "metadata"):
            n = first_number(v, depth + 1)
            if n is not None:
                return n
    return None


def rollup_value(payload):
    """One number from a roll-up window: a 'total' field if present, else the sum of its fields."""
    nums = {k: to_num(v) for k, v in payload.items()
            if not isinstance(v, (dict, list, bool)) and to_num(v) is not None}
    if not nums:
        return first_number(payload)
    for k, v in nums.items():
        if "total" in k.lower():
            return v
    return sum(nums.values())


def daily_rollup(data_type, start, end_excl, chunk_days=90):
    def d(x):
        return {"date": {"year": x.year, "month": x.month, "day": x.day}}
    out = {}
    cur = start
    while cur < end_excl:
        nxt = min(cur + timedelta(days=chunk_days), end_excl)
        res = api_post(f"dataTypes/{data_type}/dataPoints:dailyRollUp",
                       {"range": {"start": d(cur), "end": d(nxt)}, "windowSizeDays": 1})
        for p in res.get("rollupDataPoints", []):
            day = civil_date((p.get("civilStartTime") or {}).get("date"))
            payload = payload_of(p, skip=("civilStartTime", "civilEndTime", "startTime", "endTime"))
            if day and payload:
                val = rollup_value(payload)
                if val is not None:
                    out[day] = val
        cur = nxt
    return out


def sleep_daily(start, end_excl):
    flt = (f'sleep.interval.civil_end_time >= "{start.isoformat()}" AND '
           f'sleep.interval.civil_end_time < "{end_excl.isoformat()}"')
    try:
        pts = list_all("sleep", {"filter": flt, "pageSize": 25}, endpoint="dataPoints:reconcile")
    except RuntimeError:
        pts = list_all("sleep", {"filter": flt, "pageSize": 25})
    out = {}
    for dp in pts:
        s = dp.get("sleep", {})
        iv = s.get("interval", {})
        if not iv.get("endTime"):
            continue
        day = local_date(iv["endTime"], iv.get("endUtcOffset"))
        summ = s.get("summary", {})
        stages = {}
        for st in summ.get("stagesSummary", []) or []:
            stages[st.get("type", "?")] = to_num(st.get("minutes")) or 0
        if not stages:
            for st in s.get("stages", []) or []:
                try:
                    a = datetime.fromisoformat(st["startTime"].replace("Z", "+00:00"))
                    b = datetime.fromisoformat(st["endTime"].replace("Z", "+00:00"))
                except (KeyError, ValueError):
                    continue
                key = st.get("type", "?")
                stages[key] = stages.get(key, 0) + (b - a).total_seconds() / 60
        asleep = to_num(summ.get("minutesAsleep"))
        if asleep is None:
            asleep = sum(v for k, v in stages.items() if k != "AWAKE")
        rec = {"minutesAsleep": asleep, "stages": stages}
        if day not in out or (asleep or 0) > (out[day]["minutesAsleep"] or 0):
            out[day] = rec  # keep the longest sleep per wake-up date (main sleep, not naps)
    return out


def daily_metric(data_type, start):
    field = data_type.replace("-", "_")
    pts = list_all(data_type, {"filter": f'{field}.date >= "{start.isoformat()}"'})
    out = {}
    for dp in pts:
        obj = payload_of(dp)
        day = civil_date(obj.get("date"))
        val = first_number(obj)
        if day and val is not None:
            out[day] = val
    return out


_fit_cache = {"key": None, "ts": 0, "data": None}


def fitbit_summary(days, force=False):
    today = parse_day(None)
    key = (days, today.isoformat())
    if not force and _fit_cache["key"] == key and time.time() - _fit_cache["ts"] < 600:
        return _fit_cache["data"]
    start = today - timedelta(days=days - 1)
    end_excl = today + timedelta(days=1)
    result = {"days": [(start + timedelta(i)).isoformat() for i in range(days)], "errors": {}}

    def safe(name, fn):
        try:
            result[name] = fn()
        except Exception as e:  # keep the app working even if one metric fails
            result[name] = {}
            result["errors"][name] = str(e)[:300]

    safe("steps", lambda: daily_rollup("steps", start, end_excl))
    safe("sleep", lambda: sleep_daily(start, end_excl))
    safe("calories", lambda: daily_rollup("total-calories", start, end_excl, chunk_days=14))
    safe("azm", lambda: daily_rollup("active-zone-minutes", start, end_excl, chunk_days=14))
    safe("restingHr", lambda: daily_metric("daily-resting-heart-rate", start))
    safe("hrv", lambda: daily_metric("daily-heart-rate-variability", start))
    safe("spo2", lambda: daily_metric("daily-oxygen-saturation", start))
    _fit_cache.update(key=key, ts=time.time(), data=result)
    return result


def fitbit_for_ai(day, n=7):
    """Compact Fitbit context for the AI coach. Never fails."""
    if access_token() is None:
        return None
    try:
        f = fitbit_summary(30)
    except Exception:
        return None
    end = parse_day(day)
    out = []
    for i in range(n - 1, -1, -1):
        d = (end - timedelta(days=i)).isoformat()
        sl = f["sleep"].get(d)
        out.append({"day": d, "sleep_h": round(sl["minutesAsleep"] / 60, 1) if sl else None,
                    "steps": f["steps"].get(d), "resting_hr": f["restingHr"].get(d),
                    "hrv_ms": f["hrv"].get(d), "kcal_burned": f["calories"].get(d),
                    "zone_min": f["azm"].get(d)})
    return out


# ---------------------------------------------------------------- local database
DEFAULT_SETTINGS = {
    "name": "", "sex": "", "age": None, "height_cm": None, "goal_kg": None,
    "kcal_target": 2000, "protein_target": 120, "water_target_ml": 3000, "cardio_target_min": 150,
    "supplements": ["Vitamin D", "Vitamin C", "Magnesium"],
    "conditions": "Lumbar slipped disc (herniated disc). Neck (cervical) gets strained under load.",
}
LOG_KINDS = {"set", "food", "water", "supp", "pain", "weight", "mood", "slip"}
SINGLE_PER_DAY = {"pain", "weight", "mood", "plan"}


class _Postgres:
    """Online storage. Wraps a Postgres connection so it answers the few sqlite3-style calls this app makes."""

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        return False

    def execute(self, sql, args=()):
        import psycopg2
        import psycopg2.extras
        for attempt in (0, 1):
            try:
                con = _state["pg"]
                if con is None or con.closed:
                    con = psycopg2.connect(DATABASE_URL, connect_timeout=15)
                    con.autocommit = True
                    _state["pg"] = con
                cur = con.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
                cur.execute(sql.replace("?", "%s"), tuple(args))
                return cur
            except (psycopg2.OperationalError, psycopg2.InterfaceError):
                _state["pg"] = None  # the database went to sleep or the link dropped: reconnect once
                if attempt:
                    raise


def db():
    if DATABASE_URL:
        return _Postgres()
    con = sqlite3.connect(DB_FILE, timeout=10)
    con.row_factory = sqlite3.Row
    return con


def init_db():
    serial = "BIGSERIAL PRIMARY KEY" if DATABASE_URL else "INTEGER PRIMARY KEY AUTOINCREMENT"
    real = "DOUBLE PRECISION" if DATABASE_URL else "REAL"
    for attempt in (0, 1):
        try:
            with db() as con:
                con.execute(f"CREATE TABLE IF NOT EXISTS entries (id {serial}, "
                            f"kind TEXT NOT NULL, day TEXT NOT NULL, ts {real} NOT NULL, data TEXT NOT NULL)")
                con.execute("CREATE INDEX IF NOT EXISTS idx_day_kind ON entries(day, kind)")
                con.execute("CREATE TABLE IF NOT EXISTS kv (key TEXT PRIMARY KEY, value TEXT NOT NULL)")
            break
        except Exception:
            if attempt or not DATABASE_URL:  # two copies of the app creating the tables at once: try again
                raise
    if not DATABASE_URL:
        try:
            os.chmod(DB_FILE, 0o600)  # your log is readable only by your own account
        except OSError:
            pass


def kv_get(key):
    with db() as con:
        row = con.execute("SELECT value FROM kv WHERE key=?", (key,)).fetchone()
    return json.loads(row["value"]) if row else None


def kv_put(key, obj):
    with db() as con:
        con.execute("INSERT INTO kv(key, value) VALUES(?, ?) "
                    "ON CONFLICT(key) DO UPDATE SET value=excluded.value", (key, json.dumps(obj)))


def kv_del(key):
    with db() as con:
        con.execute("DELETE FROM kv WHERE key=?", (key,))


def get_settings():
    s = dict(DEFAULT_SETTINGS)
    s.update(kv_get("settings") or {})
    return s


def put_settings(new):
    s = get_settings()
    for k in DEFAULT_SETTINGS:
        if k in new:
            s[k] = new[k]
    kv_put("settings", s)
    return s


def add_entry(kind, day, data):
    with db() as con:
        if kind in SINGLE_PER_DAY:
            con.execute("DELETE FROM entries WHERE kind=? AND day=?", (kind, day))
        cur = con.execute("INSERT INTO entries(kind, day, ts, data) VALUES(?,?,?,?)"
                          + (" RETURNING id" if DATABASE_URL else ""), (kind, day, time.time(), json.dumps(data)))
        return cur.fetchone()["id"] if DATABASE_URL else cur.lastrowid


def rows_for(day_from, day_to, kinds=None):
    q = "SELECT id, kind, day, ts, data FROM entries WHERE day BETWEEN ? AND ?"
    args = [day_from, day_to]
    if kinds:
        q += " AND kind IN (%s)" % ",".join("?" * len(kinds))
        args += list(kinds)
    with db() as con:
        rows = con.execute(q + " ORDER BY ts, id", args).fetchall()
    return [{**json.loads(r["data"]), "id": r["id"], "kind": r["kind"], "day": r["day"], "ts": r["ts"]}
            for r in rows]


def game_stats(today):
    """XP, level, streak and bounce-back rate, computed from the log itself."""
    with db() as con:
        rows = con.execute("SELECT day, kind, COUNT(*) AS n FROM entries WHERE kind IN (%s) GROUP BY day, kind"
                           % ",".join("?" * len(LOG_KINDS)), list(LOG_KINDS)).fetchall()
    per_day = {}
    for r in rows:
        if r["day"] <= today:
            per_day.setdefault(r["day"], {})[r["kind"]] = r["n"]
    xp, comebacks, comeback_today, prev = 0, 0, False, None
    for d in sorted(per_day):
        k = per_day[d]
        xp += 30 if "set" in k else 0
        xp += min(k.get("food", 0), 3) * 10
        xp += 5 if "water" in k else 0
        xp += min(k.get("supp", 0), 5) * 5
        xp += 5 if "pain" in k else 0
        xp += 5 if "weight" in k else 0
        xp += 10 if "mood" in k else 0
        xp += 15 if "slip" in k else 0  # honesty XP: logging a slip is the opposite of avoiding it
        if prev:
            gap = (date.fromisoformat(d) - date.fromisoformat(prev)).days
            if gap > 1 or (gap == 1 and "slip" in per_day[prev]):
                xp += 50  # comeback bonus: showing up after a gap or a slip
                comebacks += 1
                comeback_today = comeback_today or d == today
        prev = d
    t = date.fromisoformat(today)
    streak, cur = 0, t if today in per_day else t - timedelta(days=1)
    while cur.isoformat() in per_day:
        streak += 1
        cur -= timedelta(days=1)
    slip_days = [d for d in per_day if "slip" in per_day[d] and d < today]
    bounced = sum(1 for d in slip_days
                  if (date.fromisoformat(d) + timedelta(days=1)).isoformat() in per_day)
    past = [d for d in per_day if d < today]
    last_logged = max(past) if past else None
    return {
        "xp": xp, "level": 1 + xp // 200, "xp_in_level": xp % 200, "xp_per_level": 200,
        "streak": streak, "comebacks": comebacks, "comeback_today": comeback_today,
        "logged_today": today in per_day,
        "gap_days": (t - date.fromisoformat(last_logged)).days - 1 if last_logged else None,
        "slips": len(slip_days), "bounced": bounced,
        "bounce_rate": round(100 * bounced / len(slip_days)) if slip_days else None,
    }


def next_split(day):
    with db() as con:
        row = con.execute("SELECT data FROM entries WHERE kind='set' AND day < ? ORDER BY day DESC, ts DESC LIMIT 1",
                          (day,)).fetchone()
    last = json.loads(row["data"]).get("split") if row else None
    if last in ROTATION:
        return ROTATION[(ROTATION.index(last) + 1) % len(ROTATION)]
    return ROTATION[0]


def latest_of(kind, day):
    with db() as con:
        row = con.execute("SELECT day, data FROM entries WHERE kind=? AND day <= ? ORDER BY day DESC, ts DESC LIMIT 1",
                          (kind, day)).fetchone()
    return {**json.loads(row["data"]), "day": row["day"]} if row else None


def day_state(day):
    rows = rows_for(day, day, LOG_KINDS | {"plan"})
    by = {}
    for r in rows:
        by.setdefault(r["kind"], []).append(r)
    foods = by.get("food", [])
    return {
        "day": day,
        "sets": by.get("set", []),
        "foods": foods,
        "water_ml": sum(to_num(w.get("ml")) or 0 for w in by.get("water", [])),
        "supps": [{"id": s["id"], "name": s.get("name")} for s in by.get("supp", [])],
        "pain": (by.get("pain") or [None])[-1],
        "last_pain": latest_of("pain", day),
        "weight": (by.get("weight") or [None])[-1],
        "last_weight": latest_of("weight", day),
        "mood": (by.get("mood") or [None])[-1],
        "slips": by.get("slip", []),
        "plan": (by.get("plan") or [None])[-1],
        "totals": {"kcal": round(sum(to_num(f.get("kcal")) or 0 for f in foods)),
                   "protein": round(sum(to_num(f.get("protein")) or 0 for f in foods))},
        "next_split": next_split(day),
        "settings": get_settings(),
        "game": game_stats(day),
    }


def history(end_day, days):
    end = parse_day(end_day)
    start = end - timedelta(days=days - 1)
    out = {}
    for i in range(days):
        d = (start + timedelta(i)).isoformat()
        out[d] = {"day": d, "kcal": 0, "protein": 0, "foods": 0, "water_ml": 0, "supps": 0, "sets": 0,
                  "volume": 0, "cardio_min": 0, "splits": [], "pain": None, "neck": None,
                  "weight": None, "mood": None, "slips": 0, "logged": False}
    for r in rows_for(start.isoformat(), end.isoformat(), LOG_KINDS):
        d = out[r["day"]]
        d["logged"] = True
        k = r["kind"]
        if k == "set":
            d["sets"] += 1
            if r.get("minutes") is not None:
                d["cardio_min"] += to_num(r.get("minutes")) or 0
            else:
                d["volume"] += (to_num(r.get("weight")) or 0) * (to_num(r.get("reps")) or 0) * (to_num(r.get("sets")) or 1)
            if r.get("split") and r["split"] not in d["splits"]:
                d["splits"].append(r["split"])
        elif k == "food":
            d["kcal"] += to_num(r.get("kcal")) or 0
            d["protein"] += to_num(r.get("protein")) or 0
            d["foods"] += 1
        elif k == "water":
            d["water_ml"] += to_num(r.get("ml")) or 0
        elif k == "supp":
            d["supps"] += 1
        elif k == "pain":
            d["pain"], d["neck"] = to_num(r.get("back")), to_num(r.get("neck"))
        elif k == "weight":
            d["weight"] = to_num(r.get("kg"))
        elif k == "mood":
            d["mood"] = to_num(r.get("mood"))
        elif k == "slip":
            d["slips"] += 1
    return list(out.values())


def last_lift(exercise, day):
    with db() as con:
        rows = con.execute("SELECT day, data FROM entries WHERE kind='set' AND day < ? ORDER BY day DESC, ts ASC LIMIT 400",
                           (day,)).fetchall()
    found_day, sets = None, []
    for r in rows:
        data = json.loads(r["data"])
        if (data.get("exercise") or "").lower() != exercise.lower():
            continue
        if found_day is None:
            found_day = r["day"]
        if r["day"] == found_day:
            sets.append(data)
    return {"day": found_day, "sets": sets}


# ---------------------------------------------------------------- Gemini (AI coach)
_model = {"name": None, "json_mode": True}


def gemini_model():
    if CONFIG.get("gemini_model"):
        return CONFIG["gemini_model"]
    if _model["name"]:
        return _model["name"]
    name = GEMINI_FALLBACK_MODEL
    try:  # pick the newest general-purpose Flash model this key can use
        res = http_json(f"{GEMINI_BASE}/models?pageSize=1000", headers={"x-goog-api-key": CONFIG["gemini_key"]})
        found = []
        for m in res.get("models", []):
            mid = m.get("name", "").split("/")[-1]
            methods = m.get("supportedGenerationMethods")
            if methods is not None and "generateContent" not in methods:
                continue
            ver = re.fullmatch(r"gemini-(\d+(?:\.\d+)?)-flash", mid)
            if ver:
                found.append((float(ver.group(1)), mid))
        if found:
            name = max(found)[1]
    except Exception:
        pass
    _model["name"] = name
    return name


def _read_json(text):
    text = re.sub(r"^```(?:json)?\s*|\s*```$", "", text.strip())
    try:
        return json.loads(text)
    except ValueError:
        a, b = text.find("{"), text.rfind("}")
        if a != -1 and b > a:
            return json.loads(text[a:b + 1])
        raise


def gemini(system, contents, want_json=False, temperature=None):
    """One call to the Gemini API (generateContent). `contents` is a list of turns:
    {"role": "user" | "model", "parts": [{"text": ...} | {"inline_data": {"mime_type", "data"}}]}.
    `temperature` is accepted for readability but not sent: current Flash models ignore it."""
    if not CONFIG.get("gemini_key"):
        raise RuntimeError("Add your Gemini API key in Settings to use the AI features.")
    url = f"{GEMINI_BASE}/models/{gemini_model()}:generateContent"
    headers = {"x-goog-api-key": CONFIG["gemini_key"]}
    body = {"systemInstruction": {"parts": [{"text": system}]}, "contents": contents}

    def call(with_json_mode):
        b = dict(body)
        if with_json_mode:
            b["generationConfig"] = {"responseMimeType": "application/json"}
        return http_json(url, data=b, headers=headers, timeout=120)

    try:
        try:
            res = call(want_json and _model["json_mode"])
        except RuntimeError as e:
            if want_json and _model["json_mode"] and "HTTP 400" in str(e) and "API key" not in str(e):
                _model["json_mode"] = False  # this model rejects JSON mode: the prompt already asks for JSON
                res = call(False)
            else:
                raise
    except RuntimeError as e:
        msg = str(e)
        if "HTTP 429" in msg:
            raise RuntimeError("Gemini's free limit was hit. Wait a minute and try again.") from None
        if "HTTP 403" in msg or "HTTP 401" in msg or ("HTTP 400" in msg and "API key" in msg):
            raise RuntimeError("Gemini rejected the API key. Check it in Settings.") from None
        if "HTTP 404" in msg:
            _model["name"] = None
            raise RuntimeError("Gemini model not found. Try again, or set a model name in config.json (gemini_model).") from None
        raise
    cands = res.get("candidates") or []
    parts = (cands[0].get("content") or {}).get("parts") if cands else None
    text = "".join(p.get("text", "") for p in parts or [] if not p.get("thought")).strip()
    if not text:
        raise RuntimeError("Gemini returned no answer (it may have blocked the request). Try rephrasing.")
    if not want_json:
        return text
    try:
        return _read_json(text)
    except ValueError:
        raise RuntimeError("Gemini's answer could not be read. Try again.") from None


def user_text(text):
    return [{"role": "user", "parts": [{"text": text}]}]


def profile_line(s):
    bits = [f"{k}: {s[k]}" for k in ("sex", "age", "height_cm", "goal_kg") if s.get(k)]
    return "; ".join(bits) or "not provided"


FOOD_SYSTEM = """You are a careful nutrition logger for an Indian user. You receive a voice note or text
describing what they ate (English, Hindi or Hinglish). Estimate calories and macros per item.
When a quantity is not given, assume a typical Indian home or restaurant portion and say so in "assumption".
Be realistic, not flattering: include oil, ghee, sugar and sides people forget.
Return JSON only:
{"transcript": "what you heard, in English", "items": [{"name": "", "qty": "", "kcal": 0, "protein_g": 0,
"carbs_g": 0, "fat_g": 0, "assumption": ""}], "total_kcal": 0, "total_protein_g": 0,
"confidence": "low|medium|high"}
If nothing edible is described, return {"items": [], "total_kcal": 0, "total_protein_g": 0, "transcript": "..."}."""


def ai_food(day, text=None, audio_b64=None, mime=None):
    parts = []
    if audio_b64:
        parts.append({"inline_data": {"mime_type": mime or "audio/wav", "data": audio_b64}})
        parts.append({"text": "Voice note of what I ate. Log it."})
    else:
        parts.append({"text": f"What I ate: {text}"})
    res = gemini(FOOD_SYSTEM, [{"role": "user", "parts": parts}], want_json=True, temperature=0.2)
    items = res.get("items") or []
    if not items:
        raise RuntimeError("Couldn't find any food in that. Heard: " + str(res.get("transcript") or text or ""))
    kcal = to_num(res.get("total_kcal")) or sum(to_num(i.get("kcal")) or 0 for i in items)
    protein = to_num(res.get("total_protein_g")) or sum(to_num(i.get("protein_g")) or 0 for i in items)
    data = {
        "name": ", ".join(str(i.get("name", "")) for i in items)[:140],
        "kcal": round(kcal), "protein": round(protein),
        "carbs": round(sum(to_num(i.get("carbs_g")) or 0 for i in items)),
        "fat": round(sum(to_num(i.get("fat_g")) or 0 for i in items)),
        "items": items, "confidence": res.get("confidence"),
        "transcript": res.get("transcript"), "source": "voice" if audio_b64 else "text",
    }
    data["id"] = add_entry("food", day, data)
    return data


WORKOUT_SYSTEM = """You are a cautious strength coach inside a personal app. The user has: {conditions}
You are not a doctor or physiotherapist. Rules you must follow:
- Choose exercises ONLY from the "allowed" list, using the exact names. Never add others.
- Train each muscle group in today's split. Aim for 5 to 7 exercises on a normal day, fewer if pain is up.
- Prefer supported, machine and cable movements. Keep a neutral spine. No breath-holding under heavy load.
- Use the last logged weights to suggest today's load. Progress slowly: add reps before weight. If back pain is 4 or more, reduce load about 20 percent and stop 3 reps short of failure.
- Poor sleep (under 6 h) or a clear HRV drop means reduce volume.
- If back or neck pain is 7 or more, the verdict is REST: gentle walking and mobility only.
- Mention once that sharp, shooting or worsening pain, numbness, tingling or weakness in a leg or arm means stop and see a doctor.
Return JSON only:
{{"verdict": "GO|MODIFY|REST", "why": "one or two sentences using their numbers",
"warmup": ["..."], "exercises": [{{"name": "", "sets": 3, "reps": "10-12", "weight_hint": "", "cue": "one form cue that protects the back or neck"}}],
"avoid_today": ["exercise or movement pattern, with a short reason"], "cardio": "one sentence", "red_flags": "one sentence"}}"""


def ai_workout(day, split):
    s = get_settings()
    pain = latest_of("pain", day) or {}
    back, neck = to_num(pain.get("back")) or 0, to_num(pain.get("neck")) or 0
    if split not in SPLITS:
        split = ROTATION[0]
    groups = SPLITS[split]
    if back >= 7 or neck >= 7:
        allowed = [e for e in EXERCISES if is_safe(e, back, neck)]
    else:
        allowed = [e for e in EXERCISES if (e["group"] in groups or e["group"] == "mobility") and is_safe(e, back, neck)]
    recent = {}
    start = (parse_day(day) - timedelta(days=28)).isoformat()
    for r in rows_for(start, day, {"set"}):
        if r.get("minutes") is None and r.get("exercise"):
            recent[r["exercise"]] = f"{r.get('sets')}x{r.get('reps')} @ {r.get('weight')} kg on {r['day']}"
    prompt = {
        "today": day, "split": split, "muscle_groups": groups,
        "back_pain_0_to_10": back, "neck_pain_0_to_10": neck, "pain_note": pain.get("note") or "",
        "pain_checked_on": pain.get("day") or "never checked in",
        "allowed": [{"name": e["name"], "group": e["group"], "equipment": e["equipment"]} for e in allowed],
        "last_logged_lifts": recent,
        "fitbit_last_7_days": fitbit_for_ai(day),
        "profile": profile_line(s),
    }
    res = gemini(WORKOUT_SYSTEM.format(conditions=s.get("conditions") or "no conditions given"),
                 user_text(json.dumps(prompt)), want_json=True, temperature=0.3)
    names = {e["name"].lower() for e in allowed}
    res["exercises"] = [x for x in (res.get("exercises") or []) if str(x.get("name", "")).lower() in names]
    res.update(split=split, back=back, neck=neck)
    add_entry("plan", day, res)
    return res


BLOOD_SYSTEM = """You read blood test reports for a layperson. You are not a doctor and you do not diagnose.
Extract every test in the report. For each, compare the value with the reference range PRINTED on the report.
If no range is printed, use a standard adult reference range and set "ref_source" to "standard".
Return JSON only:
{"report_date": "", "lab": "", "tests": [{"name": "", "value": "", "unit": "", "ref_range": "", "ref_source": "report|standard",
"status": "low|high|borderline|normal", "meaning": "plain-English line on what this marker relates to, only for non-normal results"}],
"summary": "3 to 4 plain sentences on what stands out",
"see_doctor": "none|routine|soon|urgent", "doctor_reason": "why, in one sentence",
"questions_for_doctor": ["..."]}
Use "urgent" only for values that are commonly treated as critical. Use "soon" when several related markers are off
or one is far outside range. Never suggest medication or doses. Supplements: say only "discuss with your doctor".
If the file is not a blood report, return {"tests": [], "summary": "This doesn't look like a blood report."}."""


def ai_blood(day, name, file_b64, mime):
    s = get_settings()
    parts = [{"inline_data": {"mime_type": mime, "data": file_b64}},
             {"text": f"Analyse this blood report. Patient profile: {profile_line(s)}. Known conditions: {s.get('conditions')}"}]
    res = gemini(BLOOD_SYSTEM, [{"role": "user", "parts": parts}], want_json=True, temperature=0.1)
    if not res.get("tests"):
        raise RuntimeError(res.get("summary") or "No tests found in that file.")
    data = {"name": name, "result": res}
    data["id"] = add_entry("blood", day, data)
    data["day"] = day
    return data


MIND_SYSTEM = """You are a warm, direct coach inside the user's personal fitness app. The user has told you two things
about themselves: they use food as a coping mechanism, and after a slip they get anxious and then avoid acting
altogether (anxious avoidance). Your one job is to break the slip -> shame -> avoidance loop and get them back to
one small action.
Style: at most 110 words. Plain, kind, a little firm. No lectures, no toxic positivity, no lists longer than 3.
Reply in the language the user writes in (English or Hinglish).
Each reply does three things:
1. Normalise in one line, using their actual numbers from the context (one day rarely moves a week).
2. Ask at most ONE curious question about what set it off (tired, stressed, bored, lonely, skipped a meal?).
3. Offer ONE tiny next action that takes under 10 minutes (log the next meal, a glass of water, a 5-minute walk, a pain check-in).
Never suggest compensating: no fasting, no skipping meals, no punishment cardio, no "earning it back".
Coming back after a slip is the win. Say so when they do it.
You are not a therapist and you do not diagnose. If the loop sounds frequent or distressing, mention once, gently,
that a psychologist works on exactly this pattern.
If the user mentions self-harm, suicide, purging, or not eating for days: stop coaching, respond with care, and ask
them to reach a professional now (in India: Tele-MANAS 14416, free, 24x7) or emergency services."""


def coach_context(day):
    s = get_settings()
    hist = history(day, 7)
    compact = [{"day": h["day"], "logged": h["logged"], "kcal": round(h["kcal"]) if h["foods"] else None,
                "workout": ", ".join(h["splits"]) or ("yes" if h["sets"] else None),
                "back_pain": h["pain"], "mood_1_to_5": h["mood"], "slips": h["slips"]} for h in hist]
    g = game_stats(day)
    return {"today": day, "kcal_target": s.get("kcal_target"), "last_7_days": compact,
            "streak_days": g["streak"], "comebacks_so_far": g["comebacks"],
            "bounce_back_rate_percent": g["bounce_rate"], "days_missed_before_today": g["gap_days"]}


def ai_mind(day, message):
    past = rows_for((parse_day(day) - timedelta(days=3)).isoformat(), day, {"chat"})[-12:]
    contents = [{"role": "user" if m.get("role") == "user" else "model", "parts": [{"text": m.get("text", "")}]}
                for m in past]
    while contents and contents[0]["role"] != "user":
        contents.pop(0)
    contents.append({"role": "user", "parts": [{"text":
                     f"{message}\n\n[App context, not written by the user: {json.dumps(coach_context(day))}]"}]})
    reply = gemini(MIND_SYSTEM, contents, temperature=0.7)
    add_entry("chat", day, {"role": "user", "text": message})
    add_entry("chat", day, {"role": "coach", "text": reply})
    return {"reply": reply}


WEEKLY_SYSTEM = """You write a short weekly review for one person using their own tracked data. The user has: {conditions}
Be specific with numbers. Be honest but never shaming: missed days are data, not failure.
Write plain text in this shape, under 200 words:
WINS: 3 short lines.
WATCH: 1 or 2 short lines (pain trend, sleep, protein, days not logged).
NEXT WEEK: exactly one focus, small and concrete.
Never recommend crash dieting, fasting or training through pain. You are not a doctor."""


def ai_weekly(day):
    s = get_settings()
    prompt = {"week_ending": day,
              "targets": {k: s.get(k) for k in ("kcal_target", "protein_target", "water_target_ml", "cardio_target_min", "goal_kg")},
              "daily_log": history(day, 7), "fitbit": fitbit_for_ai(day), "game": game_stats(day)}
    return {"text": gemini(WEEKLY_SYSTEM.format(conditions=s.get("conditions") or "none given"),
                           user_text(json.dumps(prompt)), temperature=0.5)}


# ---------------------------------------------------------------- phone access
# Off by default. When a passcode is set (Settings, on the Mac), the app also listens on the
# local network so a phone on the same Wi-Fi can open it. Every phone request needs a session
# cookie that is only issued after the passcode is entered.
ICON_PNG = base64.b64decode("iVBORw0KGgoAAAANSUhEUgAAALQAAAC0CAIAAACyr5FlAAAN9klEQVR4AeydCXBVVxnHX5KX5WVfgBAgoaxJSaFlL5StNAFsSwvWwqiojDpKtU5LHbXLDNTBoWqnHTuKduzYMhZGp1ZLobIkQSihiiBbAwEClLVsCZDlZX1Jnl946cvNe/fc952b+949596POXk579xzz/L/fjn7vUSPeb6SHCmgqkC0g/6RAgwFCA6GMBTscBAcRAFTAYKDKQ1dIDiIAaYCBAdTGrpAcOhgwC63EBx2sbSOehIcOkSzyy0Eh10sraOeBIcO0exyC8FhF0vrqCfBoUM0u9xCcNjF0jrqaSgcOvKnWwRWgOAQ2DhmF43gMNsCAudPcAhsHLOLRnCYbQGB8yc4BDaO2UUjOMy2gMD5ExxmG0fg/AkOgY1jdtEIDrMtIHD+BIfAxjG7aASH2RYQOH+CQ2DjmF00gsNsCwicP8EhsHHMLpq4cJitDOVPz8oSA2wFqOVga2P7KwSH7RFgC0BwsLWx/RWCw/YIsAUgONja2P4KwWEpBIytDMFhrJ6WSo3gsJQ5ja0MwWGsnpZKjeCwlDmNrQzBYayelkqN4LCUOY2tDMFhrJ6WSs0mcFjKZhGrDMERManly4jgkM9mESsxwRExqeXLiOCQz2YRKzHBETGp5cvIanAkxEaNH+r6+vTML09KHzEgXj6DiFRiS8HxzRmZ+1bnb1hx14sLs9c8kbN55fDNzw6/L88lkuASlcVCp8/XfSv3Z49kx8ZEKeUfkR2/8am7IFwZSH6kAhZpOaATmVOQzKoztCjTRiaxrlI4SwErwAHjjOcWDGDV0Be+alGOz0OfeAWsAMeCcakZSTHadc7LioVo2nHoaoACVoDj8QnpAbVS/TrvnhTVcApkKSA9HANSnZOHoeYjswuSnSHaF5ZKNg2XHo5FE9OjonrNUFiWTIiNnpVPjQdLHpVw6eFYPDFNpVqMIGN6Fkbi1guWG45xua68rDi8VeaOoZ4Fr5bki2CPT+BoNkCVpPiYaSNowQOUQDmJWw5ntOPhe1NRtVREKr6H+xbF3fbySgzHg2NSUl3c04+iwpRo1PjVXhyo1lZiOB7DLW8EVDstMWby8MSAQPqqqoCscKQkRM/O1zl6oJ5FFYXgQFnhgGYjRm/3UFxIqx3BJKiEGAmHSvJhC+KdpygL0i/FOX4oalFVeZcN/VLCMax/XOHghL5Yi3oWjHpSwrF4ImqnTaP+j/DPgTVSs+olSeHgW/sKNh70LH1se4LTtF6IfHBMG5mUmezsuyWoZwmpoXxwLOLZadOoP/UsGuL4LkkGhysuyqiJ6KCM2FHZ9OyCDwP1T8ngmD82NT7WsDLPG2vkPsuEoa5l0zPBzcpPTozDFlLdLGKESlaHheP7Ok9Ryg77LMqvuv0LxqV+/OKod1fc9cLCbHB/WJ5b8tORS6dm6E5QkBtlgiMnzXn/CCO3RUYPjOc6DqJqs5cX57z21cEw/VFezUiKWbVo4E8eDnEmXnmLgH6Z4HgU3WysL7+J1LqPZ8MWT0x7cgqzMVs+M2v5zExkSQSMJhMcX5nMNINS2dZ277qy6iu1HmUgy9+XYUecM2plqOdlVs4fUJAj67BXGjjG5bqGZMaybKwML6mob2rzbjtarwxk+WEpLCdd56oJDFmyQq24OGOi3lg2xBUr5RESaeDA77RtOlQHKJQeQ8EBMWEGBJ86XFEharIzJDPuhYUDdaRv+i1ywIE/EXi9zrPvTCPIWnG5paahHTwhnb6lUmeMY3YB9kDJE5PTYX4bsiSiRRAWjl5C4U8EbjnS02BsxfUs9+YmZCVzHzecNTo5gWfF5ZdLB+nIpZcKEf8iBxyPoU8EbjpY69cQ2bNERUXp6FmKOA8qp7liXv/aEH/ZpPBIAEeqK3ru3czXKyhVhq7kXHWbP+TQheZqXM+CHD34UwbPg3enwCeXmzQs8duzsrhuMTeyBHDgV0W3HOppNnyy7jze4PNof04Z7gIEteMor8LOMFd8/73PzOsv0cxWAjiQ8xRPh3fz4a55it8S4MH3LPN4uolivQ/sO6Wa2YoOB/5EYPkpd0NLJwChdPs/a6pr6lCGsPxcc5b5euGA3CWa2fYJDlhBWjI144dF/cPnnn8Uu0LwwcHAZgMs0el1lOF6lhmjk5LjUWrcl+dKT9K5bgZFAgczW9ifC59ovpTBNGAgyE63Q8kRnPrUEYl7Xhr13tPDVi8a+IOH+oXPgc2Ccw8OqW/u2HNSfXhRioMD0pw7BjXG5GpjIFlVBzv7YRCtlyHANGAg2C6ervd9aHrgADDf/u7QkCvHqqKEKfCjI/XtgV1Kd1bQ3bhbGde6o3T/Qo4kkNG6EzX7F2wXv/WdvKfm9tNREG44HhiVBMjryCmst3wYNE9RZrerUr1RUcYBP7QciXEhNkHyB8YPzkBt8UCC4rini/vDDIu3PHxwpCREr31yEG8e4Y5/vqbt2OUWjVxKjqHggBRmhnr1T7Ghh8cgx4i5V5YMSsINqvxF4oNjdkEKNFP+mwXxbFIbiirL9kmVu8WD6lnmjw0x7CguDBFBma9Q/v4pzpn5yVxF4oNDzN2BLYcD174CJGht93580h0QqPoV5ItzMnuWvKy4kdmyHs6A+vYLdcAA4igdHxxNbai/P2UG4fbvO9t0rS707uuOClTPkhgXPWMUc68VPxSFlftwV1xH+q2sQTsjLT44Tl5tZaRjWvBmzaGov1i7TzR42r3+rxqeeexRBbJPuVLr+d6fLly+hTqKplESwy9Vfq41MgvOjg+OikvNJ67wZRCcpYEhN90dOyp69uiZKTscre3e8tNd5zw04vguzWHsqGWnOsfmop7N3/5pfbPH++zGy74EBfmEMfvxsMIB9fz5pmvwKYj7bemNFg+qPYACl+IwghmZ6spbEXoo6luThb+iV7fegHwFcS9/cJW3JHwtB6QOjcfvd9aAx3RXeqzhb/tDDEWVhdx1AjXsgFuK1M7/PaQWCJEDXI274+jFZl/g+vKbr20Tgo83SqoBVl+p8J/ccEDS68qqV7xzsRa3oQXxw+HeP1DL227DttwnuJ4leOCZnhgDOwaYipT2Prv69p6bP/7L55gbwxTnVmPH99+5+Mddev6e9cAB1SivanxgTdXSdefWfHgNGpKIuV/98/ozGy7P/EXV6n9wN5JQ7BJczwIoTOn9UjlYPIXbMS4ADrgFhiCTVp1c9ub5tVuuR0woyAgGAEt+dw602lvVCMXQ4XTC4csJxjh/3XcbGpKIuT/vvQU9Ovw1+ArA+1lyrN7rRY1RAuYsyGef3C0dBz5rCi5Vs8d7+ELzxn/fiphQkNF7/73NOwINKHmf4AhIS/yv9c2d/zvfPSDQLm2xYvgJq8734957XFbp7kSxp525KFftBQeojpyz9FO8VG52QXIse9kU0vS7st4DDn+4lB6H5O8+1yH6dtywA1L2n9sows1TWjyd5VWoRXpIXApnu5YD1s38U01tC/le/eOMwT68BNs37agTidrZCnTVdnCA9iW4HXzoWQoHJ+AfXirFJQsFkMXZEQ7kijuYEBY8inCn0j3t3j2nLNWnQPXtCMfVWg9yC+pL49KQDy/tPd3YiDuMCKLL4uwIB9gGeep4SGYs8uGlf1U2QLIWczaFA9+zYOwNC2s7CQ6MUlLEuVDTdvaGzrMpwRU8cK4Z+ehU8L0ih9i05QCTIOcsEDOks9jal7++9oUDuVTqV0rDs8Nyk1hfZe0Lx6lrrVduG3CSr+JScw3uRQ8+xSX6tC8cYKRtn6KOGEJMDYec+GikIOwlW8NRasQ+2dajKg9wC2tvroLZGo4K9EvlWJqevt56tTb0gxGs2wUPtzUcYJs+9iylFh2KgjLgDIQDUpPP9XFCu/O4AaMWYVWzOxyHzmNf/RNsQpjsCPiUV3A5dYfYHQ4QDn/8ByIrXYkR41llgqL5CQ5Hid5xg7UHHEAqweHYf7ZRx85Idb3nyBcPL4GOlnQEh6PT69Cx4b6z0mpHe4L5Jji6NNGxOWLhhdEuRe78EBxdMvznjLuxleNwsLulAzqjrjv7+iP0/QRHl3naOxy7TnB0ExZ7eKlLArUfgqNbFa45i1UPcHRr8cUvgqNbifJT7qY21KOMTW2dXM1MdwYS/iI4uo3W1u4FPrq/aP5CRtNMQ46LBEePnUpxK55l6Pdl9yQtp4/g6LEbwHG9LsTZsEu32kr1rqj25CSJj+DoMVR7p+P17dU939V8q/5+1dOBGpqo3S1ZmKhwmCTjR0fqfrOjmvV+l90n3fvV3s1iUmHDni3BESjxW7trfvTupYD/HA42X17deuM5wd4eGVh0o78THCqKwkx1ztrT33jz/Ct33uL10vtXin99Zn35zVbca25VUpQziOBg2u3QheYNd97itelgnfUekmZWW3GB4FCIQd7eChAcvfWgbwoFCA6FGOTtrQDB0VsPqb8ZXXiCw2hFLZQewWEhYxpdFYLDaEUtlB7BYSFjGl0VgsNoRS2UHsFhIWMaXRWCw2hFLZSeLeCwkL0iWhWCI6Jyy5UZwSGXvSJaWoIjonLLlRnBIZe9IlpagiOicsuVGcEhl70iWlqCI6JyS5QZFJXgABHIqStAcKjrQqGgAMEBIpBTV4DgUNeFQkEBggNEIKeuAMGhrguFggIEB4hATl0BgkNdF3aoja4QHDYyNm9VCQ5exWwUn+CwkbF5q0pw8Cpmo/gEh42MzVtVgoNXMRvFJzhsZGzeqhoHB2/OFF94BQgO4U1kXgEJDvO0Fz5ngkN4E5lXQILDPO2Fz5ngEN5E5hXw/wAAAP//dYU6ewAAAAZJREFUAwBtXb0UUPv92wAAAABJRU5ErkJggg==")
MANIFEST = json.dumps({"name": "Fit Insights", "short_name": "Fit Insights", "display": "standalone",
                       "start_url": "/", "background_color": "#f4f4f2", "theme_color": "#2a78d6",
                       "icons": [{"src": "/icon.png", "sizes": "180x180", "type": "image/png"}]})
_lockout_mem = {"fails": {}, "log": []}


def lockout_load():
    """Wrong-passcode counts. Online they live in the database, so every copy of the app shares them."""
    st = (kv_get("lockout") if DATABASE_URL else _lockout_mem) or {"fails": {}, "log": []}
    now = time.time()
    st["log"] = [t for t in st.get("log", []) if now - t < 900]
    st["fails"] = {ip: v for ip, v in list(st.get("fails", {}).items())[-200:] if v[1] == 0 or v[1] > now}
    return st


def lockout_save(st):
    if DATABASE_URL:
        kv_put("lockout", st)
    else:
        _lockout_mem.update(st)


def phone_enabled():
    return bool(CONFIG.get("phone_hash"))


def _hash_pass(passcode, salt):
    return hashlib.pbkdf2_hmac("sha256", passcode.encode(), bytes.fromhex(salt), 200_000).hex()


def set_passcode(passcode):
    CONFIG["phone_salt"] = secrets.token_hex(16)
    CONFIG["phone_hash"] = _hash_pass(passcode, CONFIG["phone_salt"])
    CONFIG["phone_sessions"] = []  # changing the passcode signs every phone out
    save_json(CONFIG_FILE, CONFIG)


def clear_passcode():
    for k in ("phone_salt", "phone_hash", "phone_sessions"):
        CONFIG.pop(k, None)
    save_json(CONFIG_FILE, CONFIG)


def check_passcode(passcode):
    return phone_enabled() and hmac.compare_digest(_hash_pass(passcode, CONFIG["phone_salt"]), CONFIG["phone_hash"])


def new_session():
    token = secrets.token_urlsafe(32)
    sessions = CONFIG.setdefault("phone_sessions", [])
    sessions.append(hashlib.sha256(token.encode()).hexdigest())
    del sessions[:-10]  # keep the 10 most recent devices
    save_json(CONFIG_FILE, CONFIG)
    return token


def session_ok(token):
    return bool(token) and hashlib.sha256(token.encode()).hexdigest() in CONFIG.get("phone_sessions", [])


def lan_urls():
    urls = []
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("10.255.255.255", 1))  # no packet is sent: this only asks which network card would be used
        urls.append(f"http://{s.getsockname()[0]}:{PORT}")
        s.close()
    except OSError:
        pass
    host = socket.gethostname()
    if host and "." not in host:
        host += ".local"
    if host and not host.startswith("localhost"):
        urls.append(f"http://{host}:{PORT}")
    return urls


PHONE_LOGIN_HTML = """<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1"><meta name="robots" content="noindex"><title>Fit Insights</title>
<link rel="apple-touch-icon" href="/icon.png">
<style>body{font:16px -apple-system,system-ui,sans-serif;background:#f4f4f2;color:#0b0b0b;display:grid;place-items:center;min-height:90vh;margin:0}
@media (prefers-color-scheme:dark){body{background:#111110;color:#f0efec}input{background:#1a1a19;color:#f0efec;border-color:#33332f}}
form{width:min(320px,86vw);text-align:center}input{font:inherit;width:100%;padding:12px;border-radius:10px;border:1px solid #cfcfca;margin:6px 0;box-sizing:border-box}
button{font:inherit;width:100%;padding:12px;border:0;border-radius:10px;background:#2a78d6;color:#fff;margin-top:6px}p{color:#b3261e;min-height:1.4em}
small{display:block;opacity:.7;margin:6px 0 10px;line-height:1.4}</style></head>
<body><form id="f"><img src="/icon.png" width="72" height="72" style="border-radius:16px" alt=""><h2 id="h">Fit Insights</h2>
<small id="s"></small><input id="p" type="password" placeholder="Passcode" autocomplete="current-password" autofocus>
<input id="p2" type="password" placeholder="Type it again" autocomplete="new-password" style="display:none"><button id="b">Unlock</button><p id="m"></p></form>
<script>const SETUP=@@SETUP@@,$=i=>document.getElementById(i);
if(SETUP){$("h").textContent="Create your passcode";$("s").textContent="This passcode is the only lock on your health data. Use 8 or more characters and don't reuse an easy one.";
$("p").autocomplete="new-password";$("p2").style.display="";$("b").textContent="Save and open";}
$("f").onsubmit=async e=>{e.preventDefault();const v=$("p").value;
if(SETUP&&v.length<8)return $("m").textContent="Use at least 8 characters.";
if(SETUP&&v!==$("p2").value)return $("m").textContent="The two don't match.";
const r=await fetch("/phone-login",{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify({passcode:v})});
if(r.ok)location.href="/";else $("m").textContent=(await r.json().catch(()=>({error:"Something went wrong."}))).error;};</script></body></html>"""


# ---------------------------------------------------------------- web server
class Web(BaseHTTPRequestHandler):
    def log_message(self, fmt, *args):
        pass

    def out_headers(self, ctype, length, headers):
        h = [("Content-Type", ctype), ("Content-Length", str(length)), ("Cache-Control", "no-store"),
             ("X-Content-Type-Options", "nosniff"), ("X-Frame-Options", "DENY"), ("Referrer-Policy", "no-referrer")]
        if _state["hosted"]:
            h.append(("X-Robots-Tag", "noindex, nofollow"))
            if self.base_url().startswith("https://"):
                h.append(("Strict-Transport-Security", "max-age=31536000"))
        return h + list((headers or {}).items())

    def send(self, code, body, ctype="text/html; charset=utf-8", headers=None):
        data = body.encode() if isinstance(body, str) else body
        self.send_response(code)
        for k, v in self.out_headers(ctype, len(data), headers):
            self.send_header(k, v)
        self.end_headers()
        self.wfile.write(data)

    def js(self, obj, code=200, headers=None):
        self.send(code, json.dumps(obj), "application/json", headers)

    def redirect(self, url):
        self.send(302, "", headers={"Location": url})

    def base_url(self):
        """The address the browser used to reach us. Online that is always https, except in local tests."""
        if not _state["hosted"]:
            return f"http://localhost:{PORT}"
        host = self.headers.get("Host") or ""
        local = host.split(":")[0] in ("localhost", "127.0.0.1")
        return ("http://" if local else "https://") + host

    def client_ip(self):
        if _state["hosted"]:
            fwd = self.headers.get("X-Real-IP") or (self.headers.get("X-Forwarded-For") or "").split(",")[0].strip()
            if fwd:
                return fwd
        return self.client_address[0]

    def session_cookie(self):
        extra = "; SameSite=Lax" if _state["hosted"] else "; SameSite=Strict"  # Lax lets Google's sign-in redirect come back
        if self.base_url().startswith("https://"):
            extra += "; Secure"
        return f"fi_session={new_session()}; Path=/; Max-Age=2592000; HttpOnly" + extra

    def who(self):
        """Who is asking.
        On your own computer: "local" (this computer's browser), "phone" (unlocked with the passcode over Wi-Fi),
        "locked" (has not entered the passcode) or None (refused).
        Online: "setup" (no passcode created yet), "owner" (unlocked) or "locked"."""
        host, origin = self.headers.get("Host") or "", self.headers.get("Origin")
        cookie = self.headers.get("Cookie") or ""
        token = next((c.split("=", 1)[1] for c in cookie.replace(" ", "").split(";") if c.startswith("fi_session=")), "")
        if _state["hosted"]:
            if not host or (origin is not None and origin != self.base_url()):
                return None
            if not phone_enabled():
                return "setup"
            return "owner" if session_ok(token) else "locked"
        if self.client_address[0] in ("127.0.0.1", "::1"):
            ok_hosts = (f"localhost:{PORT}", f"127.0.0.1:{PORT}")
            if host in ok_hosts and (origin is None or origin in tuple("http://" + h for h in ok_hosts)):
                return "local"
            return None
        if not phone_enabled() or (origin is not None and origin not in ("http://" + host, "https://" + host)):
            return None
        return "phone" if session_ok(token) else "locked"

    def phone_login(self, setup=False):
        ip, now, st = self.client_ip(), time.time(), lockout_load()
        count, until = st["fails"].get(ip, (0, 0))
        if now < until or len(st["log"]) >= 20:
            return self.js({"error": "Too many tries. Wait a few minutes."}, 429)
        try:
            n = int(self.headers.get("Content-Length") or 0)
            passcode = str(json.loads(self.rfile.read(min(n, 2000)).decode() or "{}").get("passcode") or "")
        except ValueError:
            passcode = ""
        if setup:
            if len(passcode) < 8:
                return self.js({"error": "Use at least 8 characters."}, 400)
            with _lock:
                load_config()  # look again right now: someone else may have finished setup a moment ago
                if phone_enabled():
                    return self.js({"error": "A passcode already exists. Reload the page."}, 409)
                set_passcode(passcode)
        elif not check_passcode(passcode):
            count += 1
            st["log"].append(now)
            st["fails"][ip] = (0, now + 300) if count >= 5 else (count, 0)
            lockout_save(st)
            return self.js({"error": "Wrong passcode."}, 401)
        if ip in st["fails"]:
            del st["fails"][ip]
            lockout_save(st)
        return self.js({"ok": True}, headers={"Set-Cookie": self.session_cookie()})

    def do_GET(self):
        who = self.who()
        if who is None:
            return self.send(403, "Forbidden", "text/plain")
        u = urllib.parse.urlparse(self.path)
        q = dict(urllib.parse.parse_qsl(u.query))
        if _state["hosted"] and (self.headers.get("X-Forwarded-Proto") or "").split(",")[0].strip() == "http" \
                and self.base_url().startswith("https://"):
            return self.send(301, "", headers={"Location": self.base_url() + self.path})
        full = who in ("local", "owner")
        if u.path == "/icon.png":
            return self.send(200, ICON_PNG, "image/png")
        if u.path == "/manifest.json":
            return self.send(200, MANIFEST, "application/manifest+json")
        if who in ("locked", "setup"):
            if u.path.startswith("/api/"):
                return self.js({"error": "locked"}, 401)
            if u.path != "/":
                return self.redirect("/")
            return self.send(200, PHONE_LOGIN_HTML.replace("@@SETUP@@", "true" if who == "setup" else "false"))
        if not full and u.path in ("/login", "/callback", "/logout"):
            return self.redirect("/#settings")  # over home Wi-Fi, Google sign-in only works on the computer itself
        try:
            if u.path == "/":
                return self.send(200, INDEX_HTML)
            if u.path == "/login":
                if not has_oauth():
                    return self.redirect("/#settings")
                params = {"client_id": CONFIG["client_id"], "redirect_uri": self.base_url() + "/callback",
                          "response_type": "code", "scope": " ".join(SCOPES),
                          "access_type": "offline", "prompt": "consent", "state": make_state()}
                return self.redirect(AUTH_URL + "?" + urllib.parse.urlencode(params))
            if u.path == "/callback":
                if q.get("error"):
                    return self.send(400, "<p>Google said: %s. <a href='/'>Back</a></p>" % re.sub(r"[^\w .-]", "", q["error"]))
                if not q.get("code") or not state_ok(q.get("state")):
                    return self.send(400, "<p>Sign-in expired. <a href='/login'>Try again</a></p>")
                exchange_code(q["code"], self.base_url() + "/callback")
                _fit_cache["key"] = None
                return self.redirect("/")
            if u.path == "/logout":
                delete_json(TOKEN_FILE)
                _fit_cache["key"] = None
                return self.redirect("/#settings")
            if u.path == "/api/status":
                if re.fullmatch(r"-?\d{1,3}", q.get("tz") or "") and abs(int(q["tz"])) <= 840 and CONFIG.get("tz_min") != int(q["tz"]):
                    CONFIG["tz_min"] = int(q["tz"])
                    save_json(CONFIG_FILE, CONFIG)
                return self.js({"signedIn": access_token() is not None, "hasOAuth": has_oauth(),
                                "hasGemini": bool(CONFIG.get("gemini_key")), "redirectUri": self.base_url() + "/callback",
                                "today": today().isoformat(), "remote": who == "phone", "hosted": _state["hosted"],
                                "maxUpload": MAX_UPLOAD, "storage": "database" if DATABASE_URL else "file",
                                "phoneEnabled": phone_enabled(), "phoneListening": _state.get("lan", False),
                                "phoneUrls": lan_urls() if who == "local" else []})
            if u.path == "/api/check" and full:
                return self.js({"checks": check_connections()})
            if u.path == "/api/exercises":
                return self.js({"exercises": EXERCISES, "splits": SPLITS, "rotation": ROTATION})
            if u.path == "/api/state":
                return self.js(day_state(parse_day(q.get("day")).isoformat()))
            if u.path == "/api/history":
                return self.js({"days": history(q.get("end"), max(1, min(int(q.get("days", 30)), 120)))})
            if u.path == "/api/lastlift":
                return self.js(last_lift(q.get("exercise", ""), parse_day(q.get("day")).isoformat()))
            if u.path == "/api/chat":
                day = parse_day(q.get("day"))
                return self.js({"messages": rows_for((day - timedelta(days=3)).isoformat(), day.isoformat(), {"chat"})[-40:]})
            if u.path == "/api/blood":
                return self.js({"reports": list(reversed(rows_for("0000-00-00", "9999-99-99", {"blood"})))})
            if u.path in ("/api/fitbit", "/api/raw"):
                if access_token() is None:
                    return self.js({"error": "not signed in"}, 401)
                if u.path == "/api/fitbit":
                    return self.js(fitbit_summary(30, force=q.get("force") == "1"))
                t = q.get("type", "steps")
                if t not in RAW_TYPES:
                    return self.js({"error": "unknown type"}, 400)
                return self.js(api_get(f"dataTypes/{t}/dataPoints", {"pageSize": 25 if t in ("sleep", "exercise") else 50}))
            return self.send(404, "Not found", "text/plain")
        except Exception as e:
            return self.js({"error": str(e)}, 500)

    def do_POST(self):
        who = self.who()
        if who is None or "application/json" not in (self.headers.get("Content-Type") or ""):
            return self.send(403, "Forbidden", "text/plain")
        if who in ("locked", "setup"):
            if urllib.parse.urlparse(self.path).path == "/phone-login":
                return self.phone_login(setup=who == "setup")
            return self.js({"error": "locked"}, 401)
        try:
            n = int(self.headers.get("Content-Length") or 0)
            if n > MAX_UPLOAD * 1.4 + 200_000:
                return self.js({"error": f"That file is too large (limit about {MAX_UPLOAD // 1_000_000} MB)."}, 413)
            b = json.loads(self.rfile.read(n).decode() or "{}")
            path = urllib.parse.urlparse(self.path).path
            day = parse_day(b.get("day")).isoformat()
            if path == "/api/log":
                kind, data = b.get("kind"), b.get("data")
                if kind not in LOG_KINDS or not isinstance(data, dict):
                    return self.js({"error": "bad entry"}, 400)
                before = game_stats(day)["xp"]
                eid = add_entry(kind, day, data)
                g = game_stats(day)
                return self.js({"id": eid, "game": g, "xp_gained": g["xp"] - before})
            if path == "/api/delete":
                with db() as con:
                    con.execute("DELETE FROM entries WHERE id=?", (int(b.get("id")),))
                return self.js({"ok": True})
            if path == "/api/settings":
                if isinstance(b.get("settings"), dict):
                    put_settings(b["settings"])
                # over home Wi-Fi, keys can only be changed on the computer itself
                cfg = (b.get("config") or {}) if who in ("local", "owner") else {}
                changed, extra = False, None
                if "phone_passcode" in cfg:
                    code = str(cfg.get("phone_passcode") or "")
                    least = 8 if _state["hosted"] else 6
                    if len(code) < least and (code or _state["hosted"]):  # online, the passcode can't be switched off
                        return self.js({"error": f"Use a passcode of at least {least} characters."}, 400)
                    set_passcode(code) if code else clear_passcode()
                    if _state["hosted"]:  # every device is signed out; keep this one in
                        extra = {"Set-Cookie": self.session_cookie()}
                for k in ("gemini_key", "client_id", "client_secret"):
                    v = str(cfg.get(k) or "").strip().replace(" ", "")
                    if v:
                        CONFIG[k] = v
                        changed = True
                if changed:
                    save_json(CONFIG_FILE, CONFIG)
                    _model["name"] = None
                return self.js({"ok": True, "settings": get_settings()}, headers=extra)
            if path == "/api/ai/food":
                return self.js(ai_food(day, text=b.get("text"), audio_b64=b.get("audio_b64"), mime=b.get("mime")))
            if path == "/api/ai/workout":
                return self.js(ai_workout(day, b.get("split")))
            if path == "/api/ai/blood":
                return self.js(ai_blood(day, str(b.get("name") or "report")[:120], b.get("file_b64"), b.get("mime")))
            if path == "/api/ai/mind":
                msg = str(b.get("message") or "").strip()
                if not msg:
                    return self.js({"error": "Type a message first."}, 400)
                return self.js(ai_mind(day, msg[:4000]))
            if path == "/api/ai/weekly":
                return self.js(ai_weekly(day))
            return self.send(404, "Not found", "text/plain")
        except Exception as e:
            return self.js({"error": str(e)}, 500)


INDEX_HTML = r"""<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<meta name="apple-mobile-web-app-capable" content="yes"><meta name="mobile-web-app-capable" content="yes">
<meta name="apple-mobile-web-app-title" content="Fit Insights">
<meta name="theme-color" content="#fcfcfb" media="(prefers-color-scheme: light)"><meta name="theme-color" content="#1a1a19" media="(prefers-color-scheme: dark)">
<link rel="apple-touch-icon" href="/icon.png"><link rel="icon" href="/icon.png"><link rel="manifest" href="/manifest.json">
<title>Fit Insights</title>
<style>
:root{
  --bg:#f4f4f2;--card:#fcfcfb;--ink:#0b0b0b;--ink2:#52514e;--line:#e3e2de;--accent:#2a78d6;--accent-ink:#fff;
  --s1:#2a78d6;--s2:#eb6834;--s3:#1baf7a;--s4:#eda100;
  --good:#0ca30c;--warn:#fab219;--serious:#ec835a;--crit:#d03b3b;
  --goodbg:#e6f5e6;--warnbg:#fff3d6;--critbg:#fbe4e4;--infobg:#e4eefb;
}
@media (prefers-color-scheme:dark){:root{
  --bg:#111110;--card:#1a1a19;--ink:#f0efec;--ink2:#c3c2b7;--line:#33332f;--accent:#3987e5;
  --s1:#3987e5;--s2:#d95926;--s3:#199e70;--s4:#c98500;
  --goodbg:#12301a;--warnbg:#3a2f10;--critbg:#3a1717;--infobg:#14263d;
}}
*{box-sizing:border-box}
a{color:var(--accent)}
body{margin:0;font:15px/1.5 -apple-system,system-ui,"Segoe UI",Roboto,sans-serif;background:var(--bg);color:var(--ink)}
header{display:flex;gap:16px;align-items:center;flex-wrap:wrap;padding:12px 20px;background:var(--card);border-bottom:1px solid var(--line)}
h1{font-size:19px;margin:0}h2{font-size:15px;margin:0 0 10px}h3{font-size:13px;margin:14px 0 6px;color:var(--ink2);text-transform:uppercase;letter-spacing:.04em}
#game{flex:1;min-width:220px;font-size:13px;color:var(--ink2);display:flex;gap:12px;align-items:center;flex-wrap:wrap}
.xp{width:120px;height:8px;border-radius:4px;background:var(--line);overflow:hidden}.xp i{display:block;height:100%;background:var(--accent)}
nav{display:flex;gap:4px;padding:8px 16px;background:var(--card);border-bottom:1px solid var(--line);overflow-x:auto;position:sticky;top:0;z-index:5}
nav button{background:none;border:0;padding:8px 14px;border-radius:8px;font:inherit;color:var(--ink2);cursor:pointer;white-space:nowrap}
nav button.on{background:var(--infobg);color:var(--ink);font-weight:600}
main{max-width:1120px;margin:0 auto;padding:16px}
.grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(320px,1fr));gap:12px;margin-bottom:12px}
.grid.wide{grid-template-columns:repeat(auto-fit,minmax(440px,1fr))}
.tiles{display:grid;grid-template-columns:repeat(auto-fit,minmax(150px,1fr));gap:10px;margin-bottom:12px}
.card,.tile{background:var(--card);border:1px solid var(--line);border-radius:12px;padding:14px 16px}
.card{margin-bottom:12px}.grid .card{margin-bottom:0}
.tile .k{color:var(--ink2);font-size:12px}.tile .v{font-size:23px;font-weight:650;line-height:1.25}.tile .s{color:var(--ink2);font-size:12px}
.btn{background:var(--accent);color:var(--accent-ink);border:0;border-radius:8px;padding:8px 14px;font:inherit;font-size:14px;cursor:pointer;text-decoration:none;display:inline-block}
.btn.ghost{background:transparent;color:var(--ink);border:1px solid var(--line)}
.btn.sm{padding:4px 10px;font-size:13px}.btn:disabled{opacity:.5;cursor:default}
.btn.rec{background:var(--crit)}
input,select,textarea{font:inherit;padding:8px 10px;border-radius:8px;border:1px solid var(--line);background:var(--bg);color:var(--ink);max-width:100%}
textarea{width:100%;min-height:64px;resize:vertical}
label{font-size:12px;color:var(--ink2);display:block;margin-bottom:2px}
.row{display:flex;gap:10px;flex-wrap:wrap;align-items:flex-end;margin-bottom:10px}
.row>div{min-width:0}.grow{flex:1;min-width:200px}.grow input{width:100%}
.muted{color:var(--ink2)}.small{font-size:13px}.right{text-align:right}
table{width:100%;border-collapse:collapse;font-size:14px}th{text-align:left;color:var(--ink2);font-weight:500;font-size:12px}
th,td{padding:6px 8px;border-bottom:1px solid var(--line);vertical-align:top}tr:last-child td{border-bottom:0}
.tw{overflow-x:auto}
.b{display:inline-block;font-size:11px;padding:1px 7px;border-radius:10px;margin-left:6px;white-space:nowrap;color:var(--ink)}
.b1{background:var(--goodbg)}.b2{background:var(--warnbg)}.b3{background:var(--critbg)}
.note{border-radius:10px;padding:10px 14px;margin-bottom:12px;font-size:14px}
.note.good{background:var(--goodbg)}.note.warn{background:var(--warnbg)}.note.crit{background:var(--critbg)}.note.info{background:var(--infobg)}
.chips{display:flex;flex-wrap:wrap;gap:6px}.chip{border:1px solid var(--line);background:var(--bg);color:var(--ink);border-radius:16px;padding:4px 11px;font-size:13px;cursor:pointer}
.chip.on{background:var(--accent);color:var(--accent-ink);border-color:var(--accent)}
.bar{height:8px;background:var(--line);border-radius:4px;overflow:hidden;margin:4px 0 10px}.bar i{display:block;height:100%;background:var(--accent)}
.legend{display:flex;gap:14px;flex-wrap:wrap;font-size:12px;color:var(--ink2);margin-bottom:4px}.legend i{display:inline-block;width:10px;height:10px;border-radius:2px;margin-right:5px}
svg text{fill:var(--ink2);font-size:11px}
#tip{position:fixed;pointer-events:none;background:var(--card);border:1px solid var(--line);border-radius:8px;padding:6px 10px;font-size:12px;box-shadow:0 4px 14px rgba(0,0,0,.18);display:none;z-index:20}
#toast{position:fixed;bottom:20px;left:50%;transform:translateX(-50%);background:var(--ink);color:var(--bg);padding:8px 16px;border-radius:20px;font-size:14px;display:none;z-index:30}
.chat{max-height:380px;overflow-y:auto;display:flex;flex-direction:column;gap:8px;margin-bottom:10px}
.msg{padding:8px 12px;border-radius:12px;max-width:85%;white-space:pre-wrap}.msg.user{align-self:flex-end;background:var(--infobg)}.msg.coach{align-self:flex-start;background:var(--bg);border:1px solid var(--line)}
range-x{display:block}input[type=range]{width:100%;padding:0}
details summary{cursor:pointer;color:var(--ink2);font-size:13px}
pre{background:var(--bg);border:1px solid var(--line);border-radius:8px;padding:10px;max-height:340px;overflow:auto;font-size:12px}
.x{background:none;border:0;color:var(--ink2);cursor:pointer;font-size:15px;padding:0 4px}
body{padding-bottom:env(safe-area-inset-bottom)}
@media (max-width:640px){
  header{padding:10px 12px;gap:8px;padding-top:max(10px,env(safe-area-inset-top))}h1{font-size:17px;flex:1}
  #game{order:3;flex-basis:100%;gap:8px;font-size:12px}.xp{width:70px}
  nav{padding:6px 8px}nav button{padding:9px 11px}
  main{padding:10px}
  .grid,.grid.wide{grid-template-columns:1fr}
  .tiles{grid-template-columns:repeat(2,1fr);gap:8px}.tile{padding:10px 12px}.tile .v{font-size:20px}
  .card{padding:12px}
  input,select,textarea{font-size:16px}  /* 16px stops iPhone Safari zooming in on every tap */
  .btn{padding:10px 14px}.btn.sm{padding:7px 12px}.chip{padding:7px 12px;font-size:14px}.x{font-size:18px;padding:4px 8px}
  .msg{max-width:92%}th,td{padding:6px 5px}.grow.full{flex-basis:100%}
  #toast{bottom:calc(20px + env(safe-area-inset-bottom))}
}
</style></head><body>
<header><h1>Fit Insights</h1><div id="game"></div><input type="date" id="day" aria-label="Day"></header>
<nav id="nav"></nav>
<main id="view"><p class="muted">Loading…</p></main>
<div id="tip"></div><div id="toast"></div>
<script>
const $ = (s, r=document) => r.querySelector(s);
const esc = s => String(s ?? "").replace(/[&<>"']/g, c => ({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[c]));
const num = v => { const n = parseFloat(v); return isFinite(n) ? n : null; };
const fmt = v => v == null ? "–" : Math.round(v).toLocaleString();
const fmtH = m => m == null ? "–" : `${Math.floor(m/60)}h ${Math.round(m%60)}m`;
const addDays = (d, n) => { const t = new Date(d + "T12:00:00"); t.setDate(t.getDate()+n); return t.toISOString().slice(0,10); };
const shortD = d => new Date(d + "T12:00:00").toLocaleDateString(undefined, {weekday:"short", day:"numeric"});
const rich = t => esc(t).replace(/\*\*(.+?)\*\*/g, "<b>$1</b>").replace(/\n/g, "<br>");
const TABS = [["today","Today"],["workout","Workout"],["food","Food"],["body","Body"],["blood","Blood reports"],["mind","Mind"],["week","Week"],["settings","Settings"]];
const S = {tab:"today", day:null, st:null, hist:[], fit:null, ex:[], splits:{}, status:{}, split:null, form:{}, chat:null, blood:null, weekly:null, busy:{}};

async function api(path, body){
  const r = await fetch(path, body !== undefined ? {method:"POST", headers:{"Content-Type":"application/json"}, body:JSON.stringify(body)} : undefined);
  const j = await r.json().catch(() => ({error:"Unexpected response"}));
  if (r.status === 413) throw new Error("That file is too large for this app" + (S.status.maxUpload ? " (limit about " + Math.round(S.status.maxUpload/1e6) + " MB)." : "."));
  if (r.status === 401 && j.error === "locked") { location.reload(); throw new Error("Locked. Enter your passcode."); }
  if (!r.ok) throw new Error(j.error || ("HTTP " + r.status));
  return j;
}
const getStatus = () => api("/api/status?tz=" + (-new Date().getTimezoneOffset()));
let toastT;
function toast(m){ const t = $("#toast"); t.textContent = m; t.style.display = "block"; clearTimeout(toastT); toastT = setTimeout(() => t.style.display = "none", 2600); }
async function guard(key, fn){
  if (S.busy[key]) return; S.busy[key] = true; render();
  try { await fn(); } catch (e) { toast(e.message); }
  S.busy[key] = false; render();
}

/* ---------- data helpers ---------- */
const hday = d => S.hist.find(h => h.day === d);
const fitv = (k, d) => S.fit && S.fit[k] ? S.fit[k][d] ?? null : null;
function weightOn(d){ let w = null; for (const h of S.hist) if (h.day <= d && h.weight != null) w = h.weight; return w ?? (S.st.last_weight ? S.st.last_weight.kg : null); }
function tdee(d){
  const s = S.st.settings, w = weightOn(d); if (!w || !s.height_cm || !s.age) return null;
  const k = s.sex === "male" ? 5 : s.sex === "female" ? -161 : -78;
  const steps = fitv("steps", d);
  const f = steps == null ? 1.375 : steps < 5000 ? 1.2 : steps < 7500 ? 1.375 : steps < 10000 ? 1.465 : 1.55;
  return Math.round((10*w + 6.25*s.height_cm - 5*s.age + k) * f);
}
function calOut(d){ const f = fitv("calories", d); if (f) return {v:Math.round(f), src:"Fitbit"}; const t = tdee(d); return t ? {v:t, src:"estimate"} : null; }
function painNow(){ const p = S.st.pain || S.st.last_pain; return {back: p ? num(p.back) || 0 : 0, neck: p ? num(p.neck) || 0 : 0, fresh: !!S.st.pain, day: p ? p.day : null}; }
function safeFor(e, back, neck){
  if (e.neck || e.spine >= 3) return false;
  if (back >= 7 || neck >= 7) return e.spine === 1 && (e.group === "mobility" || e.name.startsWith("Walking"));
  if (back >= 4) return e.spine === 1;
  return true;
}
const exByName = n => S.ex.find(e => e.name.toLowerCase() === String(n || "").toLowerCase());
const SPINE = {1:"Low spine load", 2:"Medium spine load", 3:"High spine load"};
const badges = e => `<span class="b b${e.spine}">${SPINE[e.spine]}</span>${e.neck ? '<span class="b b3">Loads the neck</span>' : ""}`;
const lastN = n => S.hist.slice(-n);

/* ---------- charts (plain SVG, one axis, hover tooltip) ---------- */
function niceStep(raw){ const p = Math.pow(10, Math.floor(Math.log10(raw || 1))); const f = (raw || 1) / p; return (f <= 1 ? 1 : f <= 2 ? 2 : f <= 5 ? 5 : 10) * p; }
function chart(sel, o){
  const el = $(sel); if (!el) return;
  const {labels, series, type="bar", stacked=false, ref=null, height=190, unit=""} = o;
  const f = o.fmt || (v => (Math.abs(v) < 10 && v % 1 ? v.toFixed(1) : Math.round(v).toLocaleString()));
  const n = labels.length, W = 640, H = height, pl = 46, pr = 10, pt = 10, pb = 24, iw = W-pl-pr, ih = H-pt-pb;
  let lo = Infinity, hi = -Infinity;
  for (let i = 0; i < n; i++){
    const v = series.map(s => s.values[i]).filter(x => x != null); if (!v.length) continue;
    if (stacked){ hi = Math.max(hi, v.reduce((a,b) => a+b, 0)); lo = Math.min(lo, 0); } else { hi = Math.max(hi, ...v); lo = Math.min(lo, ...v); }
  }
  if (!isFinite(hi)){ el.innerHTML = `<p class="muted small">${esc(o.empty || "No data yet.")}</p>`; return; }
  if (ref){ hi = Math.max(hi, ref.value); lo = Math.min(lo, ref.value); }
  if (type === "bar"){ lo = Math.min(lo, 0); hi = Math.max(hi, 0); } else { const pad = (hi-lo)*0.25 || Math.abs(hi)*0.05 || 1; lo -= pad; hi += pad; }
  const step = niceStep((hi-lo)/4); lo = Math.floor(lo/step)*step; hi = Math.ceil(hi/step)*step; if (hi === lo) hi = lo + step;
  const y = v => pt + ih - (v-lo)/(hi-lo)*ih, band = iw/n, x = i => pl + band*i + band/2;
  let g = "";
  for (let t = lo; t <= hi + step/1000; t += step) g += `<line x1="${pl}" x2="${W-pr}" y1="${y(t)}" y2="${y(t)}" style="stroke:var(--line)" stroke-width="${Math.abs(t) < step/1000 ? 1.5 : 1}"/><text x="${pl-6}" y="${y(t)+4}" text-anchor="end">${f(t)}</text>`;
  const every = Math.ceil(n/8);
  labels.forEach((l, i) => { if (i % every === 0 || i === n-1 && (n-1) % every > every/2) g += `<text x="${x(i)}" y="${H-6}" text-anchor="middle">${esc(l)}</text>`; });
  const rbar = (bx, v0, v1, w, col) => {  // bar from v0 (base) to v1 (data end), rounded at the data end
    const y0 = y(v0), y1 = y(v1), r = Math.min(4, w/2, Math.abs(y1-y0)); if (Math.abs(y1-y0) < 0.5) return "";
    const d = y1 < y0 ? -1 : 1;
    return `<path d="M${bx},${y0}V${y1-d*r}Q${bx},${y1} ${bx+r},${y1}H${bx+w-r}Q${bx+w},${y1} ${bx+w},${y1-d*r}V${y0}Z" style="fill:${col}"/>`;
  };
  if (type === "bar" && stacked){
    const w = Math.min(30, band*0.66);
    for (let i = 0; i < n; i++){ let acc = 0; const live = series.filter(s => s.values[i]);
      live.forEach((s, k) => { const v = s.values[i], top = k === live.length-1;
        if (top) g += rbar(x(i)-w/2, acc, acc+v, w, s.color);
        else { const h = y(acc)-y(acc+v); if (h > 2.5) g += `<rect x="${x(i)-w/2}" y="${y(acc+v)+2}" width="${w}" height="${h-2}" style="fill:${s.color}"/>`; }
        acc += v; }); }
  } else if (type === "bar"){
    const k = series.length, w = Math.min(26, band*0.72/k);
    series.forEach((s, j) => s.values.forEach((v, i) => { if (v != null) g += rbar(x(i) - (k*w + (k-1)*2)/2 + j*(w+2), 0, v, w, s.color); }));
  } else {
    series.forEach(s => { const pts = s.values.map((v, i) => v == null ? null : [x(i), y(v)]).filter(Boolean);
      if (pts.length > 1) g += `<path d="M${pts.map(p => p.join(",")).join("L")}" fill="none" style="stroke:${s.color}" stroke-width="2" stroke-linejoin="round"/>`;
      pts.forEach(p => g += `<circle cx="${p[0]}" cy="${p[1]}" r="4" style="fill:${s.color};stroke:var(--card)" stroke-width="2"/>`); });
  }
  if (ref) g += `<line x1="${pl}" x2="${W-pr}" y1="${y(ref.value)}" y2="${y(ref.value)}" style="stroke:var(--ink2)" stroke-dasharray="4 4"/><text x="${W-pr}" y="${y(ref.value)-5}" text-anchor="end">${esc(ref.label)}</text>`;
  const legend = series.length > 1 ? `<div class="legend">${series.map(s => `<span><i style="background:${s.color}"></i>${esc(s.name)}</span>`).join("")}</div>` : "";
  el.innerHTML = `${legend}<svg viewBox="0 0 ${W} ${H}" width="100%" role="img" aria-label="${esc(o.title || "chart")}">${g}<rect x="${pl}" y="${pt}" width="${iw}" height="${ih}" fill="transparent" class="hit"/></svg>`;
  const hit = $(".hit", el), tip = $("#tip");
  hit.onmousemove = ev => {
    const b = hit.getBoundingClientRect(), i = Math.max(0, Math.min(n-1, Math.floor((ev.clientX-b.left)/b.width*n)));
    const rows = series.filter(s => s.values[i] != null).map(s => `<div><i style="display:inline-block;width:8px;height:8px;border-radius:2px;background:${s.color};margin-right:5px"></i>${esc(s.name)}: <b>${f(s.values[i])}${unit}</b></div>`).join("");
    tip.innerHTML = `<div class="muted">${esc(o.full ? o.full[i] : labels[i])}</div>${rows || "No data"}`;
    tip.style.display = "block"; tip.style.left = Math.min(ev.clientX+14, innerWidth-190) + "px"; tip.style.top = (ev.clientY+14) + "px";
  };
  hit.onmouseleave = () => tip.style.display = "none";
}

/* ---------- loading ---------- */
async function refresh(){
  const [st, hist] = await Promise.all([api(`/api/state?day=${S.day}`), api(`/api/history?end=${S.day}&days=30`)]);
  S.st = st; S.hist = hist.days; render();
}
async function loadFit(force){
  if (!S.status.signedIn) return;
  try { S.fit = await api("/api/fitbit" + (force ? "?force=1" : "")); render(); } catch (e) { S.fitErr = e.message; }
}
async function log(kind, data){
  const r = await api("/api/log", {kind, day:S.day, data});
  if (r.xp_gained > 0) toast(`+${r.xp_gained} XP`);
  await refresh(); return r;
}
async function del(id){ await api("/api/delete", {id}); await refresh(); }

function header(){
  const g = S.st.game;
  $("#game").innerHTML = `<b style="color:var(--ink)">Level ${g.level}</b><span class="xp" title="${g.xp_in_level} of ${g.xp_per_level} XP"><i style="width:${100*g.xp_in_level/g.xp_per_level}%"></i></span>
    <span>${g.xp_in_level}/${g.xp_per_level} XP</span><span>${g.streak}-day streak</span><span>${g.comebacks} comeback${g.comebacks === 1 ? "" : "s"}</span>`;
  $("#nav").innerHTML = TABS.map(([k, l]) => `<button data-tab="${k}" class="${S.tab === k ? "on" : ""}">${l}</button>`).join("");
}
function render(){
  if (!S.st) return;
  header();
  const v = VIEWS[S.tab]();
  $("#view").innerHTML = v.html;
  document.querySelectorAll('#view input[type=number]').forEach(i => i.inputMode = "decimal");
  if (v.after) v.after();
}
const needAI = () => S.status.hasGemini ? "" : `<div class="note info">AI features need a free Gemini API key. Add it in <a href="#settings" data-tab="settings">Settings</a>.</div>`;
const tile = (k, v, s) => `<div class="tile"><div class="k">${k}</div><div class="v">${v}</div><div class="s">${s || ""}</div></div>`;

/* ---------- shared cards ---------- */
function waterCard(){
  const s = S.st.settings, ml = S.st.water_ml, t = s.water_target_ml || 3000;
  return `<div class="card"><h2>Water</h2><div><b>${(ml/1000).toFixed(2)} L</b> <span class="muted">of ${(t/1000).toFixed(1)} L</span></div>
    <div class="bar"><i style="width:${Math.min(100, 100*ml/t)}%"></i></div>
    <div class="chips"><button class="chip" data-water="250">+ 250 ml</button><button class="chip" data-water="500">+ 500 ml</button><button class="chip" data-water="750">+ 750 ml</button>${ml > 0 ? '<button class="chip" data-water="-250">Undo 250</button>' : ""}</div></div>`;
}
function suppCard(){
  const list = S.st.settings.supplements || [], taken = S.st.supps;
  return `<div class="card"><h2>Supplements</h2>${list.length ? `<div class="chips">${list.map(n => { const t = taken.find(x => x.name === n);
    return `<button class="chip ${t ? "on" : ""}" data-supp="${esc(n)}" ${t ? `data-id="${t.id}"` : ""}>${t ? "✓ " : ""}${esc(n)}</button>`; }).join("")}</div>
    <p class="muted small" style="margin:8px 0 0">${taken.length} of ${list.length} taken today. Tap to mark.</p>` : `<p class="muted small">Add your supplements in Settings.</p>`}</div>`;
}
function painCard(){
  const p = S.st.pain || {}, lp = S.st.last_pain;
  return `<div class="card"><h2>Pain check-in</h2>
    <label>Lower back: <b id="pbv">${p.back ?? (lp ? lp.back : 0)}</b> / 10</label><input type="range" min="0" max="10" id="pb" value="${p.back ?? (lp ? lp.back : 0)}">
    <label style="margin-top:8px">Neck: <b id="pnv">${p.neck ?? (lp ? lp.neck : 0)}</b> / 10</label><input type="range" min="0" max="10" id="pn" value="${p.neck ?? (lp ? lp.neck : 0)}">
    <div class="row" style="margin-top:10px"><div class="grow"><input id="pnote" placeholder="Note (optional): what hurts, when" value="${esc(p.note || "")}"></div><button class="btn" data-act="pain">${S.st.pain ? "Update" : "Save"}</button></div>
    <p class="muted small" style="margin:0">${S.st.pain ? "Checked in today." : lp ? `Last check-in: ${shortD(lp.day)}. Not checked in today.` : "Not checked in yet."} 0 to 3 trains normally, 4 to 6 switches to low-load moves, 7+ means rest.</p></div>`;
}
function bindPain(){ const pb = $("#pb"), pn = $("#pn"); if (pb){ pb.oninput = () => $("#pbv").textContent = pb.value; pn.oninput = () => $("#pnv").textContent = pn.value; } }

/* ---------- views ---------- */
const VIEWS = {};

VIEWS.today = () => {
  const st = S.st, s = st.settings, g = st.game, d = S.day, out = calOut(d), kin = st.totals.kcal, p = painNow();
  const sl = fitv("sleep", d), split = S.split || st.next_split, trained = st.sets.length > 0;
  let banner = "";
  if (st.slips.length) banner = `<div class="note good"><b>Slip logged.</b> Writing it down is the opposite of avoiding it. The next meal is just a normal meal.</div>`;
  else if (g.comeback_today) banner = `<div class="note good"><b>Comeback bonus: +50 XP.</b> You showed up after a gap. That is the hardest rep there is.</div>`;
  else if (!g.logged_today && g.gap_days >= 1) banner = `<div class="note info"><b>${g.gap_days} day${g.gap_days > 1 ? "s" : ""} without a log.</b> That's data, not a verdict. One small entry below earns the comeback bonus.</div>`;
  let next;
  if (!st.pain) next = ["Do the 10-second pain check-in below.", null];
  else if (!st.foods.length) next = ["Log your last meal.", "food"];
  else if (!trained && p.back < 7 && p.neck < 7) next = [`Open today's plan: ${esc(split)}.`, "workout"];
  else if (st.water_ml < (s.water_target_ml || 3000)) next = ["Drink a glass of water and tap + 250 ml.", null];
  else next = ["Everything's logged. Nothing more needed today.", null];
  const deficit = out && st.foods.length ? out.v - kin : null;
  return {html: `${banner}
    <div class="note info"><b>Next small step:</b> ${next[0]} ${next[1] ? `<a href="#${next[1]}" data-tab="${next[1]}">Go</a>` : ""}</div>
    <div class="tiles">
      ${tile("Calories eaten", fmt(kin), `target ${fmt(s.kcal_target)}`)}
      ${tile("Calories burned", out ? fmt(out.v) : "–", out ? (out.src === "Fitbit" ? "Fitbit, so far today" : "estimate from your profile") : "add weight, height, age in Settings")}
      ${tile(deficit != null && deficit < 0 ? "Surplus" : "Deficit", deficit != null ? fmt(Math.abs(deficit)) : "–", deficit != null ? "burned minus eaten, so far" : "log food to see this")}
      ${tile("Protein", st.totals.protein + " g", `target ${fmt(s.protein_target)} g`)}
      ${tile("Sleep", sl ? fmtH(sl.minutesAsleep) : "–", S.status.signedIn ? "last night" : "connect Fitbit")}
      ${tile("Steps", fmt(fitv("steps", d)), S.status.signedIn ? "today" : "connect Fitbit")}
      ${tile("Resting HR", fitv("restingHr", d) != null ? Math.round(fitv("restingHr", d)) + " bpm" : "–", "")}
      ${tile("Weight", weightOn(d) != null ? weightOn(d).toFixed(1) + " kg" : "–", s.goal_kg ? `goal ${s.goal_kg} kg` : "")}
    </div>
    ${S.status.signedIn ? "" : `<div class="note warn">Fitbit isn't connected, so sleep, steps and calories burned are blank. Connect it in <a href="#settings" data-tab="settings">Settings</a>.</div>`}
    <div class="grid">${painCard()}
      <div class="card"><h2>Today's training</h2>
        <p style="margin:0 0 8px">${trained ? `<b>${st.sets.length} entr${st.sets.length > 1 ? "ies" : "y"} logged.</b>` : p.back >= 7 || p.neck >= 7 ? "<b>Rest day.</b> Pain is 7 or more: walking and mobility only." : `Up next in your split: <b>${esc(split)}</b>`}</p>
        <a class="btn" href="#workout" data-tab="workout">${trained ? "Open workout log" : "Open today's plan"}</a></div>
    </div>
    <div class="grid">${waterCard()}${suppCard()}</div>`, after: bindPain};
};

VIEWS.workout = () => {
  const st = S.st, split = S.split || st.next_split, groups = S.splits[split] || [], p = painNow(), rest = p.back >= 7 || p.neck >= 7;
  const pool = rest ? S.ex.filter(e => safeFor(e, p.back, p.neck)) : S.ex.filter(e => groups.includes(e.group) && safeFor(e, p.back, p.neck));
  const byG = {}; pool.forEach(e => (byG[e.group] = byG[e.group] || []).push(e));
  const f = S.form, cur = exByName(f.exercise), timed = cur && (cur.group === "cardio" || cur.group === "mobility");
  let warn = "";
  if (cur && !safeFor(cur, p.back, p.neck)) warn = `<div class="note crit"><b>${esc(cur.name)}</b> is ${cur.neck ? "a neck-loading move" : SPINE[cur.spine].toLowerCase()}${p.back >= 4 ? ` and your back pain is ${p.back}/10` : ""}. ${cur.alt ? `Safer swap: <button class="chip" data-pick="${esc(cur.alt)}">${esc(cur.alt)}</button>` : "Consider skipping it today."}</div>`;
  const saved = st.plan && st.plan.split === split ? st.plan : null;
  const stale = saved && (saved.back !== p.back || saved.neck !== p.neck), plan = stale ? null : saved;
  const vcls = {GO:"good", MODIFY:"warn", REST:"crit"};
  const vol = st.sets.reduce((a, x) => a + (x.minutes != null ? 0 : (num(x.weight) || 0) * (num(x.reps) || 0) * (num(x.sets) || 1)), 0);
  const ef = S.exFilter || {};
  const dir = S.ex.filter(e => (!ef.g || e.group === ef.g) && (!ef.q || e.equipment === ef.q));
  return {html: `
    <div class="card"><h2>Split</h2><div class="chips">${Object.keys(S.splits).map(n => `<button class="chip ${n === split ? "on" : ""}" data-split="${esc(n)}">${esc(n)}</button>`).join("")}</div>
      <p class="muted small" style="margin:8px 0 0">Back pain ${p.back}/10, neck ${p.neck}/10${p.fresh ? "" : p.day ? ` (from ${shortD(p.day)}, not checked today)` : " (no check-in yet)"}. <a href="#today" data-tab="today">Update check-in</a></p></div>
    ${rest ? `<div class="note crit"><b>Rest day.</b> Pain is 7 or more, so only walking and gentle mobility are offered. If pain is sharp, shooting down a leg or arm, or comes with numbness or weakness, see a doctor.</div>` : ""}
    <div class="grid">
      <div class="card"><h2>Back-safe picks for today</h2>
        ${Object.keys(byG).map(gk => `<h3>${gk}</h3><div class="chips">${byG[gk].map(e => `<button class="chip" data-pick="${esc(e.name)}" title="${e.equipment}">${esc(e.name)}</button>`).join("")}</div>`).join("") || '<p class="muted small">Nothing to show.</p>'}
        <p class="muted small" style="margin:10px 0 0">Filtered by fixed rules from your pain check-in: high spine-load and neck-loading moves are never offered, and at pain 4+ only low-load moves stay. General guidance, not medical advice.</p></div>
      <div class="card"><h2>AI coach plan</h2>${needAI()}
        ${plan ? `<div class="note ${vcls[plan.verdict] || "info"}"><b>${esc(plan.verdict || "PLAN")}:</b> ${esc(plan.why)}</div>
          ${plan.warmup && plan.warmup.length ? `<h3>Warm-up</h3><div class="small">${plan.warmup.map(esc).join(" · ")}</div>` : ""}
          ${plan.exercises && plan.exercises.length ? `<h3>Exercises</h3><div class="tw"><table>${plan.exercises.map(x => `<tr><td><b>${esc(x.name)}</b><div class="muted small">${esc(x.cue || "")}</div></td><td style="white-space:nowrap">${esc(x.sets)} × ${esc(x.reps)}<div class="muted small">${esc(x.weight_hint || "")}</div></td><td><button class="btn sm ghost" data-use='${esc(JSON.stringify({exercise:x.name, sets:x.sets, reps:parseInt(x.reps) || ""}))}'>Use</button></td></tr>`).join("")}</table></div>` : ""}
          ${plan.avoid_today && plan.avoid_today.length ? `<h3>Avoid today</h3><div class="small">${plan.avoid_today.map(esc).join("<br>")}</div>` : ""}
          ${plan.cardio ? `<h3>Cardio</h3><div class="small">${esc(plan.cardio)}</div>` : ""}
          ${plan.red_flags ? `<p class="muted small">${esc(plan.red_flags)}</p>` : ""}` : `${stale ? '<div class="note warn">Your pain check-in changed since the last plan, so it was cleared. Get a fresh one.</div>' : ""}<p class="muted small">Gets a plan for ${esc(split)} from your pain level, last lifts and Fitbit sleep and HRV. It can only choose from the back-safe picks.</p>`}
        <button class="btn" data-act="plan" ${S.busy.plan || !S.status.hasGemini ? "disabled" : ""}>${S.busy.plan ? "Thinking…" : plan ? "Regenerate plan" : "Get today's plan"}</button></div>
    </div>
    <div class="card"><h2>Log a set</h2>${warn}
      <div class="row"><div class="grow full"><label>Exercise (search ${S.ex.length} moves, or type your own)</label><input id="fx" list="exlist" value="${esc(f.exercise || "")}" placeholder="e.g. Seated Cable Row" autocomplete="off"><datalist id="exlist">${S.ex.map(e => `<option value="${esc(e.name)}">${e.group} · ${e.equipment}</option>`).join("")}</datalist></div>
        ${timed ? `<div><label>Minutes</label><input id="fm" type="number" min="1" style="width:90px" value="${esc(f.minutes || "")}"></div>`
          : `<div><label>Weight (kg)</label><input id="fw" type="number" min="0" step="0.5" style="width:90px" value="${esc(f.weight ?? "")}"></div>
             <div><label>Reps</label><input id="fr" type="number" min="1" style="width:74px" value="${esc(f.reps ?? "")}"></div>
             <div><label>Sets</label><input id="fs" type="number" min="1" style="width:74px" value="${esc(f.sets ?? 3)}"></div>`}
        <button class="btn" data-act="addset">Add</button></div>
      <div class="muted small" id="lastlift">${cur ? `${cur.group} · ${cur.equipment} ${badges(cur)}` : ""} ${S.last && S.last.day && S.lastFor === f.exercise ? ` &nbsp;Last time (${shortD(S.last.day)}): ${S.last.sets.map(x => x.minutes != null ? `${x.minutes} min` : `${x.sets}×${x.reps} @ ${x.weight} kg`).join(", ")}` : ""}</div></div>
    <div class="card"><h2>Logged for ${shortD(S.day)}</h2>
      ${st.sets.length ? `<div class="tw"><table><tr><th>Exercise</th><th>Work</th><th>Split</th><th></th></tr>${st.sets.map(x => `<tr><td>${esc(x.exercise)}</td><td>${x.minutes != null ? `${esc(x.minutes)} min` : `${esc(x.sets)} × ${esc(x.reps)} @ ${esc(x.weight)} kg`}</td><td class="muted">${esc(x.split || "")}</td><td class="right"><button class="x" data-del="${x.id}" title="Delete">✕</button></td></tr>`).join("")}</table></div>
        <p class="muted small" style="margin:8px 0 0">Total volume: ${fmt(vol)} kg</p>` : `<p class="muted small">Nothing logged yet. Pick a move above.</p>`}</div>
    <details class="card" ${S.dirOpen ? "open" : ""} id="dir"><summary>Exercise directory (${S.ex.length} moves with spine-load ratings)</summary>
      <div class="row" style="margin-top:10px"><div><label>Muscle group</label><select id="dg"><option value="">All</option>${[...new Set(S.ex.map(e => e.group))].map(x => `<option ${ef.g === x ? "selected" : ""}>${x}</option>`).join("")}</select></div>
        <div><label>Equipment</label><select id="dq"><option value="">All</option>${[...new Set(S.ex.map(e => e.equipment))].map(x => `<option ${ef.q === x ? "selected" : ""}>${x}</option>`).join("")}</select></div></div>
      <div class="tw"><table><tr><th>Exercise</th><th>Group</th><th>Equipment</th><th>Rating</th><th>Safer swap</th></tr>${dir.map(e => `<tr><td><a href="#" data-pick="${esc(e.name)}">${esc(e.name)}</a></td><td>${e.group}</td><td>${e.equipment}</td><td>${badges(e)}</td><td class="muted">${esc(e.alt)}</td></tr>`).join("")}</table></div></details>`,
    after(){
      const fx = $("#fx");
      fx.onchange = async () => { readForm(); await pickEx(fx.value); };
      const dg = $("#dg"), dq = $("#dq"), dir = $("#dir");
      dir.ontoggle = () => S.dirOpen = dir.open;
      dg.onchange = dq.onchange = () => { S.exFilter = {g:dg.value, q:dq.value}; S.dirOpen = true; readForm(); render(); };
    }};
};
function readForm(){ const g = id => { const e = $(id); return e ? e.value : undefined; };
  if (!$("#fx")) return;
  S.form = {...S.form, exercise:g("#fx"), weight:g("#fw") ?? S.form.weight, reps:g("#fr") ?? S.form.reps, sets:g("#fs") ?? S.form.sets, minutes:g("#fm") ?? S.form.minutes}; }
async function pickEx(name, extra){
  S.form = {...S.form, exercise:name, ...(extra || {})}; S.last = null; S.lastFor = name;
  try { S.last = await api(`/api/lastlift?day=${S.day}&exercise=${encodeURIComponent(name)}`);
    const l = S.last.sets[S.last.sets.length-1]; if (l && l.minutes == null && !(extra && extra.reps)) S.form = {...S.form, weight:l.weight, reps:l.reps, sets:l.sets}; else if (l && l.minutes == null) S.form.weight = l.weight; } catch (e) {}
  render(); const t = $("#fw") || $("#fm"); if (t) t.focus();
}

VIEWS.food = () => {
  const st = S.st, s = st.settings, k = st.totals.kcal, pr = st.totals.protein;
  const canRec = !!(navigator.mediaDevices && window.isSecureContext && window.MediaRecorder);  // browsers only allow recording on localhost or HTTPS
  return {html: `${needAI()}
    <div class="grid">
      <div class="card"><h2>What did you eat?</h2>
        <textarea id="ftext" placeholder="Type it, in English or Hinglish. e.g. 2 roti, dal, thoda chawal, ek chai with sugar"></textarea>
        <div class="row" style="margin-top:8px"><button class="btn" data-act="foodtext" ${S.busy.food || !S.status.hasGemini ? "disabled" : ""}>${S.busy.food ? "Estimating…" : "Estimate calories"}</button>
          ${canRec ? `<button class="btn ghost" id="recbtn" data-act="rec" ${S.busy.food || !S.status.hasGemini ? "disabled" : ""}>Record voice note</button>` : ""}</div>
        <p class="muted small" style="margin:0">${canRec ? "Voice: press record, say what you ate, press stop." : "To speak it: tap the box, then the microphone key on your keyboard, and say what you ate."} Estimates are rough (±20%). Consistency matters more than precision.</p>
        <h3>Or add it yourself</h3>
        <div class="row"><div class="grow"><input id="mname" placeholder="Food name"></div><div><input id="mk" type="number" placeholder="kcal" style="width:90px"></div><div><input id="mp" type="number" placeholder="protein g" style="width:100px"></div><button class="btn ghost" data-act="foodmanual">Add</button></div></div>
      <div class="card"><h2>Today</h2>
        <div>Calories: <b>${fmt(k)}</b> <span class="muted">of ${fmt(s.kcal_target)}</span></div><div class="bar"><i style="width:${Math.min(100, 100*k/(s.kcal_target || 2000))}%;${k > (s.kcal_target || 2000)*1.1 ? "background:var(--serious)" : ""}"></i></div>
        <div>Protein: <b>${pr} g</b> <span class="muted">of ${fmt(s.protein_target)} g</span></div><div class="bar"><i style="width:${Math.min(100, 100*pr/(s.protein_target || 120))}%"></i></div>
        ${k > (s.kcal_target || 2000)*1.1 ? `<p class="small" style="margin:0">Over target today. One day rarely moves a week. No need to "make up for it" tomorrow: just eat normally. <a href="#mind" data-tab="mind">Talk it through</a></p>` : ""}</div>
    </div>
    <div class="card"><h2>Food log for ${shortD(S.day)}</h2>
      ${st.foods.length ? `<div class="tw"><table><tr><th>Food</th><th class="right">kcal</th><th class="right">Protein</th><th></th></tr>${st.foods.map(x => `<tr><td>${esc(x.name)}${x.items && x.items.length ? `<details><summary>${x.items.length} item${x.items.length > 1 ? "s" : ""}${x.confidence ? `, ${esc(x.confidence)} confidence` : ""}</summary>${x.items.map(i => `<div class="small">${esc(i.name)}${i.qty ? ` (${esc(i.qty)})` : ""}: ${esc(i.kcal)} kcal${i.assumption ? ` <span class="muted">· ${esc(i.assumption)}</span>` : ""}</div>`).join("")}</details>` : ""}</td><td class="right">${fmt(x.kcal)}</td><td class="right">${fmt(x.protein)} g</td><td class="right"><button class="x" data-del="${x.id}" title="Delete">✕</button></td></tr>`).join("")}</table></div>` : `<p class="muted small">Nothing logged yet.</p>`}</div>
    <div class="grid">${waterCard()}${suppCard()}</div>`};
};

VIEWS.body = () => {
  const st = S.st, s = st.settings, d = S.day, w = weightOn(d), h14 = lastN(14), h30 = S.hist;
  const firstW = h30.find(h => h.weight != null), past = h30.filter(h => h.weight != null && h.day <= addDays(d, -7)).pop();
  const base = past || (firstW && firstW.day < d ? firstW : null), w7 = base ? base.weight : null;
  const full = lastN(7).filter(h => h.foods > 0 && calOut(h.day) && h.day !== S.status.today);
  const defSum = full.reduce((a, h) => a + calOut(h.day).v - h.kcal, 0);
  const azm = lastN(7).reduce((a, h) => a + (fitv("azm", h.day) || 0), 0), manual = lastN(7).reduce((a, h) => a + h.cardio_min, 0);
  const hasAzm = S.fit && S.fit.azm && Object.keys(S.fit.azm).length > 0, done = hasAzm ? azm : manual, target = s.cardio_target_min || 150, p = painNow();
  let advice;
  if (p.back >= 7 || p.neck >= 7) advice = "Pain is 7 or more today. Skip cardio load. Short, easy flat walks (5 to 10 minutes) only if they feel fine.";
  else if (done >= target) advice = "Weekly target reached. Anything extra is optional: keep it to easy walking.";
  else advice = `About ${Math.ceil((target-done)/3)} minutes today would put you on track (${Math.round(target-done)} min left this week). Low-impact picks: incline treadmill walk, elliptical, swimming, recumbent bike.${p.back >= 4 ? " With back pain at 4+, stick to flat walking or swimming." : ""} Skip the rowing machine and running while the back is sensitive.`;
  return {html: `
    <div class="tiles">
      ${tile("Weight", w != null ? w.toFixed(1) + " kg" : "–", st.weight ? "logged today" : "latest")}
      ${tile("Weight change", w != null && w7 != null ? (w-w7 > 0 ? "+" : "") + (w-w7).toFixed(1) + " kg" : "–", base ? `since ${shortD(base.day)}` : "needs two weigh-ins")}
      ${tile("To goal", w != null && s.goal_kg ? Math.abs(w-s.goal_kg).toFixed(1) + " kg" : "–", s.goal_kg ? `goal ${s.goal_kg} kg` : "set a goal in Settings")}
      ${tile(defSum < 0 ? "7-day surplus" : "7-day deficit", full.length ? fmt(Math.abs(defSum)) + " kcal" : "–", full.length ? `${full.length} of 7 days with food logged` : "log food to see this")}
      ${tile("Expected from deficit", full.length ? (defSum >= 0 ? "−" : "+") + Math.abs(defSum/7700).toFixed(2) + " kg" : "–", "7,700 kcal ≈ 1 kg of fat")}
    </div>
    <div class="card"><h2>Log weight</h2><div class="row"><div><label>Weight (kg), ideally morning, same conditions</label><input id="wkg" type="number" step="0.1" min="20" max="300" value="${st.weight ? esc(st.weight.kg) : ""}" style="width:130px"></div><button class="btn" data-act="weight">Save</button></div>
      <p class="muted small" style="margin:0">Daily weight swings 1 to 2 kg from water and salt. Judge the weekly trend, never one reading.</p></div>
    <div class="grid">
      <div class="card"><h2>Weight, last 30 days (kg)</h2><div id="cWeight"></div></div>
      <div class="card"><h2>Calories eaten vs burned, last 14 days</h2><div id="cCal"></div></div>
    </div>
    <div class="card"><h2>Cardio load this week</h2>
      <div><b>${Math.round(done)} min</b> <span class="muted">of ${target} min ${hasAzm ? "(Fitbit active zone minutes, last 7 days)" : "(cardio minutes you logged, last 7 days)"}</span></div>
      <div class="bar"><i style="width:${Math.min(100, 100*done/target)}%"></i></div><p class="small" style="margin:0">${advice}</p></div>
    <div class="grid wide">
      <div class="card"><h2>Sleep by stage, last 14 nights (hours)</h2><div id="cSleep"></div></div>
      <div class="card"><h2>Steps, last 14 days</h2><div id="cSteps"></div></div>
      <div class="card"><h2>Resting heart rate (bpm)</h2><div id="cRhr"></div></div>
      <div class="card"><h2>Heart rate variability (ms)</h2><div id="cHrv"></div></div>
    </div>
    ${S.fit && Object.keys(S.fit.errors || {}).length ? `<div class="card"><h2>Some Fitbit data couldn't load</h2>${Object.entries(S.fit.errors).map(([k, v]) => `<div class="small"><b>${esc(k)}</b>: ${esc(v)}</div>`).join("")}<p class="muted small">Open Settings → Raw data explorer for that type and send a screenshot.</p></div>` : ""}`,
    after(){
      const L14 = h14.map(h => shortD(h.day)), F14 = h14.map(h => h.day), L30 = h30.map(h => shortD(h.day)), noFit = S.status.signedIn ? "No data yet." : "Connect Fitbit in Settings to see this.";
      chart("#cWeight", {type:"line", labels:L30, full:h30.map(h => h.day), series:[{name:"Weight", color:"var(--s1)", values:h30.map(h => h.weight)}], ref:s.goal_kg && firstW ? {value:+s.goal_kg, label:"goal"} : null, unit:" kg", fmt:v => v.toFixed(1), empty:"Log your weight to start the trend.", title:"Weight"});
      chart("#cCal", {labels:L14, full:F14, series:[{name:"Eaten", color:"var(--s1)", values:h14.map(h => h.foods ? h.kcal : null)}, {name:"Burned", color:"var(--s2)", values:h14.map(h => { const o = calOut(h.day); return o ? o.v : null; })}], unit:" kcal", empty:"Log food to see this.", title:"Calories"});
      const stg = [["DEEP","Deep","var(--s1)"],["LIGHT","Light","var(--s2)"],["REM","REM","var(--s3)"],["AWAKE","Awake","var(--s4)"]];
      chart("#cSleep", {stacked:true, labels:L14, full:F14, series:stg.map(([k, n, c]) => ({name:n, color:c, values:h14.map(h => { const x = fitv("sleep", h.day); return x && x.stages[k] != null ? +(x.stages[k]/60).toFixed(2) : null; })})), unit:" h", fmt:v => (+v).toFixed(1), empty:noFit, title:"Sleep stages"});
      chart("#cSteps", {labels:L14, full:F14, series:[{name:"Steps", color:"var(--s1)", values:h14.map(h => fitv("steps", h.day))}], empty:noFit, title:"Steps"});
      chart("#cRhr", {type:"line", labels:L14, full:F14, series:[{name:"Resting HR", color:"var(--s1)", values:h14.map(h => fitv("restingHr", h.day))}], unit:" bpm", empty:noFit, title:"Resting HR"});
      chart("#cHrv", {type:"line", labels:L14, full:F14, series:[{name:"HRV", color:"var(--s1)", values:h14.map(h => fitv("hrv", h.day))}], unit:" ms", empty:noFit, title:"HRV"});
    }};
};

VIEWS.blood = () => {
  if (S.blood === null){ S.blood = []; api("/api/blood").then(r => { S.blood = r.reports; render(); }).catch(() => {}); }
  const rank = {high:0, low:0, borderline:1, normal:2}, lab = {high:"High", low:"Low", borderline:"Borderline", normal:"Normal"}, cls = {high:"b3", low:"b3", borderline:"b2", normal:"b1"};
  const doc = {none:["good","No doctor visit suggested by these numbers."], routine:["info","Mention at your next routine check-up."], soon:["warn","Book a doctor's appointment soon."], urgent:["crit","See a doctor promptly."]};
  return {html: `${needAI()}
    <div class="card"><h2>Analyse a blood report</h2>
      <div class="row"><div class="grow"><label>PDF or photo of the report (PDF up to about ${Math.round((S.status.maxUpload || 15e6)/1e6)} MB, photos are shrunk to fit)</label><input type="file" id="bfile" accept="application/pdf,image/*"></div>
        <button class="btn" data-act="blood" ${S.busy.blood || !S.status.hasGemini ? "disabled" : ""}>${S.busy.blood ? "Reading report…" : "Analyse"}</button></div>
      <p class="muted small" style="margin:0">Flags values outside the reference range printed on your report and explains them in plain English. It does not diagnose and can misread a scan. Decisions about your health belong with a doctor.</p></div>
    ${S.blood.map(r => { const x = r.result || {}, tests = [...(x.tests || [])].sort((a, b) => (rank[a.status] ?? 2) - (rank[b.status] ?? 2)), off = tests.filter(t => t.status && t.status !== "normal").length, dd = doc[x.see_doctor] || doc.routine;
      return `<div class="card"><h2>${esc(r.name)} <span class="muted small">· ${esc(x.report_date || r.day)}${x.lab ? " · " + esc(x.lab) : ""}</span><button class="x" style="float:right" data-delblood="${r.id}" title="Delete">✕</button></h2>
        <div class="note ${dd[0]}"><b>${dd[1]}</b> ${esc(x.doctor_reason || "")}</div>
        <p>${esc(x.summary || "")}</p><p class="muted small">${off} of ${tests.length} values outside range.</p>
        <div class="tw"><table><tr><th>Test</th><th>Value</th><th>Reference</th><th>Status</th><th>What it relates to</th></tr>${tests.map(t => `<tr><td>${esc(t.name)}</td><td style="white-space:nowrap">${esc(t.value)} ${esc(t.unit)}</td><td>${esc(t.ref_range)}${t.ref_source === "standard" ? ' <span class="muted small">(standard)</span>' : ""}</td><td><span class="b ${cls[t.status] || "b1"}" style="margin:0">${lab[t.status] || esc(t.status)}</span></td><td class="small">${esc(t.meaning || "")}</td></tr>`).join("")}</table></div>
        ${x.questions_for_doctor && x.questions_for_doctor.length ? `<h3>Questions to ask your doctor</h3><div class="small">${x.questions_for_doctor.map(esc).join("<br>")}</div>` : ""}</div>`; }).join("")}`};
};

VIEWS.mind = () => {
  if (S.chat === null){ S.chat = []; api(`/api/chat?day=${S.day}`).then(r => { S.chat = r.messages; render(); }).catch(() => {}); }
  const g = S.st.game, mood = S.st.mood ? S.st.mood.mood : null, moods = ["Rough","Low","Okay","Good","Great"];
  return {html: `${needAI()}
    <div class="tiles">
      ${tile("Bounce-back rate", g.bounce_rate != null ? g.bounce_rate + "%" : "–", g.slips ? `logged again the day after ${g.bounced} of ${g.slips} slips` : "no slips logged yet")}
      ${tile("Comebacks", g.comebacks, "times you returned after a gap or slip")}
      ${tile("Current streak", g.streak + (g.streak === 1 ? " day" : " days"), "streaks break. Comebacks are the skill.")}
    </div>
    <div class="grid">
      <div class="card"><h2>How are you today?</h2><div class="chips">${moods.map((m, i) => `<button class="chip ${mood === i+1 ? "on" : ""}" data-mood="${i+1}">${m}</button>`).join("")}</div>
        <h3>Had a slip?</h3>
        <div class="row"><div class="grow"><input id="slipnote" placeholder="What happened? (optional) e.g. stress-ate after a bad call"></div><button class="btn ghost" data-act="slip" ${S.busy.mind ? "disabled" : ""}>I slipped</button></div>
        <p class="muted small" style="margin:0">Logging a slip earns XP. Coming back the next day earns the comeback bonus. The app rewards returning, not being perfect.</p></div>
      <div class="card"><h2>Coach</h2>
        <div class="chat" id="chat">${S.chat.length ? S.chat.map(m => `<div class="msg ${m.role === "user" ? "user" : "coach"}">${rich(m.text)}</div>`).join("") : `<p class="muted small">Tell the coach what's going on. It knows your last 7 days of logs, and it will ask one question and give you one small next step.</p>`}${S.busy.mind ? '<div class="msg coach muted">…</div>' : ""}</div>
        <div class="row" style="margin:0"><div class="grow"><input id="mmsg" placeholder="Type here…" ${S.busy.mind ? "disabled" : ""}></div><button class="btn" data-act="mind" ${S.busy.mind || !S.status.hasGemini ? "disabled" : ""}>Send</button></div></div>
    </div>
    <p class="muted small">This coach is not a therapist and can't diagnose. If things feel heavy or this loop keeps repeating, a psychologist can help. In India, Tele-MANAS is free and open 24x7 on 14416.</p>`,
    after(){ const c = $("#chat"); if (c) c.scrollTop = c.scrollHeight; const m = $("#mmsg"); if (m) m.onkeydown = e => { if (e.key === "Enter") ACT.mind(); }; }};
};

VIEWS.week = () => {
  const h = lastN(7), s = S.st.settings, avg = a => { const v = a.filter(x => x != null); return v.length ? v.reduce((p, c) => p+c, 0)/v.length : null; };
  const workouts = h.filter(x => x.sets > 0).length, logged = h.filter(x => x.logged).length, foodDays = h.filter(x => x.foods > 0);
  const wk = h.filter(x => x.weight != null), w0 = wk.length > 1 ? wk[0].weight : null, w1 = wk.length > 1 ? wk[wk.length-1].weight : null;
  return {html: `
    <div class="tiles">
      ${tile("Days logged", `${logged} / 7`, "")}
      ${tile("Workouts", workouts, [...new Set(h.flatMap(x => x.splits))].length + " different splits")}
      ${tile("Avg calories", fmt(avg(foodDays.map(x => x.kcal))), `target ${fmt(s.kcal_target)}`)}
      ${tile("Avg protein", foodDays.length ? Math.round(avg(foodDays.map(x => x.protein))) + " g" : "–", `target ${fmt(s.protein_target)} g`)}
      ${tile("Avg sleep", fmtH(avg(h.map(x => { const sl = fitv("sleep", x.day); return sl ? sl.minutesAsleep : null; }))), "")}
      ${tile("Avg back pain", avg(h.map(x => x.pain)) != null ? avg(h.map(x => x.pain)).toFixed(1) + " / 10" : "–", "")}
      ${tile("Weight change", w0 != null && w1 != null ? (w1-w0 > 0 ? "+" : "") + (w1-w0).toFixed(1) + " kg" : "–", "")}
    </div>
    <div class="card"><h2>Week ending ${shortD(S.day)}</h2><div class="tw"><table>
      <tr><th>Day</th><th>Workout</th><th class="right">Eaten</th><th class="right">Burned</th><th class="right">Deficit</th><th class="right">Protein</th><th class="right">Water</th><th class="right">Sleep</th><th class="right">Steps</th><th class="right">Back pain</th><th class="right">Supps</th></tr>
      ${h.map(x => { const o = calOut(x.day), sl = fitv("sleep", x.day), df = o && x.foods ? o.v - x.kcal : null;
        return `<tr><td style="white-space:nowrap">${shortD(x.day)}${x.slips ? ' <span class="b b2" style="margin:0">slip</span>' : ""}${x.logged ? "" : ' <span class="muted small">no log</span>'}</td><td>${esc(x.splits.join(", ")) || (x.sets ? "Yes" : "–")}</td><td class="right">${x.foods ? fmt(x.kcal) : "–"}</td><td class="right">${o ? fmt(o.v) : "–"}</td><td class="right">${df != null ? (df < 0 ? "+" + fmt(-df) + " over" : fmt(df)) : "–"}</td><td class="right">${x.foods ? Math.round(x.protein) + " g" : "–"}</td><td class="right">${x.water_ml ? (x.water_ml/1000).toFixed(1) + " L" : "–"}</td><td class="right">${sl ? fmtH(sl.minutesAsleep) : "–"}</td><td class="right">${fmt(fitv("steps", x.day))}</td><td class="right">${x.pain ?? "–"}</td><td class="right">${x.supps || "–"}</td></tr>`; }).join("")}
    </table></div></div>
    <div class="card"><h2>Coach's weekly review</h2>${needAI()}${S.weekly ? `<div>${rich(S.weekly)}</div>` : `<p class="muted small">A short, honest review of this week: wins, what to watch, and one focus for next week.</p>`}
      <p style="margin:10px 0 0"><button class="btn" data-act="weekly" ${S.busy.weekly || !S.status.hasGemini ? "disabled" : ""}>${S.busy.weekly ? "Writing…" : S.weekly ? "Rewrite" : "Write my weekly review"}</button></p></div>`};
};

VIEWS.settings = () => {
  const s = S.st.settings, st = S.status, v = k => esc(s[k] ?? "");
  return {html: `
    <div class="card"><h2>About you</h2>
      <div class="row"><div><label>Name</label><input id="s_name" value="${v("name")}"></div>
        <div><label>Sex (for calorie estimate)</label><select id="s_sex"><option value="">Prefer not to say</option><option value="male" ${s.sex === "male" ? "selected" : ""}>Male</option><option value="female" ${s.sex === "female" ? "selected" : ""}>Female</option></select></div>
        <div><label>Age</label><input id="s_age" type="number" style="width:80px" value="${v("age")}"></div>
        <div><label>Height (cm)</label><input id="s_height_cm" type="number" style="width:100px" value="${v("height_cm")}"></div>
        <div><label>Goal weight (kg)</label><input id="s_goal_kg" type="number" step="0.1" style="width:110px" value="${v("goal_kg")}"></div></div>
      <div class="row"><div><label>Daily calories target</label><input id="s_kcal_target" type="number" style="width:120px" value="${v("kcal_target")}"></div>
        <div><label>Protein target (g)</label><input id="s_protein_target" type="number" style="width:110px" value="${v("protein_target")}"></div>
        <div><label>Water target (ml)</label><input id="s_water_target_ml" type="number" style="width:110px" value="${v("water_target_ml")}"></div>
        <div><label>Cardio per week (min)</label><input id="s_cardio_target_min" type="number" style="width:110px" value="${v("cardio_target_min")}"></div></div>
      <div class="row"><div class="grow"><label>Supplements to track (comma separated)</label><input id="s_supplements" value="${esc((s.supplements || []).join(", "))}"></div></div>
      <div class="row"><div class="grow"><label>Injuries and conditions (the AI coach reads this)</label><textarea id="s_conditions">${v("conditions")}</textarea></div></div>
      <button class="btn" data-act="savesettings">Save</button></div>
    <div class="card"><h2>AI coach (Gemini)</h2>
      <p class="small">${st.hasGemini ? "✓ A Gemini key is saved." : "Not set up yet."} Get a free key at <b>aistudio.google.com/apikey</b> → Create API key → paste it here.</p>
      ${st.remote ? '<p class="muted small">Keys can only be changed on your Mac.</p>' : `<div class="row"><div class="grow"><label>Gemini API key ${st.hasGemini ? "(leave blank to keep the saved one)" : ""}</label><input id="c_gemini_key" type="password" autocomplete="off" placeholder="${st.hasGemini ? "••••••••" : "Paste key"}"></div><button class="btn" data-act="saveconfig">Save key</button></div>`}
      <p class="muted small" style="margin:0">Privacy: food notes, blood reports and coach chats are sent to Google's Gemini to get an answer. On Gemini's free tier, Google may use that content to improve its products. Everything else stays ${st.hosted ? "in your own online storage, behind your passcode" : "on this Mac"}.</p></div>
    ${st.remote ? `<div class="card"><h2>Fitbit (Google Health)</h2><p class="small">${st.signedIn ? "✓ Connected." : "Not connected."} Fitbit sign-in and keys are managed on your Mac.</p>${st.signedIn ? '<button class="btn ghost" data-act="refit">Refresh Fitbit data</button>' : ""}</div>` : `<div class="card"><h2>Fitbit (Google Health)</h2>
      <p class="small">${st.signedIn ? "✓ Connected." : st.hasOAuth ? "Keys saved. Not signed in." : "Not set up yet."} In Google Cloud → Clients → your client, add this under Authorized redirect URIs: <b>${esc(st.redirectUri)}</b></p>
      ${st.hasOAuth ? "" : `<div class="row"><div class="grow"><label>Client ID</label><input id="c_client_id" autocomplete="off" placeholder="…apps.googleusercontent.com"></div><div class="grow"><label>Client secret</label><input id="c_client_secret" type="password" autocomplete="off" placeholder="GOCSPX-…"></div><button class="btn" data-act="saveconfig">Save</button></div>`}
      <div class="row" style="margin:0">${st.hasOAuth && !st.signedIn ? '<a class="btn" href="/login">Sign in with Google</a>' : ""}${st.signedIn ? '<button class="btn ghost" data-act="refit">Refresh Fitbit data</button><a class="btn ghost" href="/logout">Disconnect</a>' : ""}
        ${st.hasOAuth ? '<button class="btn ghost" data-act="rekey">Change keys</button>' : ""}</div>
      <p class="muted small" style="margin:8px 0 0">While your Google app is in "Testing", Google signs you out every 7 days. Just sign in again.</p></div>
    ${st.hosted ? `<div class="card"><h2>Passcode and phone</h2>
      <p class="small">✓ This app is online and locked with your passcode. On your iPhone, open this same address in Safari, enter the passcode, then tap Share → <b>Add to Home Screen</b> to get an app icon.</p>
      <div class="row"><div class="grow"><label>New passcode (8+ characters, signs out your other devices)</label><input id="c_phone" type="password" autocomplete="new-password"></div><button class="btn" data-act="savephone">Change</button></div>
      <div class="row" style="margin:0"><button class="btn ghost" data-act="check" ${S.busy.check ? "disabled" : ""}>${S.busy.check ? "Testing…" : "Test connections to Google"}</button></div>
      ${S.checks ? `<div class="small" style="margin-top:8px">${S.checks.map(c => `${c.ok ? "✓" : "✗"} <b>${esc(c.name)}</b> ${c.ok ? "reachable" : `blocked (${esc(c.host)}): ${esc(c.detail || "")}`}`).join("<br>")}</div>${S.checks.every(c => c.ok) ? "" : '<p class="small">Something is blocked by your web host. Send a screenshot of this.</p>'}` : ""}</div>` : `<div class="card"><h2>Use on your phone</h2>
      <p class="small">${!st.phoneEnabled ? "Off. Set a passcode to switch it on." : !st.phoneListening ? "<b>Passcode saved. Now restart the app:</b> in Terminal press Ctrl + C, then start it again the same way." : `✓ On. With your iPhone on the <b>same Wi-Fi as this Mac</b>, open Safari and go to: ${st.phoneUrls.map(u => `<b>${esc(u)}</b>`).join(" or ") || "this Mac's address, port 8080"}`}</p>
      <div class="row"><div class="grow"><label>${st.phoneEnabled ? "New passcode (signs your phone out)" : "Passcode for your phone (6+ characters)"}</label><input id="c_phone" type="password" autocomplete="new-password"></div><button class="btn" data-act="savephone">Save</button>${st.phoneEnabled ? '<button class="btn ghost" data-act="offphone">Turn off</button>' : ""}</div>
      <p class="muted small" style="margin:0">On the iPhone: enter the passcode, then tap Share → <b>Add to Home Screen</b> to get an app icon. The Mac must be on with this app running. Use this only on Wi-Fi you trust (home, or your own hotspot): on shared Wi-Fi the connection is not encrypted.</p></div>`}`}
    ${st.signedIn ? `<div class="card"><h2>Raw data explorer</h2><p class="muted small">See exactly what Google sends for any data type.</p>
      <div class="row"><select id="rawType">${["steps","sleep","heart-rate","daily-resting-heart-rate","heart-rate-variability","daily-heart-rate-variability","oxygen-saturation","daily-oxygen-saturation","daily-respiratory-rate","distance","active-minutes","active-zone-minutes","total-calories","exercise","daily-vo2-max","floors"].map(t => `<option>${t}</option>`).join("")}</select><button class="btn ghost" data-act="raw">Show</button></div><pre id="rawOut">Pick a type and press Show.</pre></div>` : ""}`};
};

/* ---------- actions ---------- */
function b64(buf){ const u = new Uint8Array(buf); let s = ""; for (let i = 0; i < u.length; i += 0x8000) s += String.fromCharCode.apply(null, u.subarray(i, i + 0x8000)); return btoa(s); }
async function fitUpload(file, max){  // photos are redrawn smaller until they fit the upload limit; PDFs are sent as they are
  if (!/^image\//.test(file.type) || file.size <= Math.min(max, 1.5e6)) return file;
  const url = URL.createObjectURL(file);
  try {
    const img = await new Promise((ok, no) => { const i = new Image(); i.onload = () => ok(i); i.onerror = () => no(new Error("Couldn't open that photo. Try a screenshot or a PDF.")); i.src = url; });
    for (const edge of [2400, 1800, 1300]){
      const k = Math.min(1, edge / Math.max(img.naturalWidth, img.naturalHeight)), c = document.createElement("canvas");
      c.width = Math.round(img.naturalWidth*k); c.height = Math.round(img.naturalHeight*k); c.getContext("2d").drawImage(img, 0, 0, c.width, c.height);
      const out = await new Promise(ok => c.toBlob(ok, "image/jpeg", 0.85));
      if (out && out.size <= max) return out;
    }
    return file;
  } finally { URL.revokeObjectURL(url); }
}
async function blobToWav(blob){  // browser recording -> 16 kHz mono WAV, a format Gemini accepts
  const AC = window.AudioContext || window.webkitAudioContext, ctx = new AC();
  const audio = await ctx.decodeAudioData(await blob.arrayBuffer()); ctx.close();
  const rate = 16000, off = new OfflineAudioContext(1, Math.max(1, Math.ceil(audio.duration*rate)), rate), src = off.createBufferSource();
  src.buffer = audio; src.connect(off.destination); src.start();
  const pcm = (await off.startRendering()).getChannelData(0), dv = new DataView(new ArrayBuffer(44 + pcm.length*2));
  const w = (o, t) => { for (let i = 0; i < t.length; i++) dv.setUint8(o+i, t.charCodeAt(i)); };
  w(0, "RIFF"); dv.setUint32(4, 36 + pcm.length*2, true); w(8, "WAVE"); w(12, "fmt "); dv.setUint32(16, 16, true); dv.setUint16(20, 1, true); dv.setUint16(22, 1, true);
  dv.setUint32(24, rate, true); dv.setUint32(28, rate*2, true); dv.setUint16(32, 2, true); dv.setUint16(34, 16, true); w(36, "data"); dv.setUint32(40, pcm.length*2, true);
  for (let i = 0; i < pcm.length; i++){ const x = Math.max(-1, Math.min(1, pcm[i])); dv.setInt16(44 + i*2, x < 0 ? x*0x8000 : x*0x7fff, true); }
  return b64(dv.buffer);
}
let rec = null;
async function aiFood(body){ await guard("food", async () => { const r = await api("/api/ai/food", {day:S.day, ...body}); toast(`Logged ${r.kcal} kcal`); await refresh(); }); }
const setGet = () => { const o = {}; for (const k of ["name","sex","conditions"]) o[k] = $("#s_" + k).value.trim();
  for (const k of ["age","height_cm","goal_kg","kcal_target","protein_target","water_target_ml","cardio_target_min"]) o[k] = num($("#s_" + k).value);
  o.supplements = $("#s_supplements").value.split(",").map(x => x.trim()).filter(Boolean); return o; };

const ACT = {
  async pain(){ await log("pain", {back:+$("#pb").value, neck:+$("#pn").value, note:$("#pnote").value.trim()}); toast("Pain check-in saved"); },
  async addset(){
    readForm(); const f = S.form, name = (f.exercise || "").trim(), e = exByName(name), split = S.split || S.st.next_split;
    if (!name) return toast("Pick an exercise first.");
    if (e && (e.group === "cardio" || e.group === "mobility")){ const m = num(f.minutes); if (!m) return toast("Enter minutes."); await log("set", {exercise:e.name, group:e.group, minutes:m, split}); }
    else { const w = num(f.weight) ?? 0, r = num(f.reps), s = num(f.sets) || 1; if (!r) return toast("Enter reps."); await log("set", {exercise:e ? e.name : name, group:e ? e.group : "custom", weight:w, reps:r, sets:s, split}); }
    S.form = {exercise:"", sets:3}; S.last = null; render();
  },
  plan(){ guard("plan", async () => { await api("/api/ai/workout", {day:S.day, split:S.split || S.st.next_split}); await refresh(); }); },
  foodtext(){ const t = $("#ftext").value.trim(); if (!t) return toast("Type what you ate first."); aiFood({text:t}); },
  async foodmanual(){ const n = $("#mname").value.trim(), k = num($("#mk").value); if (!n || k == null) return toast("Enter a name and calories."); await log("food", {name:n, kcal:k, protein:num($("#mp").value) || 0, source:"manual"}); },
  async rec(){
    const btn = $("#recbtn");
    if (rec){ rec.stop(); return; }
    let stream; try { stream = await navigator.mediaDevices.getUserMedia({audio:true}); } catch (e) { return toast("Microphone blocked. Allow it in the browser, or type instead."); }
    const chunks = []; rec = new MediaRecorder(stream);
    rec.ondataavailable = e => chunks.push(e.data);
    rec.onstop = async () => { stream.getTracks().forEach(t => t.stop()); const type = rec.mimeType; rec = null;
      try { const wav = await blobToWav(new Blob(chunks, {type})); await aiFood({audio_b64:wav, mime:"audio/wav"}); } catch (e) { toast("Couldn't read that recording. Try again or type it."); render(); } };
    rec.start(); btn.textContent = "Stop and log"; btn.classList.add("rec"); btn.classList.remove("ghost");
    const mine = rec, secs = Math.min(180, Math.floor((S.status.maxUpload || 15e6) / 34000));  // a voice note is about 32 KB per second
    setTimeout(() => { if (rec === mine) rec.stop(); }, secs * 1000);
  },
  async weight(){ const k = num($("#wkg").value); if (!k) return toast("Enter your weight."); await log("weight", {kg:k}); toast("Weight saved"); },
  blood(){ const f0 = $("#bfile").files[0], max = S.status.maxUpload || 15e6; if (!f0) return toast("Choose a PDF or photo first.");
    guard("blood", async () => { const f = await fitUpload(f0, max);
      if (f.size > max) throw new Error(`That file is over ${Math.round(max/1e6)} MB. Take clear photos of the pages and upload those instead.`);
      const r = await api("/api/ai/blood", {day:S.day, name:f0.name, mime:f.type || "application/pdf", file_b64:b64(await f.arrayBuffer())}); S.blood = [r, ...(S.blood || [])]; }); },
  mind(preset){ const el = $("#mmsg"), msg = typeof preset === "string" ? preset : el.value.trim(); if (!msg) return;
    S.chat = [...(S.chat || []), {role:"user", text:msg}];
    guard("mind", async () => { try { const r = await api("/api/ai/mind", {day:S.day, message:msg}); S.chat.push({role:"coach", text:r.reply}); } catch (e) { S.chat.pop(); throw e; } }); },
  async slip(){ const note = $("#slipnote").value.trim(); await log("slip", {note}); if (S.status.hasGemini) ACT.mind("I slipped today." + (note ? " " + note : "")); else toast("Slip logged. Tomorrow is a normal day."); },
  weekly(){ guard("weekly", async () => { S.weekly = (await api("/api/ai/weekly", {day:S.day})).text; }); },
  async savesettings(){ await api("/api/settings", {settings:setGet()}); toast("Saved"); await refresh(); },
  async saveconfig(){ const g = id => { const e = $(id); return e ? e.value.trim() : ""; };
    await api("/api/settings", {config:{gemini_key:g("#c_gemini_key"), client_id:g("#c_client_id"), client_secret:g("#c_client_secret")}}); S.status = await getStatus(); toast("Saved"); render(); },
  rekey(){ S.status = {...S.status, hasOAuth:false}; render(); },
  async check(){ S.busy.check = true; render(); try { S.checks = (await api("/api/check")).checks; } finally { S.busy.check = false; render(); } },
  async savephone(){ const c = $("#c_phone").value, least = S.status.hosted ? 8 : 6; if (c.length < least) return toast("Use at least " + least + " characters."); await api("/api/settings", {config:{phone_passcode:c}}); S.status = await getStatus(); toast("Passcode saved"); render(); },
  async offphone(){ await api("/api/settings", {config:{phone_passcode:""}}); S.status = await getStatus(); toast("Phone access is off"); render(); },
  async refit(){ toast("Refreshing…"); await loadFit(true); toast("Fitbit data refreshed"); },
  async raw(){ $("#rawOut").textContent = "Loading…"; const r = await fetch(`/api/raw?type=${$("#rawType").value}`); $("#rawOut").textContent = JSON.stringify(await r.json(), null, 2); },
};

document.addEventListener("click", async ev => {
  const t = ev.target.closest("[data-tab],[data-act],[data-water],[data-supp],[data-del],[data-delblood],[data-mood],[data-split],[data-pick],[data-use]");
  if (!t) return; const d = t.dataset;
  try {
    if (d.tab){ ev.preventDefault(); go(d.tab); }
    else if (d.act) await ACT[d.act]();
    else if (d.water) await log("water", {ml:+d.water});
    else if (d.supp){ if (d.id) await del(+d.id); else await log("supp", {name:d.supp}); }
    else if (d.del) await del(+d.del);
    else if (d.delblood){ await api("/api/delete", {id:+d.delblood}); S.blood = S.blood.filter(r => r.id !== +d.delblood); render(); }
    else if (d.mood) await log("mood", {mood:+d.mood});
    else if (d.split){ readForm(); S.split = d.split; render(); }
    else if (d.pick){ ev.preventDefault(); readForm(); await pickEx(d.pick); }
    else if (d.use){ const u = JSON.parse(d.use); readForm(); await pickEx(u.exercise, {sets:u.sets, reps:u.reps}); }
  } catch (e) { toast(e.message); }
});
function go(tab){ if (S.tab === "workout") readForm(); S.tab = VIEWS[tab] ? tab : "today"; history.replaceState(null, "", "#" + S.tab); render(); scrollTo(0, 0); }

(async function init(){
  try {
    S.status = await getStatus();
    const ex = await api("/api/exercises"); S.ex = ex.exercises; S.splits = ex.splits;
    S.day = S.status.today; const di = $("#day"); di.value = S.day; di.max = S.day;
    di.onchange = async () => { S.day = di.value || S.status.today; S.split = null; S.chat = null; S.weekly = null; S.form = {}; await refresh(); };
    const h = location.hash.slice(1); if (VIEWS[h]) S.tab = h;
    await refresh(); loadFit();
  } catch (e) { $("#view").innerHTML = `<p>Couldn't start: ${esc(e.message)}</p>`; }
})();
</script></body></html>
"""


def main():
    init_db()
    load_config()
    if _state["hosted"]:
        hosted_init()
    _state["lan"] = phone_enabled()  # listen on the local network only when a phone passcode is set
    server = ThreadingHTTPServer(("0.0.0.0" if _state["lan"] or _state["hosted"] else "127.0.0.1", PORT), Web)
    url = f"http://localhost:{PORT}"
    print(f"Fit Insights is running at {url}  (press Ctrl+C to stop)")
    if _state["lan"] and not _state["hosted"]:
        print("On your phone (same Wi-Fi), open: " + "  or  ".join(lan_urls()))
    if not os.environ.get("NO_BROWSER") and not _state["hosted"]:
        try:
            webbrowser.open(url)
        except Exception:
            pass
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nStopped.")


# ---------------------------------------------------------------- running online (WSGI)
class _Headers(dict):
    def get(self, key, default=None):
        return dict.get(self, key.lower(), default)


class _WSGIHandler(Web):
    """The same request handling as above, fed by a web host instead of Python's built-in server."""

    def __init__(self, environ):
        h = _Headers()
        for k, v in environ.items():
            if k.startswith("HTTP_"):
                h[k[5:].replace("_", "-").lower()] = v
        for k in ("CONTENT_TYPE", "CONTENT_LENGTH"):
            if environ.get(k):
                h[k.replace("_", "-").lower()] = environ[k]
        self.headers = h
        self.client_address = (environ.get("REMOTE_ADDR") or "", 0)
        self.rfile = environ["wsgi.input"]
        qs = environ.get("QUERY_STRING") or ""
        self.path = (environ.get("PATH_INFO") or "/") + ("?" + qs if qs else "")
        self.command = environ.get("REQUEST_METHOD", "GET")
        self.result = (500, [("Content-Type", "text/plain")], b"Server error")

    def send(self, code, body, ctype="text/html; charset=utf-8", headers=None):
        data = body.encode() if isinstance(body, str) else body
        self.result = (code, self.out_headers(ctype, len(data), headers), data)


NO_STORAGE_HTML = """<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1"><meta name="robots" content="noindex"><title>Fit Insights</title>
<style>body{font:16px/1.5 -apple-system,system-ui,sans-serif;background:#f4f4f2;color:#0b0b0b;max-width:560px;margin:8vh auto;padding:0 20px}
@media (prefers-color-scheme:dark){body{background:#111110;color:#f0efec}}li{margin:6px 0}code{background:#8882;padding:1px 5px;border-radius:5px}</style></head>
<body><h2>Almost there: @@TITLE@@</h2><p>@@WHY@@</p><ol>
<li>Open <b>vercel.com</b> and click this project.</li>
<li>Click the <b>Storage</b> tab, then <b>Create Database</b>, and choose <b>Neon</b> (Serverless Postgres).</li>
<li>Keep the suggested region and the <b>Free</b> plan, and click through <b>Continue</b> and <b>Create</b>.</li>
<li>When it asks, <b>connect</b> it to this project.</li>
<li>Click the <b>Deployments</b> tab, open the <b>&hellip;</b> menu on the top row, and click <b>Redeploy</b>.</li>
<li>Reload this page.</li></ol></body></html>"""


def application(environ, start_response):
    """Entry point for web hosts: Vercel (as api/index.py), PythonAnywhere, or any WSGI server."""
    problem = None
    if SERVERLESS and not DATABASE_URL:
        problem = ("connect a database", "Vercel can't keep files, so this app stores your log in a free database. "
                   "This project doesn't have one connected yet.")
    else:
        try:
            with _lock:
                if not _state["ready"]:
                    _state["hosted"] = True
                    hosted_init()
                    init_db()
                    load_config()
                    _state["ready"] = True
            if DATABASE_URL:
                load_config()
        except Exception as e:
            print("storage error:", repr(e))
            problem = ("the database isn't answering", "The app couldn't reach its database. Reload in a few seconds. "
                       "If this keeps showing, check that the database is still connected to this project:")
    if problem:
        page = NO_STORAGE_HTML.replace("@@TITLE@@", problem[0]).replace("@@WHY@@", problem[1]).encode()
        start_response("503 Service Unavailable", [("Content-Type", "text/html; charset=utf-8"),
                                                   ("Content-Length", str(len(page))), ("Cache-Control", "no-store")])
        return [page]
    h = _WSGIHandler(environ)
    try:
        if h.command in ("GET", "HEAD"):
            h.do_GET()
        elif h.command == "POST":
            h.do_POST()
        else:
            h.send(405, "Method not allowed", "text/plain")
    except Exception as e:
        h.send(500, json.dumps({"error": str(e)}), "application/json")
    code, headers, data = h.result
    start_response("%d %s" % (code, HTTPStatus(code).phrase), headers)
    return [b"" if h.command == "HEAD" else data]


app = application  # the name Vercel looks for


if __name__ == "__main__":
    main()
