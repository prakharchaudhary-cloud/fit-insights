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
ICON_PNG = base64.b64decode("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")
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


INDEX_HTML = r"""@@INDEX_HTML@@"""


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
