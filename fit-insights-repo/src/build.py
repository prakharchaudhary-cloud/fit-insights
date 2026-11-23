#!/usr/bin/env python3
"""Builds the single-file app from backend.py + frontend.html.

Writes api/index.py (the Vercel function, which also runs on your own computer with
`python3 api/index.py`)."""
import os
here = os.path.dirname(os.path.abspath(__file__))
server = open(os.path.join(here, "backend.py")).read()
html = open(os.path.join(here, "frontend.html")).read()
assert '"""' not in html and "@@INDEX_HTML@@" in server
out = os.path.join(here, "..", "api", "index.py")
open(out, "w").write(server.replace("@@INDEX_HTML@@", html))
local = os.path.join(here, "..", "app.py")  # an extra copy, only refreshed where one already exists
if os.path.exists(local):
    open(local, "w").write(server.replace("@@INDEX_HTML@@", html))
print("built api/index.py", len(server) + len(html), "bytes")
