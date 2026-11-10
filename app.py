#!/usr/bin/env python3
"""
PITCH GUESSER - guess a real MLB pitch from the first few seconds of its video.

Everything runs inside ONE app window. Pick your settings on the start screen:

  Difficulty
    All Star       full scouting report: pitch mix + previous 3 batters + current at-bat
    Hall of Fame   no pitcher tendencies: previous 3 batters + current at-bat
    Legend         only the current at-bat
  Format
    Classic        10 rounds
    Time Trial     as many rounds as you can before the clock runs out (the clock pauses while a round loads)
  Season           any year from 2021 on, or "All years" (random)

The mystery pitch is always a swing or a called strike. The strike zone is drawn from the
PITCHER'S view (from the mound). Hover a dot to see that pitch's details.

Scoring per round (max 100): pitch type 50 (20 for same family) + location up to 50
(0 at 1.25+ ft off, so be precise). After each guess you also see whether you out-guessed the batter.

Setup (Terminal):
    brew install ffmpeg
    pip3 install pandas requests pywebview
    python3 pitch_guesser.py

pywebview gives you a native Mac window. If it isn't installed the game opens as a
Chrome app-style window (or your default browser) instead.
Keys: 1-9 pick pitch type, click the zone, Enter locks in / next round, R replays the clip.
"""
import datetime as dt
import contextvars
import hashlib
import uuid
from http.cookies import SimpleCookie
import json
import math
import os
import random
import re
import shutil
import subprocess
import tempfile
import threading
import webbrowser
from collections import deque
from concurrent.futures import ThreadPoolExecutor
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

import pandas as pd
import requests

# ----------------------------- settings -----------------------------
ROUNDS = 10              # rounds in a Classic game
CLIP_SECONDS = 3.0       # how much of the pitch video you get to see
MIN_PITCHES_IN_GAME = 45 # pitcher must have thrown at least this many that day
LOC_ZERO_FT = 1.25       # location guess this far (feet) from the pitch = 0 location points
PREFETCH = 2             # rounds loaded in the background while you play
MIN_YEAR = 2021          # earliest season offered in this game
NO_VIDEO_LIMIT = 8       # give up on a season after this many pitches in a row with no video

_today = dt.date.today()
MAX_YEAR = _today.year if _today.month >= 4 else _today.year - 1
DEFAULT_YEAR = min(max(_today.year if _today.month >= 10 else _today.year - 1, MIN_YEAR), MAX_YEAR)
YEARS = list(range(MAX_YEAR, MIN_YEAR - 1, -1))
MODES = {"all_star": "All Star", "hof": "Hall of Fame", "legend": "Legend"}
NO_VIDEO = {}            # season -> consecutive pitches with no video found

CACHE = Path.home() / ".cache" / "pitch_guesser"
CACHE.mkdir(parents=True, exist_ok=True)
TMP = Path(tempfile.mkdtemp(prefix="pitchguess_"))
BEST_FILE = CACHE / "best_scores"  # per-browser files; storage is ephemeral unless a persistent disk is attached

SESSION = requests.Session()
SESSION.headers.update({
    "User-Agent": ("Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 "
                   "(KHTML, like Gecko) Chrome/124.0 Safari/537.36")
})

PITCH_NAMES = {
    "FF": "4-Seam", "FT": "2-Seam", "SI": "Sinker", "FC": "Cutter", "FA": "Fastball", "SL": "Slider",
    "ST": "Sweeper", "SV": "Slurve", "CU": "Curveball", "KC": "Knuckle-Curve",
    "CS": "Slow Curve", "CH": "Changeup", "FS": "Splitter", "FO": "Forkball",
    "SC": "Screwball", "KN": "Knuckleball", "EP": "Eephus",
}
FAMILY = {
    "FF": "fast", "FT": "fast", "SI": "fast", "FC": "fast", "FA": "fast",
    "SL": "break", "ST": "break", "SV": "break", "CU": "break", "KC": "break", "CS": "break",
    "CH": "off", "FS": "off", "FO": "off", "SC": "off",
}
COLORS = {
    "FF": "#e63946", "FT": "#ff7f50", "SI": "#f4a261", "FC": "#8d5a3b", "FA": "#c1121f", "SL": "#e9c46a",
    "ST": "#2a9d8f", "SV": "#84a98c", "CU": "#457b9d", "KC": "#1d3557", "CS": "#6d6875",
    "CH": "#52b788", "FS": "#9d4edd", "FO": "#b5179e", "SC": "#999999",
}
SKIP_TYPES = ["PO", "UN", "IN", "AB"]
# the mystery pitch must be a swing (any kind) or a called strike
SWING_OR_CALLED = {
    "called_strike", "swinging_strike", "swinging_strike_blocked", "foul", "foul_tip",
    "hit_into_play", "hit_into_play_score", "hit_into_play_no_out", "foul_bunt",
    "missed_bunt", "bunt_foul_tip",
}



# ----------------------------- data -----------------------------
def savant_csv(cache_name, extra, year):
    """Download a Statcast search CSV (cached on disk)."""
    path = CACHE / (cache_name + ".csv")
    if not path.exists():
        params = {
            "all": "true", "hfGT": "R|", "hfSea": "%d|" % year, "player_type": "pitcher",
            "type": "details", "min_pitches": "0", "min_results": "0", "min_pas": "0",
            "group_by": "name", "sort_col": "pitches", "sort_order": "desc",
        }
        params.update(extra)
        r = SESSION.get("https://baseballsavant.mlb.com/statcast_search/csv",
                        params=params, timeout=90)
        r.raise_for_status()
        path.write_text(r.text if r.text.strip() else "")
    if path.stat().st_size == 0:
        return pd.DataFrame()
    return pd.read_csv(path, low_memory=False)


def day_data(d):
    return savant_csv("day_%s" % d, {"game_date_gt": str(d), "game_date_lt": str(d)}, d.year)


def history(pitcher_id, d):
    """Pitcher's season-to-date pitches before the game day."""
    df = savant_csv("hist_%d_%s" % (pitcher_id, d), {
        "pitchers_lookup[]": str(pitcher_id),
        "game_date_gt": "%d-03-01" % d.year,
        "game_date_lt": str(d - dt.timedelta(days=1)),
    }, d.year)
    if df.empty:
        return df
    return df[~df.pitch_type.isin(SKIP_TYPES)].dropna(subset=["pitch_type"])


NAMES = {}


def load_names(ids):
    need = sorted({int(i) for i in ids if int(i) not in NAMES})
    if need:
        try:
            r = SESSION.get("https://statsapi.mlb.com/api/v1/people",
                            params={"personIds": ",".join(map(str, need))}, timeout=30)
            for p in r.json().get("people", []):
                NAMES[p["id"]] = p["fullName"]
        except Exception:
            pass
    for i in ids:
        NAMES.setdefault(int(i), "Player %d" % int(i))


GF_CACHE = {}


def get_clip(game_pk, pitcher, ab, pn):
    """Find the Film Room video for one pitch; return (full_path, short_path) or None."""
    game_pk = int(game_pk)
    if game_pk not in GF_CACHE:
        r = SESSION.get("https://baseballsavant.mlb.com/gf", params={"game_pk": game_pk}, timeout=30)
        GF_CACHE[game_pk] = r.json()
    gf = GF_CACHE[game_pk]
    play_id = None
    for side in ("team_home", "team_away"):
        for p in gf.get(side) or []:
            try:
                if (int(p["pitcher"]) == int(pitcher) and int(p["ab_number"]) == ab
                        and int(p["pitch_number"]) == pn):
                    play_id = p.get("play_id")
            except (KeyError, TypeError, ValueError):
                continue
    if not play_id:
        return None
    page = SESSION.get("https://baseballsavant.mlb.com/sporty-videos",
                       params={"playId": play_id}, timeout=30).text
    m = re.search(r'https?://[^\s"\'<>]+\.mp4', page)
    if not m:
        return None
    full = TMP / ("%s_full.mp4" % play_id)
    with SESSION.get(m.group(0), stream=True, timeout=90) as r:
        r.raise_for_status()
        with open(full, "wb") as f:
            for chunk in r.iter_content(1 << 16):
                f.write(chunk)
    short = TMP / ("%s_short.mp4" % play_id)
    subprocess.run(["ffmpeg", "-y", "-loglevel", "error", "-i", str(full), "-t", str(CLIP_SECONDS),
                    "-an", "-c:v", "libx264", "-preset", "veryfast", "-pix_fmt", "yuv420p", str(short)],
                   check=True)
    return full, short


def random_date(year):
    """A random regular-season day (skips the weeks where tendencies would be thin)."""
    if year == 2020:
        start, end = dt.date(2020, 8, 15), dt.date(2020, 9, 25)
    else:
        start, end = dt.date(year, 5, 1), dt.date(year, 9, 25)
    end = min(end, dt.date.today() - dt.timedelta(days=2))
    if end <= start:                      # season still in progress
        start = dt.date(year, 4, 10)
    end = max(end, start + dt.timedelta(days=1))
    return start + dt.timedelta(days=random.randint(0, (end - start).days))


def generic_options(year):
    """Pitch menu for modes that hide the pitcher's arsenal."""
    opts = ["FF", "SI", "FC", "SL", "CU", "KC", "CH", "FS"]
    if year >= 2023:
        opts.insert(4, "ST")      # sweeper
    if year < 2017:
        opts.insert(2, "FT")      # two-seamer label used in older seasons
    return opts


def build_round(mode, year):
    """Pick a random pitch and gather everything the chosen difficulty is allowed to show."""
    need_prev = mode != "legend"
    for _ in range(60):
        pool = [v for v in YEARS if NO_VIDEO.get(v, 0) < NO_VIDEO_LIMIT] or YEARS
        y = year or random.choice(pool)
        if NO_VIDEO.get(y, 0) >= NO_VIDEO_LIMIT:
            NO_VIDEO[y] = 0
            raise RuntimeError("No pitch videos turned up for %d (older seasons often don't have clips). "
                               "Try a different season." % y)
        d = random_date(y)
        try:
            day = day_data(d)
        except Exception:
            continue
        if day.empty or "pitch_type" not in day:
            continue
        day = day[~day.pitch_type.isin(SKIP_TYPES)].dropna(subset=["pitch_type"])
        counts = day.groupby(["game_pk", "pitcher"]).size()
        cands = counts[counts >= MIN_PITCHES_IN_GAME].index.tolist()
        random.shuffle(cands)
        for gk, pid in cands[:2]:
            g = day[(day.game_pk == gk) & (day.pitcher == pid)].sort_values(["at_bat_number", "pitch_number"])
            abs_ = list(g.at_bat_number.unique())
            if need_prev and len(abs_) < 4:
                continue
            elig = g[g.at_bat_number.isin(abs_[3:] if need_prev else abs_)]
            elig = elig.dropna(subset=["plate_x", "plate_z", "release_speed"])
            elig = elig[elig.description.isin(SWING_OR_CALLED)]
            if mode == "legend":
                elig = elig[elig.pitch_number >= 2]       # so there is at least one pitch of at-bat info
            if elig.empty:
                continue
            t = elig.sample(1).iloc[0]
            hist = None
            if mode == "all_star":
                try:
                    hist = history(int(pid), d)
                except Exception:
                    continue
                if len(hist) < 150:
                    continue
            try:
                clip = get_clip(gk, pid, int(t["at_bat_number"]), int(t["pitch_number"]))
            except ValueError:            # Savant answered with something that isn't a game feed
                clip = None
            except Exception:             # network hiccup, ffmpeg problem... don't blame the season
                continue
            if not clip:
                NO_VIDEO[y] = NO_VIDEO.get(y, 0) + 1
                continue
            NO_VIDEO[y] = 0
            prev = []
            if need_prev:
                idx = abs_.index(t["at_bat_number"])
                prev = [g[g.at_bat_number == a] for a in abs_[idx - 3:idx]]
            cur = g[(g.at_bat_number == t["at_bat_number"]) & (g.pitch_number < t["pitch_number"])]
            load_names([pid, t["batter"]] + [p.batter.iloc[0] for p in prev])
            if mode == "all_star":
                usage = hist.pitch_type.value_counts(normalize=True)
                options = [p for p in usage.index if usage[p] >= 0.02]
            else:
                options = generic_options(y)
            if t["pitch_type"] not in options:
                options.append(t["pitch_type"])
            return {"date": d, "year": y, "mode": mode, "target": t, "hist": hist, "prev": prev, "cur": cur,
                    "full": clip[0], "short": clip[1], "options": options, "pid": int(pid)}
    raise RuntimeError("Couldn't load a playable clip. Check your internet connection and try again.")


# ----------------------------- formatting -----------------------------
def pretty(s):
    return "-" if pd.isna(s) else str(s).replace("_", " ").title()


def loc_words(x, z, stand, top, bot):
    if pd.isna(x) or pd.isna(z):
        return "-"
    top = 3.4 if pd.isna(top) else top
    bot = 1.6 if pd.isna(bot) else bot
    if abs(x) < 0.28:
        h = "middle"
    else:
        h = "in" if ((x < 0) == (stand == "R")) else "away"
    frac = (z - bot) / (top - bot)
    v = "low" if frac < 0.33 else "high" if frac > 0.67 else "mid"
    in_zone = abs(x) <= 0.83 and bot - 0.12 <= z <= top + 0.12
    if h == "middle" and v == "mid":
        txt = "middle-middle"
    elif h == "middle":
        txt = v
    elif v == "mid":
        txt = h
    else:
        txt = "%s & %s" % (v, h)
    return txt + ("" if in_zone else " (off zone)")


def score_round(g_type, a_type, g_xy, a_xy):
    if g_type == a_type:
        t_pts = 50
    elif FAMILY.get(g_type) and FAMILY.get(g_type) == FAMILY.get(a_type):
        t_pts = 20
    else:
        t_pts = 0
    if g_xy is None:
        return t_pts, 0, None
    dist = math.hypot(g_xy[0] - a_xy[0], g_xy[1] - a_xy[1])
    return t_pts, max(0, round(50 * (1 - dist / LOC_ZERO_FT))), dist



HIT_EVENTS = {"single", "double", "triple", "home_run"}


def batter_read(t):
    """Infer how well the batter 'guessed' from what happened. Returns (level 0-2, sentence)."""
    desc, event = t["description"], t.get("events")
    name = PITCH_NAMES.get(t["pitch_type"], t["pitch_type"])
    fam = FAMILY.get(t["pitch_type"])
    ev = num(t.get("launch_speed"))
    evtxt = " (%.0f mph off the bat)" % ev if ev is not None else ""
    if desc == "called_strike":
        return 0, "The batter took it for a strike, caught looking at the %s." % name
    if desc in ("swinging_strike", "swinging_strike_blocked", "foul_tip", "missed_bunt"):
        if fam == "fast":
            return 0, "The batter swung through it, late on the %s, so he was probably sitting on something slower." % name
        return 0, "The batter swung through it, out in front of the %s, so he was probably sitting on something harder." % name
    if desc in ("foul", "foul_bunt", "bunt_foul_tip"):
        return 1, "The batter only fouled it off: a piece of the %s, but he didn't square it up." % name
    if event in HIT_EVENTS:
        return 2, "The batter got a hit%s, so he had the %s timed." % (evtxt, name)
    if ev is not None and ev >= 95:
        return 2, "The batter barreled it%s: it was an out, but he had the %s timed." % (evtxt, name)
    if ev is not None and ev < 80:
        return 0, "The batter made weak contact%s, not quite on time for the %s." % (evtxt, name)
    return 1, "The batter put it in play%s: decent timing on the %s, nothing special." % (evtxt, name)


def vs_batter(t, type_pts):
    """Compare the player's pitch-type read to the batter's outcome."""
    b_level, b_text = batter_read(t)
    p_level = 2 if type_pts == 50 else 1 if type_pts == 20 else 0
    if p_level > b_level:
        verdict, line = "better", "You out-guessed the batter!"
    elif p_level < b_level:
        verdict, line = "worse", "The batter out-guessed you."
    else:
        verdict = "even"
        line = {2: "You both had it timed.", 0: "You both got fooled."}.get(p_level, "About even with the batter.")
    return {"verdict": verdict, "text": b_text + " " + line}


# ----------------------------- game state -----------------------------
# Each browser receives its own game state. The original desktop build used one global
# GAME dictionary, which would let visitors overwrite one another on a public server.
_CURRENT_SESSION = contextvars.ContextVar("pitch_guesser_session", default="local")
_SESSION_STATES = {}
_SESSION_LOCKS = {}
_SESSION_REGISTRY_LOCK = threading.Lock()

def _fresh_game_state():
    return {"cfg": None, "round": 0, "total": 0, "log": [], "current": None,
            "payload": None, "answered": True, "queue": deque(), "executor": None}

class _SessionGameProxy:
    def _state(self):
        sid = _CURRENT_SESSION.get()
        with _SESSION_REGISTRY_LOCK:
            return _SESSION_STATES.setdefault(sid, _fresh_game_state())
    def __getitem__(self, key):
        return self._state()[key]
    def __setitem__(self, key, value):
        self._state()[key] = value
    def update(self, *args, **kwargs):
        self._state().update(*args, **kwargs)

class _SessionLock:
    def __enter__(self):
        sid = _CURRENT_SESSION.get()
        with _SESSION_REGISTRY_LOCK:
            self.lock = _SESSION_LOCKS.setdefault(sid, threading.RLock())
        self.lock.acquire()
        return self
    def __exit__(self, exc_type, exc, tb):
        self.lock.release()
        return False

GAME = _SessionGameProxy()
GAME_LOCK = _SessionLock()


def num(v):
    try:
        if v is None or pd.isna(v):
            return None
        return float(v)
    except Exception:
        return None


def pitch_dict(p, stand):
    nan = float("nan")
    return {"n": int(p.pitch_number), "balls": int(p.balls), "strikes": int(p.strikes),
            "pt": p.pitch_type, "name": PITCH_NAMES.get(p.pitch_type, p.pitch_type),
            "mph": num(p.release_speed),
            "loc": loc_words(p.plate_x, p.plate_z, stand, getattr(p, "sz_top", nan), getattr(p, "sz_bot", nan)),
            "x": num(p.plate_x), "z": num(p.plate_z), "result": pretty(p.description)}


def make_payload(r, rnd, limit):
    """Everything the page may show. Hidden sections are never sent, so they can't leak."""
    t, mode = r["target"], r["mode"]
    stand = t["stand"]
    balls, strikes = int(t["balls"]), int(t["strikes"])
    top_inn = t["inning_topbot"] == "Top"
    fld = t["home_team"] if top_inn else t["away_team"]
    bat = t["away_team"] if top_inn else t["home_team"]
    runners = [b for b, c in (("1B", "on_1b"), ("2B", "on_2b"), ("3B", "on_3b")) if pd.notna(t.get(c))]
    score = ""
    if pd.notna(t.get("bat_score")) and pd.notna(t.get("fld_score")):
        score = "%s %d, %s %d" % (bat, t["bat_score"], fld, t["fld_score"])
    top = num(t.get("sz_top")) or 3.4
    bot = num(t.get("sz_bot")) or 1.6

    tend, sample = [], None
    if mode == "all_star":
        hist = r["hist"]
        hs = hist[hist.stand == stand]
        cs = hist[(hist.balls == balls) & (hist.strikes == strikes)]
        sample = {"n": len(hist), "n_hand": len(hs), "n_count": len(cs)}
        for pt, grp in hist.groupby("pitch_type"):
            use = len(grp) / len(hist) * 100
            if use < 2:
                continue
            g2 = hs[hs.pitch_type == pt]
            tend.append({
                "pt": pt, "name": PITCH_NAMES.get(pt, pt), "use": use,
                "mph": num(grp.release_speed.mean()),
                "vs_hand": (hs.pitch_type == pt).mean() * 100 if len(hs) else None,
                "in_count": (cs.pitch_type == pt).mean() * 100 if len(cs) else None,
                "usual": loc_words(g2.plate_x.mean(), g2.plate_z.mean(), stand,
                                   g2.sz_top.mean(), g2.sz_bot.mean()) if len(g2) >= 10 else "-",
            })
        tend.sort(key=lambda d: -d["use"])

    prev = []
    for pa in r["prev"]:
        b_stand = pa.stand.iloc[0]
        prev.append({"batter": NAMES[int(pa.batter.iloc[0])], "stand": b_stand,
                     "result": pretty(pa.events.iloc[-1]),
                     "pitches": [pitch_dict(p, b_stand) for p in pa.itertuples()]})
    return {
        "round": rnd, "rounds": limit, "clip_seconds": CLIP_SECONDS,
        "mode": mode, "mode_label": MODES[mode], "year": r["year"],
        "header": {"pitcher": NAMES[r["pid"]], "p_hand": t["p_throws"], "fld": fld, "bat": bat,
                   "batter": NAMES[int(t["batter"])], "stand": stand, "inning": int(t["inning"]),
                   "topbot": t["inning_topbot"], "outs": int(t["outs_when_up"]), "runners": runners,
                   "balls": balls, "strikes": strikes, "score": score,
                   "pitch_number": int(t["pitch_number"])},
        "sample": sample, "tend": tend, "prev": prev,
        "cur": [pitch_dict(p, stand) for p in r["cur"].itertuples()],
        "options": [{"pt": o, "name": PITCH_NAMES.get(o, o)} for o in r["options"]],
        "zone": {"top": top, "bot": bot, "stand": stand},
        "clip": "/media/" + Path(r["short"]).name,
    }


def fill_queue():
    """Keep PREFETCH rounds loading in the background (call with GAME_LOCK held)."""
    cfg = GAME["cfg"]
    while len(GAME["queue"]) < PREFETCH and (cfg["limit"] is None or
                                             GAME["round"] + len(GAME["queue"]) < cfg["limit"]):
        GAME["queue"].append(GAME["executor"].submit(build_round, cfg["mode"], cfg["year"]))


def start_game(data):
    mode = data.get("mode") if data.get("mode") in MODES else "all_star"
    year = data.get("year")
    try:
        year = int(year) if year not in (None, "", "any") else None
    except (TypeError, ValueError):
        year = None
    if year is not None and year not in YEARS:
        year = DEFAULT_YEAR
    classic = data.get("format") != "time"
    try:
        minutes = min(max(int(data.get("minutes") or 5), 1), 30)
    except (TypeError, ValueError):
        minutes = 5
    cfg = {"mode": mode, "year": year, "format": "classic" if classic else "time",
           "minutes": minutes, "limit": ROUNDS if classic else None}
    with GAME_LOCK:
        for f in GAME["queue"]:
            f.cancel()
        if GAME["executor"] is not None:
            GAME["executor"].shutdown(wait=False)
        GAME.update(cfg=cfg, round=0, total=0, log=[], current=None, payload=None, answered=True,
                    queue=deque(), executor=ThreadPoolExecutor(max_workers=1))
        fill_queue()
    return {"ok": True}


def api_round():
    with GAME_LOCK:
        if GAME["cfg"] is None:
            return {"error": "Pick your settings first."}
        if GAME["payload"] is not None and not GAME["answered"]:
            return GAME["payload"]
        limit = GAME["cfg"]["limit"]
        if limit is not None and GAME["round"] >= limit:
            return {"error": "Game over - start a new game."}
        fill_queue()
        ex, fut = GAME["executor"], GAME["queue"].popleft()
    try:
        r = fut.result()
    except Exception as e:
        with GAME_LOCK:
            if GAME["executor"] is ex:
                fill_queue()
        return {"error": str(e) or "Couldn't load a round."}
    with GAME_LOCK:
        if GAME["executor"] is not ex:
            return {"error": "That game was reset."}
        GAME["round"] += 1
        GAME["current"], GAME["answered"] = r, False
        GAME["payload"] = make_payload(r, GAME["round"], limit)
        fill_queue()
        return GAME["payload"]


def api_guess(data):
    with GAME_LOCK:
        if GAME["current"] is None or GAME["answered"]:
            return {"error": "No round in progress."}
        GAME["answered"] = True
        r = GAME["current"]
        limit = GAME["cfg"]["limit"]
    t = r["target"]
    stand = t["stand"]
    top = num(t.get("sz_top")) or 3.4
    bot = num(t.get("sz_bot")) or 1.6
    g_type = data.get("type")
    gx, gz = data.get("x"), data.get("z")
    g_xy = (float(gx), float(gz)) if gx is not None and gz is not None else None
    actual = (float(t["plate_x"]), float(t["plate_z"]))
    t_pts, l_pts, dist = score_round(g_type, t["pitch_type"], g_xy, actual)
    pts = t_pts + l_pts
    with GAME_LOCK:
        GAME["total"] += pts
        name = PITCH_NAMES.get(t["pitch_type"], t["pitch_type"])
        GAME["log"].append({"round": GAME["round"], "name": name, "type_pts": t_pts,
                            "loc_pts": l_pts, "pts": pts})
        total, done = GAME["total"], limit is not None and GAME["round"] >= limit
    return {
        "pt": t["pitch_type"], "name": name, "mph": num(t["release_speed"]),
        "loc": loc_words(actual[0], actual[1], stand, top, bot),
        "result": pretty(t["description"]),
        "event": None if pd.isna(t["events"]) else pretty(t["events"]),
        "type_pts": t_pts, "loc_pts": l_pts, "dist": dist, "pts": pts, "total": total,
        "type_note": "exact" if t_pts == 50 else "same family" if t_pts else "miss",
        "vs_batter": vs_batter(t, t_pts),
        "guess_name": PITCH_NAMES.get(g_type, g_type),
        "x": actual[0], "z": actual[1], "done": done,
        "full": "/media/" + Path(r["full"]).name,
    }


def api_final():
    cfg = GAME["cfg"] or {}
    key = "%s|%s" % (cfg.get("mode"), "classic" if cfg.get("limit") else "time%s" % cfg.get("minutes"))
    sid = _CURRENT_SESSION.get()
    safe_sid = hashlib.sha256(sid.encode()).hexdigest()[:24]
    best_path = BEST_FILE / (safe_sid + ".json")
    try:
        data = json.loads(best_path.read_text()) if best_path.exists() else {}
        if not isinstance(data, dict):
            data = {}
    except Exception:
        data = {}
    best = data.get(key, 0)
    total = GAME["total"]
    new_best = total > best
    if new_best:
        data[key] = total
        try:
            BEST_FILE.mkdir(parents=True, exist_ok=True)
            best_path.write_text(json.dumps(data))
        except Exception:
            pass
    limit = cfg.get("limit")
    return {"total": total, "max": limit * 100 if limit else None, "log": GAME["log"],
            "rounds_played": len(GAME["log"]), "best": max(best, total), "new_best": new_best}


def _json_default(o):
    try:
        return o.item()
    except Exception:
        return str(o)


# ----------------------------- web server -----------------------------
class Handler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"

    def log_message(self, *args):
        pass

    def _bind_session(self):
        cookie = SimpleCookie()
        try:
            cookie.load(self.headers.get("Cookie", ""))
        except Exception:
            pass
        morsel = cookie.get("pg_session")
        sid = morsel.value if morsel and re.fullmatch(r"[a-f0-9]{32}", morsel.value) else None
        self._new_session = sid is None
        self.session_id = sid or uuid.uuid4().hex
        _CURRENT_SESSION.set(self.session_id)

    def _send(self, body, ctype, status=200):
        self.send_response(status)
        self.send_header("Content-Type", ctype)
        if getattr(self, "_new_session", False):
            secure = "; Secure" if self.headers.get("X-Forwarded-Proto", "").lower() == "https" else ""
            self.send_header("Set-Cookie", "pg_session=%s; HttpOnly; SameSite=Lax; Path=/; Max-Age=2592000%s" % (self.session_id, secure))
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)

    def _json(self, obj, status=200):
        self._send(json.dumps(obj, default=_json_default).encode(), "application/json", status)

    def _media(self, name):
        path = TMP / Path(name).name
        if not path.exists():
            self.send_error(404)
            return
        size = path.stat().st_size
        start, end, status = 0, size - 1, 200
        m = re.match(r"bytes=(\d*)-(\d*)$", self.headers.get("Range") or "")
        if m and (m.group(1) or m.group(2)):
            if m.group(1):
                start = int(m.group(1))
                end = int(m.group(2)) if m.group(2) else size - 1
            else:
                start = max(size - int(m.group(2)), 0)
            end = min(end, size - 1)
            status = 206
        length = max(end - start + 1, 0)
        self.send_response(status)
        self.send_header("Content-Type", "video/mp4")
        self.send_header("Accept-Ranges", "bytes")
        self.send_header("Content-Length", str(length))
        if status == 206:
            self.send_header("Content-Range", "bytes %d-%d/%d" % (start, end, size))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        with open(path, "rb") as f:
            f.seek(start)
            left = length
            while left > 0:
                chunk = f.read(min(65536, left))
                if not chunk:
                    break
                self.wfile.write(chunk)
                left -= len(chunk)

    def do_GET(self):
        self._bind_session()
        path = self.path.split("?")[0]
        try:
            if path == "/":
                self._send(PAGE.replace("__COLORS__", json.dumps(COLORS)).encode(), "text/html; charset=utf-8")
            elif path == "/api/config":
                self._json({"years": YEARS, "default_year": DEFAULT_YEAR, "rounds": ROUNDS})
            elif path == "/api/round":
                self._json(api_round())
            elif path == "/api/final":
                self._json(api_final())
            elif path.startswith("/media/"):
                self._media(path[len("/media/"):])
            else:
                self.send_error(404)
        except (BrokenPipeError, ConnectionResetError):
            pass
        except Exception as e:
            try:
                self._json({"error": str(e)}, 500)
            except Exception:
                pass

    def do_POST(self):
        self._bind_session()
        try:
            n = int(self.headers.get("Content-Length") or 0)
            data = json.loads(self.rfile.read(n) or b"{}")
            if self.path == "/api/start":
                self._json(start_game(data))
            elif self.path == "/api/guess":
                self._json(api_guess(data))
            else:
                self.send_error(404)
        except (BrokenPipeError, ConnectionResetError):
            pass
        except Exception as e:
            try:
                self._json({"error": str(e)}, 500)
            except Exception:
                pass


PAGE = r"""<!doctype html>
<html><head><meta charset="utf-8"><title>Pitch Guesser</title>
<meta name="viewport" content="width=device-width, initial-scale=1">
<style>
*{box-sizing:border-box}
html,body{height:100%;margin:0}
body{background:#0b1220;color:#e5e7eb;font:14px/1.4 -apple-system,BlinkMacSystemFont,"SF Pro Text","Helvetica Neue",Arial,sans-serif}
#top{height:52px;display:flex;align-items:center;gap:20px;padding:0 18px;background:#111a2e;border-bottom:1px solid #1f2a44}
.brand{font-weight:700;font-size:17px}
#roundlabel{font-weight:600}
#modelabel{color:#94a3b8;font-size:13px}
#timer{font-weight:700;font-variant-numeric:tabular-nums;color:#38bdf8;font-size:17px}
#timer.low{color:#f87171}
#score{margin-left:auto;color:#facc15;font-weight:700;font-size:16px}
button{font:inherit;cursor:pointer;border:1px solid #334155;background:#1e293b;color:#e5e7eb;padding:8px 12px;border-radius:8px}
button:hover:not(:disabled){background:#334155}
button:disabled{opacity:.45;cursor:default}
button.primary{background:#2563eb;border-color:#2563eb;color:#fff;font-weight:600;width:100%}
button.primary:hover:not(:disabled){background:#1d4ed8}
select{font:inherit;background:#1e293b;color:#e5e7eb;border:1px solid #334155;border-radius:8px;padding:7px 10px}
#main{display:grid;grid-template-columns:minmax(460px,1fr) minmax(540px,640px);gap:14px;padding:14px;height:calc(100% - 52px)}
#left,#right{overflow-y:auto;min-height:0;padding-right:2px}
.card{background:#111a2e;border:1px solid #1f2a44;border-radius:12px;padding:12px 14px;margin-bottom:12px}
.card h2{margin:0 0 8px;font-size:12px;letter-spacing:.07em;text-transform:uppercase;color:#94a3b8}
.big{font-size:16px;font-weight:600;margin-bottom:4px}
table{border-collapse:collapse;width:100%;font-size:12.5px;margin-top:6px}
th{text-align:left;color:#94a3b8;font-weight:600;padding:3px 6px;border-bottom:1px solid #1f2a44}
td{padding:3px 6px;border-bottom:1px solid #16213a}
.dot{display:inline-block;width:10px;height:10px;border-radius:50%;margin-right:6px;vertical-align:middle}
.muted{color:#64748b}
.sub{margin:10px 0 0;font-weight:600}
#vid{width:100%;max-height:27vh;background:#000;border-radius:8px;display:block}
.vrow{display:flex;align-items:center;gap:12px;margin-top:8px}
#guessrow{display:flex;gap:12px;align-items:flex-start}
#zone{width:min(43vh,520px);height:min(43vh,520px);border-radius:12px;border:1px solid #1f2a44;display:block;cursor:crosshair}
.cap{font-size:11.5px;margin-top:4px;max-width:min(43vh,520px)}
#side{flex:1;min-width:190px}
#side h2{margin:0 0 8px;font-size:12px;letter-spacing:.07em;text-transform:uppercase;color:#94a3b8}
.tbtn{display:flex;width:100%;align-items:center;margin-bottom:5px;padding:6px 10px;text-align:left}
.tbtn kbd{margin-left:auto;color:#64748b;font:11px monospace}
.tbtn.sel{border-color:#38bdf8;background:#0c4a6e}
.tbtn.right{border-color:#22c55e;background:#14532d}
.tbtn.wrong{border-color:#ef4444;background:#7f1d1d}
#lock{margin-top:6px}
#result{margin-top:12px;font-size:13px}
#result .ans{font-size:15px;font-weight:700}
.vs{margin-top:10px;padding:8px 10px;border-radius:8px;border:1px solid;font-size:12.5px;line-height:1.45}
.vs b{margin-right:4px}
.vs.better{border-color:#22c55e;background:#0f2a1a}
.vs.worse{border-color:#ef4444;background:#2a1212}
.vs.even{border-color:#eab308;background:#2a2410}
.gold{color:#facc15}
.good{color:#4ade80}
#overlay{display:none;position:fixed;inset:0;background:rgba(2,6,23,.92);align-items:center;justify-content:center;z-index:10}
#overlaybox{background:#111a2e;border:1px solid #334155;border-radius:14px;padding:26px 32px;max-width:780px;max-height:92vh;overflow:auto;text-align:center}
.menu{text-align:left;min-width:min(640px,86vw)}
.menu h1{margin:0 0 4px;font-size:24px}
.sec{margin:18px 0 6px;font-size:12px;letter-spacing:.07em;text-transform:uppercase;color:#94a3b8}
.opts{display:flex;gap:8px}
.opt{flex:1;text-align:left;display:flex;flex-direction:column;gap:4px;padding:10px 12px}
.opt span{font-size:12px;color:#94a3b8;line-height:1.35}
.opt.sel{border-color:#38bdf8;background:#0c4a6e}
.row{display:flex;align-items:center;gap:10px;margin-top:8px;flex-wrap:wrap}
.bigscore{font-size:42px;font-weight:800;color:#facc15;margin:6px 0}
.scroll{max-height:36vh;overflow:auto;margin:8px 0;text-align:left}
.btns{display:flex;gap:10px;margin-top:14px}
.spin{width:36px;height:36px;border:4px solid #334155;border-top-color:#38bdf8;border-radius:50%;margin:0 auto 14px;animation:sp 1s linear infinite}
@keyframes sp{to{transform:rotate(360deg)}}
@media (max-width:1100px){#main{grid-template-columns:1fr;height:auto}#left,#right{overflow:visible}}
</style></head>
<body>
<div id="top">
  <div class="brand">&#9918; Pitch Guesser</div>
  <div id="roundlabel"></div>
  <div id="modelabel"></div>
  <div id="timer" style="display:none"></div>
  <div id="score">Score 0</div>
  <button id="menubtn">Menu</button>
</div>
<div id="main">
  <div id="left"></div>
  <div id="right">
    <div class="card">
      <video id="vid" muted playsinline></video>
      <div class="vrow"><button id="replay">&#8635; Replay clip (R)</button><span id="vlabel" class="muted"></span></div>
      <div id="vsbox"></div>
    </div>
    <div id="guessrow">
      <div>
        <svg id="zone" viewBox="0 0 600 600"></svg>
        <div class="cap muted" id="cap"></div>
      </div>
      <div id="side">
        <h2>Pitch type</h2>
        <div id="types"></div>
        <button id="lock" class="primary" disabled>Lock in guess</button>
        <div id="result"></div>
      </div>
    </div>
  </div>
</div>
<div id="overlay"><div id="overlaybox"></div></div>
<script>
const COLORS = __COLORS__;
const $ = id => document.getElementById(id);
const esc = s => String(s).replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const S = 100, X0 = -3, Z1 = 5.5;                       // 100 px per foot; picture spans 6 ft wide x 6 ft tall
// PITCHER'S VIEW: Statcast's plate_x is measured from the catcher's side, so the picture mirrors it (screen x = -plate_x).
const sx = x => (-x - X0) * S, sz = z => (Z1 - z) * S;
const clx = x => Math.min(Math.max(x, X0 + 0.1), -X0 - 0.1), clz = z => Math.min(Math.max(z, -0.4), 5.4);
const pct = v => v == null ? '-' : v.toFixed(1) + '%';
const f1 = v => v == null ? '-' : v.toFixed(1);
const dot = pt => `<span class="dot" style="background:${COLORS[pt] || '#94a3b8'}"></span>`;
const MODE_LABEL = {all_star: 'All Star', hof: 'Hall of Fame', legend: 'Legend'};
let CFG = {years: [], default_year: null, rounds: 10};
let menu = {mode: 'all_star', format: 'classic', minutes: 5, year: ''};
let cfg = null, gameId = 0, ended = false;
let R = null, picked = null, guess = null, phase = 'guess', last = null;
const tt = {left: 0, running: false, last: performance.now(), up: false};

async function api(path, body) {
  const opt = body === undefined ? {} : {method: 'POST', headers: {'Content-Type': 'application/json'}, body: JSON.stringify(body)};
  return (await fetch(path, opt)).json();
}
function overlay(html) { $('overlaybox').innerHTML = html; $('overlay').style.display = 'flex'; }
function hideOverlay() { $('overlay').style.display = 'none'; }
const overlayOpen = () => $('overlay').style.display === 'flex';
const spinner = msg => `<div class="spin"></div><p>${msg}</p>`;

// ---------- clock (Time Trial) ----------
function showTimer() {
  const s = Math.ceil(tt.left / 1000);
  $('timer').innerHTML = '&#9201; ' + Math.floor(s / 60) + ':' + String(s % 60).padStart(2, '0');
  $('timer').classList.toggle('low', s <= 30);
}
setInterval(() => {
  const now = performance.now();
  if (tt.running) {
    tt.left -= now - tt.last;
    if (tt.left <= 0) { tt.left = 0; tt.running = false; timeUp(); }
    showTimer();
  }
  tt.last = now;
}, 200);
function timeUp() {
  tt.up = true;
  if (phase === 'busy') return;          // a guess is already on its way: lock() shows the final when it lands
  showFinal();                           // an unlocked round is forfeited
}

// ---------- start screen ----------
function showMenu() {
  gameId++; tt.running = false;
  const opt = (grp, v, title, desc) =>
    `<button class="opt ${menu[grp] === v ? 'sel' : ''}" data-grp="${grp}" data-v="${v}"><b>${title}</b><span>${desc}</span></button>`;
  overlay(`<div class="menu"><h1>&#9918; Pitch Guesser</h1>
    <div class="muted">Guess the pitch type and location from a few seconds of real MLB video.</div>
    <div class="sec">Difficulty</div><div class="opts">` +
      opt('mode', 'all_star', 'All Star', 'Full scouting report: pitch mix, previous 3 batters, and the current at-bat.') +
      opt('mode', 'hof', 'Hall of Fame', 'No pitcher tendencies. You get the previous 3 batters and the current at-bat.') +
      opt('mode', 'legend', 'Legend', 'Only the current at-bat. Everything else is on you.') +
    `</div><div class="sec">Format</div><div class="opts">` +
      opt('format', 'classic', 'Classic', `${CFG.rounds} rounds, up to 100 points each.`) +
      opt('format', 'time', 'Time Trial', 'Score as many rounds as you can before the clock runs out.') +
    `</div><div class="row" id="minrow" style="display:${menu.format === 'time' ? 'flex' : 'none'}">Time limit
      <select id="m-min">` + [2, 3, 5, 10].map(v => `<option value="${v}" ${+menu.minutes === v ? 'selected' : ''}>${v} minutes</option>`).join('') +
    `</select><span class="muted">The clock pauses while a round loads.</span></div>
    <div class="sec">Season</div><div class="row"><select id="m-year"><option value="">All years (random)</option>` +
      CFG.years.map(y => `<option value="${y}" ${String(menu.year) === String(y) ? 'selected' : ''}>${y}</option>`).join('') +
    `</select><span class="muted">Not every season has pitch video; the game will tell you if one doesn't.</span></div>
    <p><button class="primary" id="startbtn">Start game</button></p></div>`);
  document.querySelectorAll('.opt').forEach(b => b.onclick = () => {
    menu[b.dataset.grp] = b.dataset.v;
    document.querySelectorAll(`.opt[data-grp="${b.dataset.grp}"]`).forEach(x => x.classList.toggle('sel', x === b));
    $('minrow').style.display = menu.format === 'time' ? 'flex' : 'none';
  });
  $('m-min').onchange = e => menu.minutes = +e.target.value;
  $('m-year').onchange = e => menu.year = e.target.value;
  $('startbtn').onclick = startGame;
}

async function startGame() {
  cfg = {mode: menu.mode, format: menu.format, minutes: +menu.minutes, year: menu.year ? +menu.year : null};
  gameId++; ended = false; R = null; picked = null; guess = null; last = null;
  tt.left = cfg.minutes * 60000; tt.up = false; tt.running = false;
  $('score').textContent = 'Score 0';
  $('roundlabel').textContent = '';
  $('modelabel').textContent = `${MODE_LABEL[cfg.mode]} \u00b7 ${cfg.year || 'All years'} \u00b7 ${cfg.format === 'time' ? 'Time Trial' : 'Classic'}`;
  $('timer').style.display = cfg.format === 'time' ? '' : 'none';
  if (cfg.format === 'time') showTimer();
  overlay(spinner('Starting...'));
  await api('/api/start', cfg);
  await loadRound();
}

async function loadRound() {
  const gid = gameId;
  tt.running = false;
  overlay(spinner('Finding a game and loading the clip...<br><span class="muted">(the first round takes the longest' +
    (cfg.format === 'time' ? '; your clock is paused' : '') + ')</span>'));
  let d;
  try { d = await api('/api/round'); } catch (e) { d = {error: String(e)}; }
  if (gid !== gameId) return;                       // the player went back to the menu meanwhile
  if (d.error) {
    overlay(`<p>${esc(d.error)}</p><div class="btns"><button class="primary" onclick="loadRound()">Try again</button><button onclick="showMenu()">Back to menu</button></div>`);
    return;
  }
  R = d; picked = null; guess = null; phase = 'guess'; last = null;
  render(); hideOverlay();
  tt.running = cfg.format === 'time' && !tt.up;
}

// ---------- round screen ----------
function pitchTable(rows) {
  if (!rows.length) return '<p class="muted">First pitch of the at-bat.</p>';
  return '<table><tr><th>#</th><th>Cnt</th><th>Pitch</th><th>MPH</th><th>Location</th><th>Result</th></tr>' +
    rows.map(p => `<tr><td>${p.n}</td><td>${p.balls}-${p.strikes}</td><td>${dot(p.pt)}${esc(p.name)}</td><td>${f1(p.mph)}</td>` +
      `<td>${esc(p.loc)} <span class="muted">${p.x == null ? '' : '(' + (-p.x).toFixed(1) + ', ' + p.z.toFixed(1) + ')'}</span></td><td>${esc(p.result)}</td></tr>`).join('') + '</table>';
}

function render() {
  const h = R.header;
  $('roundlabel').textContent = R.rounds ? `Round ${R.round} / ${R.rounds}` : `Round ${R.round}`;
  let L = `<div class="card"><h2>Situation &middot; ${esc(R.mode_label)} &middot; ${R.year}</h2>
    <div class="big">${esc(h.pitcher)} <span class="muted">(${h.p_hand}HP, ${esc(h.fld)})</span> vs ${esc(h.batter)} <span class="muted">(${h.stand}HB, ${esc(h.bat)})</span></div>
    <div>${h.topbot} ${h.inning} &middot; ${h.outs} out &middot; runners: ${h.runners.length ? h.runners.join(', ') : 'none'} &middot; count <b>${h.balls}-${h.strikes}</b>${h.score ? ' &middot; ' + esc(h.score) : ''}</div>
    <div class="muted">Mystery pitch = pitch #${h.pitch_number} of this at-bat (a swing or a called strike)</div></div>`;
  if (R.mode === 'all_star') {
    L += `<div class="card"><h2>Scouting report - season to date</h2>
      <div class="muted">${R.sample.n} pitches &middot; vs ${h.stand}HB: ${R.sample.n_hand} &middot; in ${h.balls}-${h.strikes} counts: ${R.sample.n_count}</div>
      <table><tr><th>Pitch</th><th>Use</th><th>MPH</th><th>vs ${h.stand}HB</th><th>${h.balls}-${h.strikes} cnt</th><th>Usual spot vs ${h.stand}HB</th></tr>` +
      R.tend.map(t => `<tr><td>${dot(t.pt)}${esc(t.name)}</td><td>${pct(t.use)}</td><td>${f1(t.mph)}</td><td>${pct(t.vs_hand)}</td><td>${pct(t.in_count)}</td><td>${esc(t.usual)}</td></tr>`).join('') +
      '</table></div>';
  }
  if (R.prev.length) {
    L += '<div class="card"><h2>Previous 3 batters</h2><div class="muted">In/away is relative to the batter. (x, z) in feet; x is as seen from the pitcher\'s view.</div>' +
      R.prev.map((b, i) => `<div class="sub">${i + 1}. ${esc(b.batter)} <span class="muted">(${b.stand}HB)</span> &rarr; ${esc(b.result)}</div>` + pitchTable(b.pitches)).join('') + '</div>';
  }
  L += `<div class="card"><h2>Current at-bat vs ${esc(h.batter)} so far</h2>${pitchTable(R.cur)}</div>`;
  $('left').innerHTML = L; $('left').scrollTop = 0;

  $('types').innerHTML = R.options.map((o, i) =>
    `<button class="tbtn" data-pt="${o.pt}" onclick="pick('${o.pt}')">${dot(o.pt)}${esc(o.name)}<kbd>${i < 9 ? i + 1 : ''}</kbd></button>`).join('');
  $('result').innerHTML = ''; $('vsbox').innerHTML = '';
  $('cap').textContent = "Pitcher's view (from the mound). " + (R.prev.length ? 'Small dots = previous 3 batters, ' : '') +
    'numbered = this at-bat. Hover a dot for details. Click to place your guess.';
  drawZone(); updateLock();
  const v = $('vid'); v.controls = false; v.muted = true; v.src = R.clip; v.play().catch(() => {});
  $('vlabel').textContent = `First ${R.clip_seconds} seconds of the pitch`;
}

function drawZone() {
  const z = R.zone, zl = -0.708, zr = 0.708, inX = z.stand === 'R' ? -2.2 : 2.2;   // plate_x on the batter's (inside) side
  let s = '<rect width="600" height="600" fill="#0f172a"/>';
  for (let ft = -2; ft <= 2; ft++) s += `<line x1="${sx(ft)}" y1="0" x2="${sx(ft)}" y2="600" stroke="#1f2a44"/><text x="${sx(ft)}" y="594" fill="#64748b" font-size="12" text-anchor="middle">${Math.abs(ft)}</text>`;
  for (let ft = 0; ft <= 5; ft++) s += `<line x1="0" y1="${sz(ft)}" x2="600" y2="${sz(ft)}" stroke="#1f2a44"/><text x="6" y="${sz(ft) - 4}" fill="#64748b" font-size="12">${ft} ft</text>`;
  s += `<text x="${sx(inX)}" y="572" fill="#64748b" font-size="13" font-style="italic" text-anchor="middle">inside</text>`;
  s += `<text x="${sx(-inX)}" y="572" fill="#64748b" font-size="13" font-style="italic" text-anchor="middle">away</text>`;
  s += `<rect x="${sx(zr + 0.12)}" y="${sz(z.top + 0.12)}" width="${(zr - zl + 0.24) * S}" height="${(z.top - z.bot + 0.24) * S}" fill="none" stroke="#64748b" stroke-dasharray="5 4"/>`;
  s += `<rect x="${sx(zr)}" y="${sz(z.top)}" width="${(zr - zl) * S}" height="${(z.top - z.bot) * S}" fill="#17233f" stroke="#f8fafc" stroke-width="3"/>`;
  for (let i = 1; i <= 2; i++) {
    const xx = zl + i * (zr - zl) / 3, zz = z.bot + i * (z.top - z.bot) / 3;
    s += `<line x1="${sx(xx)}" y1="${sz(z.top)}" x2="${sx(xx)}" y2="${sz(z.bot)}" stroke="#475569"/><line x1="${sx(zl)}" y1="${sz(zz)}" x2="${sx(zr)}" y2="${sz(zz)}" stroke="#475569"/>`;
  }
  s += `<polygon points="${sx(-0.708)},${sz(-0.12)} ${sx(0.708)},${sz(-0.12)} ${sx(0.708)},${sz(-0.3)} ${sx(0)},${sz(-0.48)} ${sx(-0.708)},${sz(-0.3)}" fill="#f8fafc"/>`;
  s += `<text x="${sx(z.stand === 'R' ? -2.45 : 2.45)}" y="${sz(2.5)}" fill="#475569" font-size="22" font-weight="700" text-anchor="middle">${z.stand}HB</text>`;
  R.prev.forEach(b => b.pitches.forEach(p => s += dotSvg(p, false)));
  R.cur.forEach(p => s += dotSvg(p, true));
  s += '<g id="reveal"></g><g id="mark"></g><text id="readout" x="594" y="20" fill="#94a3b8" font-size="13" text-anchor="end"></text>';
  $('zone').innerHTML = s;
}
function dotSvg(p, big) {
  if (p.x == null || p.z == null) return '';
  const x = sx(clx(p.x)), y = sz(clz(p.z)), c = COLORS[p.pt] || '#94a3b8';
  const tip = `<title>${esc(p.name)} - ${f1(p.mph)} mph - ${esc(p.loc)} - ${esc(p.result)}</title>`;
  if (!big) return `<circle cx="${x}" cy="${y}" r="7" fill="${c}" fill-opacity=".9" stroke="#0f172a">${tip}</circle>`;
  return `<g><circle cx="${x}" cy="${y}" r="13" fill="${c}" stroke="#fff" stroke-width="2.5"/>` +
    `<text x="${x}" y="${y + 4}" fill="#fff" stroke="#000" stroke-width="3" paint-order="stroke" font-size="12" font-weight="700" text-anchor="middle">${p.n}</text>${tip}</g>`;
}
function svgPoint(e) {
  const r = $('zone').getBoundingClientRect();
  const px = (e.clientX - r.left) / r.width * 600, py = (e.clientY - r.top) / r.height * 600;
  return {x: -(X0 + px / S), z: Z1 - py / S, px, py};        // back to plate_x (un-mirror)
}
$('zone').addEventListener('mousemove', e => {
  if (!R) return;
  const p = svgPoint(e), inside = (p.x < 0) === (R.zone.stand === 'R');
  $('readout').textContent = (Math.abs(p.x) < 0.005 ? 'center' : Math.abs(p.x).toFixed(2) + ' ft ' + (inside ? 'inside' : 'away')) + '  |  height ' + p.z.toFixed(2) + ' ft';
});
$('zone').addEventListener('click', e => {
  if (!R || phase !== 'guess') return;
  const p = svgPoint(e);
  guess = {x: p.x, z: p.z};
  $('mark').innerHTML = `<circle cx="${p.px}" cy="${p.py}" r="9" fill="none" stroke="#facc15" stroke-width="3"/>` +
    `<line x1="${p.px - 15}" y1="${p.py}" x2="${p.px + 15}" y2="${p.py}" stroke="#facc15" stroke-width="2"/>` +
    `<line x1="${p.px}" y1="${p.py - 15}" x2="${p.px}" y2="${p.py + 15}" stroke="#facc15" stroke-width="2"/>`;
  updateLock();
});

function pick(pt) {
  if (phase !== 'guess') return;
  picked = pt;
  document.querySelectorAll('.tbtn').forEach(b => b.classList.toggle('sel', b.dataset.pt === pt));
  updateLock();
}
function updateLock() {
  if (phase !== 'guess') return;
  const b = $('lock');
  b.disabled = !(picked && guess);
  b.textContent = !picked && !guess ? 'Pick a pitch type + click the zone' : !picked ? 'Pick a pitch type' : !guess ? 'Click the zone' : 'Lock in guess (Enter)';
}
async function lock() {
  if (phase !== 'guess' || !picked || !guess || tt.up) return;
  phase = 'busy'; $('lock').disabled = true;
  const a = await api('/api/guess', {type: picked, x: guess.x, z: guess.z});
  if (a.error) { overlay(`<p>${esc(a.error)}</p><button class="primary" onclick="hideOverlay()">OK</button>`); phase = 'guess'; updateLock(); return; }
  last = a; $('score').textContent = 'Score ' + a.total;
  const ax = sx(clx(a.x)), az = sz(clz(a.z));
  $('reveal').innerHTML = `<line x1="${sx(guess.x)}" y1="${sz(guess.z)}" x2="${ax}" y2="${az}" stroke="#22c55e" stroke-width="2" stroke-dasharray="5 4"/>` +
    `<circle cx="${ax}" cy="${az}" r="17" fill="none" stroke="#22c55e" stroke-width="4"/><circle cx="${ax}" cy="${az}" r="3" fill="#22c55e"/>`;
  document.querySelectorAll('.tbtn').forEach(b => {
    if (b.dataset.pt === a.pt) b.classList.add('right'); else if (b.dataset.pt === picked) b.classList.add('wrong');
  });
  const noteTxt = a.type_note === 'exact' ? 'exactly right' : a.type_note === 'same family' ? 'same family' : 'miss';
  $('result').innerHTML = `<div class="ans">${esc(a.name)} &middot; ${f1(a.mph)} mph</div>
    <div>${esc(a.loc)} &middot; ${esc(a.result)}${a.event ? ' (' + esc(a.event) + ')' : ''}</div>
    <p>You said <b>${esc(a.guess_name)}</b>: +${a.type_pts} (${noteTxt})<br>Location: ${a.dist == null ? 'no guess' : a.dist.toFixed(1) + ' ft off'}: +${a.loc_pts}<br>
    <b class="good">Round: ${a.pts} / 100</b></p>`;
  $('vsbox').innerHTML = `<div class="vs ${a.vs_batter.verdict}"><b>You vs. the batter:</b> ${esc(a.vs_batter.text)}</div>`;
  const v = $('vid'); v.src = a.full; v.controls = true; v.play().catch(() => {});
  $('vlabel').textContent = 'Full pitch (controls on - unmute for crowd noise)';
  phase = 'next';
  $('lock').textContent = a.done ? 'See final score (Enter)' : 'Next round (Enter)'; $('lock').disabled = false;
  if (tt.up) showFinal();                // the clock ran out while the guess was in flight - the guess still counts
}
async function act() {
  if (phase === 'guess') return lock();
  if (phase === 'next') return last && last.done ? showFinal() : loadRound();
}
async function showFinal() {
  if (ended) return;
  ended = true; tt.running = false;
  const f = await api('/api/final'), time = cfg.format === 'time';
  const sub = `${MODE_LABEL[cfg.mode]} \u00b7 ${cfg.year || 'All years'}` +
    (time ? ` \u00b7 ${f.rounds_played} round${f.rounds_played === 1 ? '' : 's'} \u00b7 avg ${f.rounds_played ? Math.round(f.total / f.rounds_played) : 0} per round` : '');
  overlay(`<h2>${time ? "Time's up!" : 'Game over'}</h2><div class="bigscore">${f.total}${f.max ? ' / ' + f.max : ' pts'}</div><div class="muted">${esc(sub)}</div>` +
    (f.new_best ? '<p class="gold">New personal best!</p>' : `<p class="muted">Personal best: ${f.best}</p>`) +
    '<div class="scroll"><table><tr><th>Round</th><th>Pitch</th><th>Type</th><th>Location</th><th>Total</th></tr>' +
    f.log.map(r => `<tr><td>${r.round}</td><td>${esc(r.name)}</td><td>${r.type_pts}</td><td>${r.loc_pts}</td><td>${r.pts}</td></tr>`).join('') +
    '</table></div><div class="btns"><button class="primary" onclick="startGame()">Play again</button><button onclick="showMenu()">Change settings</button></div>');
}
function replay() { const v = $('vid'); if (v.src) { v.currentTime = 0; v.play().catch(() => {}); } }

$('lock').addEventListener('click', act);
$('replay').addEventListener('click', replay);
$('menubtn').addEventListener('click', showMenu);
document.addEventListener('keydown', e => {
  if (overlayOpen()) return;
  if (e.key === 'Enter') act();
  else if (e.key === 'r' || e.key === 'R') replay();
  else if (/^[1-9]$/.test(e.key)) { const b = document.querySelectorAll('.tbtn')[+e.key - 1]; if (b) b.click(); }
});
(async () => {
  CFG = await api('/api/config');
  menu.year = String(CFG.default_year);
  showMenu();
})();
</script>
</body></html>
"""


# ----------------------------- launch -----------------------------
def open_window(url, server):
    try:
        import webview  # pip3 install pywebview  -> native Mac window
    except ImportError:
        webview = None
    if webview is not None:
        threading.Thread(target=server.serve_forever, daemon=True).start()
        webview.create_window("Pitch Guesser", url, width=1440, height=900, min_size=(1000, 700))
        webview.start()
        return
    print("(Tip: `pip3 install pywebview` for a native app window.)")
    if os.path.isdir("/Applications/Google Chrome.app"):
        subprocess.Popen(["open", "-na", "Google Chrome", "--args", "--app=" + url, "--window-size=1440,900"])
    else:
        webbrowser.open(url)
    print("Close the window when you're done, then press Ctrl-C here.")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass


def main():
    if not shutil.which("ffmpeg"):
        raise RuntimeError("ffmpeg is required. The included Dockerfile installs it automatically.")
    port = int(os.environ.get("PORT", "8000"))
    server = ThreadingHTTPServer(("0.0.0.0", port), Handler)
    print("Pitch Guesser listening on 0.0.0.0:%d" % port, flush=True)
    try:
        server.serve_forever()
    finally:
        server.server_close()
        shutil.rmtree(TMP, ignore_errors=True)


if __name__ == "__main__":
    main()
