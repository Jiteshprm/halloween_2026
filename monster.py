#!/usr/bin/env python3
"""
Halloween voice-changer monster for Raspberry Pi Zero 2 W.

Listens for someone talking, records until they stop, then plays it back
in a random monster voice (never the same voice twice in a row).

Every processed clip is saved as an MP3 in the "audios" folder next to this
script, named  Halloween_voice_YYYY-MM-DD_hh_mm_ss.mp3

A small web interface runs alongside it (default port 80):
  /          shows a picture for the voice that just played, buttons to play
             the last audio in the browser or on the monster's own speaker,
             and a picker for the voice of the NEXT visitor (default: random)
  /history   lists every audio in the "audios" folder; play any of them in
             the browser or on the monster's speaker

Port 80 needs a one-time permission on the Pi (see start_web_server below).

Optional: drop your own pictures in an "images" folder named after the voice,
e.g. images/Demon.png (png, jpg, jpeg, webp, gif or svg). They replace the
built-in drawings.

Setup:
  sudo apt install sox libsox-fmt-all libportaudio2 python3-numpy python3-sounddevice
  python3 monster.py

Find your input device name with:  python3 -m sounddevice
"""
import json
import os
import random
import re
import shutil
import socket
import subprocess
import tempfile
import threading
import time
import urllib.parse
import wave
from collections import deque
from datetime import datetime
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

import numpy as np
import sounddevice as sd

# ---------------------------------------------------------------- settings
INPUT_DEVICE = "AB13X"       # part of the USB mic's name (device 0 in your list)
FALLBACK_DEVICE = "pulse"    # used if the USB device can't be opened directly
RATES_TO_TRY = [48000, 44100, 16000]   # tried in this order, first one the device accepts is used

# SoX plays through PipeWire/PulseAudio (needed for the Bluetooth speaker).
# Set to None to use plain ALSA (e.g. a wired USB speaker).
AUDIO_DRIVER = "pulseaudio"

MIN_THRESHOLD = 300          # floor for the "someone is talking" level
THRESHOLD_MULTIPLIER = 3     # trigger = noise floor x this (or MIN_THRESHOLD)
STOP_FACTOR = 0.5            # recording only ends below (start level x this), so soft
                             # words and trailing-off endings aren't taken for silence
SILENCE_SECS = 1.2           # this much quiet (below the stop level) ends the recording
TAIL_KEEP_SECS = 0.3         # natural silence kept after the last word
MIN_SECS = 0.4               # ignore clips shorter than this (pops, bumps)
MAX_SECS = 15                # hard cap on a single recording
PREROLL_BLOCKS = 4           # keep a little audio from before the trigger
SAVE_RAW_RECORDING = False   # True = also keep the untouched recording in audios/raw/
                             # (handy for checking what the mic actually heard)
BLOCK_SECS = 0.064           # length of each audio block read

# Saved audio and web interface
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
AUDIO_DIR = os.path.join(BASE_DIR, "audios")    # processed clips are saved here
IMAGES_DIR = os.path.join(BASE_DIR, "images")   # optional picture overrides
MP3_BITRATE = "128"
WEB_ENABLED = True
WEB_HOST = "0.0.0.0"         # listen on all network interfaces
WEB_PORT = 80
# Bluetooth speakers often swallow the first moment of sound while they wake up.
# This much silence is added before / after anything played on the speaker
# (the saved MP3s are not changed). Set both to 0 for a wired speaker.
PLAYBACK_LEAD_IN_SECS = 0.7
PLAYBACK_TAIL_SECS = 1.0
# Bluetooth speaker to look after (needed for starting on boot): at startup the script
# connects it and makes it the default output, then checks every few seconds and
# reconnects if it drops. Use None to leave Bluetooth alone (e.g. wired speaker).
BLUETOOTH_SPEAKER = "00:0C:8A:92:93:63"
BLUETOOTH_WAIT_SECS = 45     # how long to wait for it at startup before carrying on
BLUETOOTH_CHECK_SECS = 15    # how often to check it is still connected
# A bigger playback buffer (milliseconds) makes dropouts less likely when the Pi is
# busy, at the cost of a slightly later start. 0 = use the system default.
PLAY_LATENCY_MSEC = 250
# Keep a silent stream playing so the Bluetooth link never has to wake up or close
# between clips. This stops the end of a clip being cut off when the stream closes.
# Needs pacat (sudo apt install pulseaudio-utils). Costs a little CPU and means the
# Bluetooth radio is always in use. Set False for a wired speaker.
KEEP_SPEAKER_AWAKE = True
# Voices with reverb/echo get this much silence appended BEFORE the effect, so the
# echo has room to fade out completely instead of being chopped at the end.
RENDER_TAIL_SECS = 1.5
MIC_COOLDOWN_SECS = 0.8     # mic ignores sound this long after a stored audio ends

# Each entry is a list of SoX effects. One is chosen per clip.
VOICES = [
    ("Demon",   ["pitch", "-700", "overdrive", "8", "reverb", "40"]),
    ("Giant",   ["pitch", "-1100", "echo", "0.8", "0.85", "70", "0.4"]),
    # Ghost: headroom (gain -4) BEFORE the reverb so it can't clip internally, and a
    # lighter reverb (60, was 90) so the sound isn't one dense wall of loud noise.
    ("Ghost",   ["pitch", "300", "gain", "-4", "reverb", "60", "tremolo", "6", "40"]),
    ("Gremlin", ["pitch", "800", "overdrive", "12",
                 "chorus", "0.7", "0.9", "55", "0.4", "0.25", "2", "-t"]),
    ("Zombie",    ["tempo", "0.8", "pitch", "-350", "overdrive", "10",
                   "tremolo", "4", "30", "reverb", "40"]),
    ("Witch",     ["pitch", "500", "chorus", "0.6", "0.9", "50", "0.4", "0.25", "2", "-t",
                   "tremolo", "8", "25"]),
    ("Possessed", ["pitch", "-500", "chorus", "0.7", "0.9", "55", "0.4", "0.25", "2", "-t",
                   "echo", "0.8", "0.7", "45", "0.5", "reverb", "60"]),
]
# ------------------------------------------------------------------------


# ------------------------------------------------------- built-in pictures
def _svg(glow: str, body: str) -> str:
    return (
        '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 200 200">'
        '<defs><radialGradient id="g" cx="50%" cy="50%" r="50%">'
        f'<stop offset="0" stop-color="{glow}" stop-opacity=".55"/>'
        f'<stop offset="1" stop-color="{glow}" stop-opacity="0"/>'
        '</radialGradient></defs>'
        '<circle cx="100" cy="100" r="100" fill="url(#g)"/>' + body + "</svg>"
    )


ART = {
    "Unknown": _svg("#ff7518",
        '<path d="M100 54 C96 40 100 30 112 22" stroke="#4a7a1e" stroke-width="9" '
        'fill="none" stroke-linecap="round"/>'
        '<ellipse cx="100" cy="118" rx="80" ry="64" fill="#ff7518"/>'
        '<path d="M100 54 C66 72 66 164 100 182 M100 54 C134 72 134 164 100 182" '
        'stroke="#c4540a" stroke-width="3" fill="none"/>'
        '<path d="M60 108 L88 100 L76 126z M140 108 L112 100 L124 126z" fill="#2b1200"/>'
        '<path d="M68 142 Q100 176 132 142 L122 140 L114 152 L100 142 L86 152 L78 140z" '
        'fill="#2b1200"/>'),
    "Demon": _svg("#ff2a2a",
        '<path d="M50 74 Q34 30 70 16 Q60 46 82 62z" fill="#3a0a0a"/>'
        '<path d="M150 74 Q166 30 130 16 Q140 46 118 62z" fill="#3a0a0a"/>'
        '<ellipse cx="100" cy="112" rx="56" ry="62" fill="#d4181f"/>'
        '<path d="M56 84 L94 108 L94 96 L58 74z M144 84 L106 108 L106 96 L142 74z" fill="#2a0508"/>'
        '<ellipse cx="76" cy="110" rx="12" ry="8" fill="#ffe600"/>'
        '<ellipse cx="124" cy="110" rx="12" ry="8" fill="#ffe600"/>'
        '<rect x="74" y="102" width="4" height="16" rx="2" fill="#000"/>'
        '<rect x="122" y="102" width="4" height="16" rx="2" fill="#000"/>'
        '<circle cx="94" cy="134" r="3" fill="#7a0c10"/><circle cx="106" cy="134" r="3" fill="#7a0c10"/>'
        '<path d="M58 146 Q100 196 142 146 Q100 160 58 146z" fill="#2a0508"/>'
        '<path d="M72 152 l7 16 7 -13z M114 155 l7 13 7 -16z" fill="#fff"/>'),
    "Giant": _svg("#6bbf2f",
        '<ellipse cx="44" cy="106" rx="14" ry="20" fill="#6a9a3c"/>'
        '<ellipse cx="156" cy="106" rx="14" ry="20" fill="#6a9a3c"/>'
        '<path d="M46 82 Q48 30 100 28 Q152 30 154 82 L160 132 Q152 180 100 180 '
        'Q48 180 40 132z" fill="#7cae4a"/>'
        '<path d="M52 84 Q100 58 148 84 L148 100 Q100 80 52 100z" fill="#4a7324"/>'
        '<circle cx="78" cy="104" r="9" fill="#fff6b0"/><circle cx="122" cy="104" r="9" fill="#fff6b0"/>'
        '<circle cx="80" cy="106" r="4" fill="#000"/><circle cx="120" cy="106" r="4" fill="#000"/>'
        '<ellipse cx="100" cy="130" rx="15" ry="11" fill="#6a9a3c"/>'
        '<circle cx="94" cy="132" r="3" fill="#3d5e1d"/><circle cx="106" cy="132" r="3" fill="#3d5e1d"/>'
        '<path d="M60 150 Q100 170 140 150 L136 164 Q100 184 64 164z" fill="#2b1a10"/>'
        '<path d="M72 154 L64 126 L88 158z M128 154 L136 126 L112 158z" fill="#f4ecd0"/>'),
    "Ghost": _svg("#9ad7ff",
        '<path d="M50 166 L50 88 Q50 34 100 34 Q150 34 150 88 L150 166 Q138 152 125 166 '
        'Q112 152 100 166 Q88 152 75 166 Q62 152 50 166z" fill="#f2f6ff"/>'
        '<ellipse cx="78" cy="90" rx="10" ry="15" fill="#10131f"/>'
        '<ellipse cx="122" cy="90" rx="10" ry="15" fill="#10131f"/>'
        '<ellipse cx="100" cy="128" rx="10" ry="15" fill="#10131f"/>'
        '<ellipse cx="62" cy="112" rx="8" ry="5" fill="#ffc9d6" opacity=".7"/>'
        '<ellipse cx="138" cy="112" rx="8" ry="5" fill="#ffc9d6" opacity=".7"/>'),
    "Gremlin": _svg("#8be03a",
        '<path d="M60 102 L6 60 L50 138z" fill="#6fbf3a"/><path d="M56 104 L22 80 L50 126z" fill="#e89aa8"/>'
        '<path d="M140 102 L194 60 L150 138z" fill="#6fbf3a"/><path d="M144 104 L178 80 L150 126z" fill="#e89aa8"/>'
        '<ellipse cx="100" cy="118" rx="48" ry="46" fill="#6fbf3a"/>'
        '<path d="M58 84 L92 98 L92 90 L60 74z M142 84 L108 98 L108 90 L140 74z" fill="#1d3a0d"/>'
        '<circle cx="80" cy="110" r="16" fill="#fff"/><circle cx="120" cy="110" r="16" fill="#fff"/>'
        '<circle cx="82" cy="112" r="8" fill="#e11"/><circle cx="118" cy="112" r="8" fill="#e11"/>'
        '<circle cx="83" cy="113" r="3.5" fill="#000"/><circle cx="117" cy="113" r="3.5" fill="#000"/>'
        '<path d="M68 140 Q100 172 132 140z" fill="#2a0a1a"/>'
        '<path d="M74 141 l5 11 5 -10z M90 144 l5 12 5 -12z M106 144 l5 12 5 -12z M122 141 l-5 11 -5 -10z" '
        'fill="#fff"/>'),
    "Zombie": _svg("#8fd14f",
        '<path d="M56 74 Q56 32 100 32 Q144 32 144 74 L144 130 Q144 172 100 172 Q56 172 56 130z" '
        'fill="#a8c98a"/>'
        '<path d="M54 80 Q56 40 82 36 L80 54 L98 34 L106 54 L126 36 L142 60 L146 80 Q120 54 100 62 '
        'Q76 54 54 80z" fill="#3b2f2a"/>'
        '<path d="M116 58 l24 20" stroke="#7a2020" stroke-width="5" stroke-linecap="round"/>'
        '<circle cx="80" cy="98" r="14" fill="#2a2a1a"/><circle cx="80" cy="98" r="9" fill="#e9e6c5"/>'
        '<circle cx="82" cy="100" r="4" fill="#a01010"/>'
        '<circle cx="120" cy="98" r="14" fill="#2a2a1a"/>'
        '<path d="M112 90 L128 106 M128 90 L112 106" stroke="#e9e6c5" stroke-width="4" stroke-linecap="round"/>'
        '<path d="M96 120 l4 9 4 -9z" fill="#5b7a43"/>'
        '<path d="M70 144 Q100 158 130 144" stroke="#2a1a14" stroke-width="5" fill="none" stroke-linecap="round"/>'
        '<path d="M78 138 v14 M90 142 v14 M102 144 v14 M114 142 v14 M126 138 v14" '
        'stroke="#2a1a14" stroke-width="3" stroke-linecap="round"/>'),
    "Witch": _svg("#a24bff",
        '<path d="M64 112 Q50 150 62 186 Q70 150 76 118z M136 112 Q150 150 138 186 Q130 150 124 118z" fill="#e8e0ff"/>'
        '<ellipse cx="100" cy="132" rx="38" ry="42" fill="#8fd16a"/>'
        '<path d="M100 6 L140 84 L60 84z" fill="#2b1b4a"/>'
        '<path d="M72 68 L128 68 L132 82 L68 82z" fill="#8a3ffc"/>'
        '<rect x="92" y="67" width="16" height="13" fill="none" stroke="#ffd23a" stroke-width="3"/>'
        '<ellipse cx="100" cy="86" rx="64" ry="13" fill="#2b1b4a"/>'
        '<path d="M70 114 L94 122 L94 118 L72 108z M130 114 L106 122 L106 118 L128 108z" fill="#2a1a14"/>'
        '<ellipse cx="82" cy="128" rx="9" ry="6" fill="#ffe14a"/><ellipse cx="118" cy="128" rx="9" ry="6" fill="#ffe14a"/>'
        '<circle cx="82" cy="128" r="3" fill="#000"/><circle cx="118" cy="128" r="3" fill="#000"/>'
        '<path d="M100 132 Q116 150 98 154" fill="#7bb856" stroke="#5e9a40" stroke-width="2"/>'
        '<circle cx="108" cy="152" r="2.5" fill="#4a7a30"/>'
        '<path d="M76 160 Q100 180 126 158" stroke="#2a1a14" stroke-width="4" fill="none" stroke-linecap="round"/>'
        '<path d="M92 168 l4 9 4 -7z" fill="#fff"/>'),
    "Possessed": _svg("#c040ff",
        '<ellipse cx="110" cy="106" rx="54" ry="66" fill="#d9d9e6" opacity=".3"/>'
        '<ellipse cx="100" cy="108" rx="54" ry="66" fill="#e4e4ee"/>'
        '<path d="M44 108 Q34 30 100 34 Q166 30 156 108 Q150 62 100 58 Q50 62 44 108z" fill="#16121c"/>'
        '<path d="M46 100 Q34 146 48 190 M154 100 Q166 146 152 190" stroke="#16121c" '
        'stroke-width="9" fill="none" stroke-linecap="round"/>'
        '<ellipse cx="76" cy="96" rx="19" ry="15" fill="#2a2a3a"/><ellipse cx="124" cy="96" rx="19" ry="15" fill="#2a2a3a"/>'
        '<ellipse cx="76" cy="96" rx="12" ry="9" fill="#fff"/><ellipse cx="124" cy="96" rx="12" ry="9" fill="#fff"/>'
        '<circle cx="76" cy="91" r="3" fill="#000"/><circle cx="124" cy="91" r="3" fill="#000"/>'
        '<path d="M58 96 L40 84 M60 106 L44 122 M94 96 L100 74 M142 96 L160 84 M140 106 L156 122 M106 96 L100 74" '
        'stroke="#1a1a2a" stroke-width="2" fill="none"/>'
        '<ellipse cx="100" cy="150" rx="19" ry="28" fill="#0a0a12"/>'
        '<path d="M92 128 l4 10 4 -10z" fill="#fff"/>'),
}
# ------------------------------------------------------------------------


# ------------------------------------------------------------ web pages
_CSS = """
:root{color-scheme:dark;--bg1:#0b0710;--bg2:#1c0f2b;--card:#1b1226;--line:#34214a;
--orange:#ff7518;--orange2:#ffb347;--text:#f3ecff;--muted:#a79bbd}
*{box-sizing:border-box}
[hidden]{display:none!important}
html,body{margin:0;min-height:100%}
body{font-family:system-ui,-apple-system,"Segoe UI",Roboto,sans-serif;color:var(--text);
background:radial-gradient(1200px 600px at 50% -10%,#3a1a5a 0%,transparent 60%),
linear-gradient(180deg,var(--bg1),var(--bg2));background-attachment:fixed;min-height:100vh}
header{display:flex;flex-wrap:wrap;gap:12px;align-items:center;justify-content:space-between;
padding:16px 20px;max-width:880px;margin:0 auto}
h1{font-family:Georgia,"Times New Roman",serif;font-size:1.5rem;margin:0;color:var(--orange);
letter-spacing:.5px;text-shadow:0 0 18px rgba(255,117,24,.45)}
nav{display:flex;gap:8px}
nav a{color:var(--text);text-decoration:none;padding:8px 14px;border:1px solid var(--line);
border-radius:999px;font-size:.95rem}
nav a.active{background:var(--orange);color:#1a0b00;border-color:var(--orange);font-weight:600}
main{max-width:880px;margin:0 auto;padding:0 20px 40px}
.card{background:var(--card);border:1px solid var(--line);border-radius:20px;padding:22px;
box-shadow:0 10px 40px rgba(0,0,0,.45)}
.muted{color:var(--muted)}
.hero{text-align:center}
.art{width:min(340px,76vw);aspect-ratio:1;margin:0 auto 10px;border-radius:24px;overflow:hidden}
.art img{width:100%;height:100%;display:block;object-fit:cover}
.hero h2{font-family:Georgia,"Times New Roman",serif;font-size:2rem;margin:.2em 0;color:var(--orange2)}
.hero p{margin:.3em 0 0}
button.big{background:var(--orange);color:#1a0b00;border:0;border-radius:999px;font-size:1.1rem;
font-weight:700;padding:14px 28px;cursor:pointer;margin-top:18px;min-width:230px}
button.big:disabled{opacity:.35;cursor:not-allowed}
button.big:not(:disabled):hover{filter:brightness(1.1)}
.pop{animation:pop .6s ease}
@keyframes pop{0%{transform:scale(.94);filter:brightness(1.8)}60%{transform:scale(1.02)}
100%{transform:scale(1);filter:none}}
.sticky{position:sticky;top:8px;z-index:5;margin-bottom:16px}
.now{display:flex;align-items:center;gap:12px;margin-bottom:10px;min-height:48px}
.nowart{width:48px;height:48px;border-radius:10px;object-fit:cover;flex:none}
audio{width:100%}
ul#list{list-style:none;margin:0;padding:0;display:grid;gap:10px}
.row{display:flex;align-items:center;gap:14px;padding:10px 14px;background:var(--card);
border:1px solid var(--line);border-radius:16px;cursor:pointer}
.row:hover{border-color:var(--orange)}
.row.sel{border-color:var(--orange);box-shadow:0 0 0 2px rgba(255,117,24,.35)}
.thumb{width:56px;height:56px;border-radius:12px;object-fit:cover;flex:none;background:#120a1b}
.info{flex:1;min-width:0}
.info b{display:block;font-size:1.05rem}
.info span{color:var(--muted);font-size:.9rem}
.ibtn{width:44px;height:44px;border-radius:50%;border:0;background:var(--orange);color:#1a0b00;
font-size:1.1rem;cursor:pointer;flex:none}
.rowbtns{display:flex;gap:8px;flex:none}
.sbtn{background:transparent;color:var(--orange2);border:2px solid var(--orange)}
.sbtn.live{background:var(--orange);color:#1a0b00}
.legend{font-size:.9rem;margin:-4px 0 12px}
.btns{display:flex;flex-wrap:wrap;gap:10px;justify-content:center;margin-top:18px}
.btns .big{margin-top:0;min-width:200px}
button.big.alt{background:transparent;color:var(--orange2);border:2px solid var(--orange)}
.nextbox{margin-top:16px}
.nextbox h3{margin:0 0 4px;font-family:Georgia,"Times New Roman",serif;color:var(--orange2);font-size:1.25rem}
.nextbox p{margin:0 0 12px;font-size:.95rem}
.chips{display:flex;flex-wrap:wrap;gap:8px}
.chip{display:flex;align-items:center;gap:8px;padding:5px 14px 5px 5px;border:1px solid var(--line);
border-radius:999px;background:#120a1b;color:var(--text);cursor:pointer;font-size:.95rem}
.chip:hover{border-color:var(--orange)}
.chip.on{border-color:var(--orange);background:rgba(255,117,24,.2);font-weight:600}
.chip img,.chip .dice{width:32px;height:32px;border-radius:50%;object-fit:cover;flex:none}
.chip .dice{display:flex;align-items:center;justify-content:center;background:#2b1a40;font-size:1.1rem}
.toast{position:fixed;left:50%;bottom:24px;transform:translateX(-50%);background:#2b1a40;
border:1px solid var(--orange);color:var(--text);padding:10px 18px;border-radius:999px;z-index:20;
max-width:90vw;text-align:center}
"""

_PAGE = """<!doctype html>
<html lang="en"><head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>__TITLE__</title>
<link rel="icon" href="data:,">
<style>__CSS__</style>
</head><body>
<header>
  <h1>&#127875; Halloween Monster</h1>
  <nav>
    <a href="/" class="__LIVE__">Live</a>
    <a href="/history" class="__HIST__">All recordings</a>
  </nav>
</header>
<main>
__BODY__
</main>
<div id="toast" class="toast" hidden></div>
<script>
__JS__
</script>
</body></html>
"""

_MAIN_BODY = """
<section class="card hero" id="card">
  <div class="art"><img id="artimg" src="/art/Unknown" alt="Monster"></div>
  <h2 id="voice">Waiting for a visitor&hellip;</h2>
  <p class="muted" id="when">Speak to the monster to hear its voice</p>
  <div class="btns">
    <button class="big" id="play" type="button" disabled
            title="Play in this browser">&#9654; Play last audio</button>
    <button class="big alt" id="spk" type="button" disabled
            title="Play on the monster's own speaker">&#128266; Play last on speaker</button>
  </div>
  <audio id="player" preload="none"></audio>
</section>
<section class="card nextbox">
  <h3>Next voice</h3>
  <p class="muted">Pick a voice for the next visitor. It plays once, then the monster goes back
  to choosing at random.</p>
  <div class="chips" id="chips"></div>
</section>
"""

_COMMON_JS = """
const $ = id => document.getElementById(id);
let toastTimer = null;
function toast(msg) {
  const t = $('toast'); t.textContent = msg; t.hidden = false;
  clearTimeout(toastTimer);
  toastTimer = setTimeout(() => { t.hidden = true; }, 3500);
}
function fmtDur(s) {
  if (s === null || s === undefined) return '';
  if (s < 59.95) return s.toFixed(1) + ' s';
  const t = Math.round(s);
  return Math.floor(t / 60) + ':' + String(t % 60).padStart(2, '0');
}
function meta(it) {                      // "Thu 29 Oct 2026, 20:07:12 · 3.4 s"
  return it.when + (it.duration !== null && it.duration !== undefined
                    ? ' \\u00B7 ' + fmtDur(it.duration) : '');
}
async function getJSON(path) {
  const r = await fetch(path, {cache: 'no-store'});
  return await r.json();
}
async function postJSON(path, body) {
  try {
    const r = await fetch(path, {method: 'POST', headers: {'Content-Type': 'application/json'},
                                 body: JSON.stringify(body || {})});
    const d = await r.json().catch(() => ({}));
    if (!r.ok && d.error) toast(d.error);
    return d;
  } catch (e) { toast('Could not reach the monster'); return {}; }
}

/* what the monster's own speaker is playing (stored audios) */
let speakerFile = null;
async function pollSpeaker() {
  try {
    const d = await getJSON('/api/speaker');
    const f = d.file || null;
    if (f !== speakerFile) { speakerFile = f; if (typeof onSpeaker === 'function') onSpeaker(); }
  } catch (e) { /* server restarting, try again */ }
}
async function toggleSpeaker(file) {
  if (speakerFile === file) await postJSON('/api/stop');
  else await postJSON('/api/play', {file: file});
  await pollSpeaker();
}
pollSpeaker();
setInterval(pollSpeaker, 1500);
"""

_MAIN_JS = """
const audio = $('player'), btn = $('play'), spk = $('spk');
let current = null, lastItem = null, nextVoice = null, voices = [];

function label() {
  btn.textContent = (!audio.paused && !audio.ended) ? '\\u23F8 Pause' : '\\u25B6 Play last audio';
}
function onSpeaker() {
  const on = lastItem && speakerFile === lastItem.file;
  spk.textContent = on ? '\\u23F9 Stop speaker' : '\\u{1F50A} Play last on speaker';
}
['play', 'pause', 'ended'].forEach(ev => audio.addEventListener(ev, label));

btn.addEventListener('click', () => {
  if (!current) return;
  if (!audio.paused) { audio.pause(); return; }
  if (audio.ended) audio.currentTime = 0;
  audio.play().catch(() => {});
});
spk.addEventListener('click', () => { if (lastItem) toggleSpeaker(lastItem.file); });

function renderChips() {
  const box = $('chips');
  box.replaceChildren();
  const add = (value, text, icon) => {
    const b = document.createElement('button');
    b.type = 'button';
    b.className = 'chip' + (nextVoice === value ? ' on' : '');
    b.append(icon, document.createTextNode(text));
    b.addEventListener('click', () => chooseNext(value));
    box.appendChild(b);
  };
  const dice = document.createElement('span');
  dice.className = 'dice'; dice.textContent = '\\u{1F3B2}';
  add(null, 'Random', dice);
  voices.forEach(v => {
    const i = document.createElement('img');
    i.alt = ''; i.src = '/art/' + encodeURIComponent(v);
    add(v, v, i);
  });
}
async function chooseNext(value) {
  const target = (value === nextVoice) ? null : value;     // tap again = back to random
  const d = await postJSON('/api/next', {voice: target === null ? 'random' : target});
  if (d.ok) { nextVoice = d.next || null; renderChips(); }
}
async function pollNext() {
  try {
    const d = await getJSON('/api/next');
    const n = d.next || null;
    if (n !== nextVoice || d.voices.length !== voices.length) {
      nextVoice = n; voices = d.voices; renderChips();
    }
  } catch (e) { /* ignore */ }
}

async function refresh() {
  pollNext();
  try {
    const d = await getJSON('/api/last');
    if (d.file === current) return;
    current = d.file;
    lastItem = d.file ? d : null;
    audio.pause();
    if (d.file) {
      $('artimg').src = '/art/' + encodeURIComponent(d.voice);
      $('voice').textContent = d.voice;
      $('when').textContent = meta(d);
      audio.src = d.url;
    } else {
      $('artimg').src = '/art/Unknown';
      $('voice').textContent = 'Waiting for a visitor\\u2026';
      $('when').textContent = 'Speak to the monster to hear its voice';
    }
    btn.disabled = spk.disabled = !d.file;
    label(); onSpeaker();
    const card = $('card');
    card.classList.remove('pop'); void card.offsetWidth; card.classList.add('pop');
  } catch (e) { /* server restarting, try again next tick */ }
}
label(); onSpeaker();
refresh();
setInterval(refresh, 2000);
"""

_HIST_BODY = """
<section class="card sticky">
  <div class="now">
    <img id="nowart" class="nowart" alt="" hidden>
    <div id="nowtitle" class="muted">Pick a recording below to play it</div>
  </div>
  <audio id="player" controls preload="none"></audio>
</section>
<p class="muted" id="count"></p>
<p class="muted legend" id="legend" hidden>&#9654; plays in this browser &nbsp;&middot;&nbsp;
&#128266; plays on the monster's own speaker</p>
<p class="muted" id="empty" hidden>No recordings yet. Talk to the monster and they will show up here.</p>
<ul id="list"></ul>
"""

_HIST_JS = """
const audio = $('player'), list = $('list');
let selected = null, sig = '', items = [];

function icon(voice) {
  const i = document.createElement('img');
  i.className = 'thumb'; i.alt = ''; i.loading = 'lazy';
  i.src = '/art/' + encodeURIComponent(voice);
  return i;
}

function refreshRows() {
  const playing = !audio.paused && !audio.ended;
  for (const li of list.children) {
    const file = li.dataset.file;
    const on = file === selected;
    li.classList.toggle('sel', on);
    const b = li.querySelector('.ibtn');
    if (b) b.textContent = (on && playing) ? '\\u23F8' : '\\u25B6';
    const s = li.querySelector('.sbtn');
    if (s) {
      const live = file === speakerFile;
      s.textContent = live ? '\\u23F9' : '\\u{1F50A}';
      s.classList.toggle('live', live);
      s.title = live ? 'Stop the speaker' : "Play on the monster's speaker";
    }
  }
}
function onSpeaker() { refreshRows(); }

function choose(it) {
  if (selected === it.file) {
    if (audio.paused) { if (audio.ended) audio.currentTime = 0; audio.play().catch(() => {}); }
    else audio.pause();
  } else {
    selected = it.file;
    audio.src = it.url;
    audio.play().catch(() => {});
    $('nowtitle').textContent = it.voice + ' \\u00B7 ' + meta(it);
    $('nowtitle').className = '';
    $('nowart').src = '/art/' + encodeURIComponent(it.voice);
    $('nowart').hidden = false;
  }
  refreshRows();
}

function render() {
  list.replaceChildren();
  $('empty').hidden = items.length > 0;
  $('legend').hidden = items.length === 0;
  const total = items.reduce((a, i) => a + (i.duration || 0), 0);
  $('count').textContent = items.length
    ? items.length + ' recording' + (items.length === 1 ? '' : 's') + ' \\u00B7 ' + fmtDur(total)
      + ' in total \\u00B7 newest first' : '';
  items.forEach(it => {
    const li = document.createElement('li');
    li.className = 'row'; li.dataset.file = it.file;
    const info = document.createElement('div'); info.className = 'info';
    const b = document.createElement('b'); b.textContent = it.voice;
    const s = document.createElement('span'); s.textContent = meta(it);
    info.append(b, s);
    const btns = document.createElement('div'); btns.className = 'rowbtns';
    const play = document.createElement('button');
    play.className = 'ibtn'; play.type = 'button'; play.textContent = '\\u25B6';
    play.title = 'Play in this browser';
    play.setAttribute('aria-label', 'Play ' + it.voice + ' in this browser');
    const spk = document.createElement('button');
    spk.className = 'ibtn sbtn'; spk.type = 'button'; spk.textContent = '\\u{1F50A}';
    spk.setAttribute('aria-label', 'Play ' + it.voice + " on the monster's speaker");
    spk.addEventListener('click', e => { e.stopPropagation(); toggleSpeaker(it.file); });
    btns.append(play, spk);
    li.append(icon(it.voice), info, btns);
    li.addEventListener('click', () => choose(it));
    list.appendChild(li);
  });
  refreshRows();
}

async function load() {
  try {
    items = await getJSON('/api/audios');
    const s = items.map(i => i.file + '|' + i.voice + '|' + i.duration).join('\\n');
    if (s === sig) return;
    sig = s;
    render();
  } catch (e) { /* ignore, retry later */ }
}
['play', 'pause', 'ended'].forEach(ev => audio.addEventListener(ev, refreshRows));
load();
setInterval(load, 8000);
"""


def _build_page(title: str, active: str, body: str, js: str) -> bytes:
    page = (_PAGE.replace("__TITLE__", title)
            .replace("__CSS__", _CSS)
            .replace("__LIVE__", "active" if active == "live" else "")
            .replace("__HIST__", "active" if active == "hist" else "")
            .replace("__BODY__", body)
            .replace("__JS__", _COMMON_JS + js))
    return page.encode("utf-8")


MAIN_HTML = _build_page("Halloween Monster", "live", _MAIN_BODY, _MAIN_JS)
HISTORY_HTML = _build_page("All recordings - Halloween Monster", "hist", _HIST_BODY, _HIST_JS)
# ------------------------------------------------------------------------


# ---------------------------------------------------------- audio archive
_meta_lock = threading.Lock()
_META_FILE = "voices.json"          # maps mp3 file name -> voice name
_FILE_FORMAT = "Halloween_voice_%Y-%m-%d_%H_%M_%S"
_IMAGE_TYPES = {
    ".png": "image/png", ".jpg": "image/jpeg", ".jpeg": "image/jpeg",
    ".webp": "image/webp", ".gif": "image/gif", ".svg": "image/svg+xml",
}


def _load_meta() -> dict:
    try:
        with open(os.path.join(AUDIO_DIR, _META_FILE), encoding="utf-8") as fh:
            data = json.load(fh)
        return data if isinstance(data, dict) else {}
    except (OSError, ValueError):
        return {}


def _remember_voice(filename: str, voice: str) -> None:
    with _meta_lock:
        meta = _load_meta()
        meta[filename] = voice
        tmp = os.path.join(AUDIO_DIR, _META_FILE + ".tmp")
        with open(tmp, "w", encoding="utf-8") as fh:
            json.dump(meta, fh, indent=1)
        os.replace(tmp, os.path.join(AUDIO_DIR, _META_FILE))


def _pretty_when(filename: str, mtime: float) -> str:
    try:
        when = datetime.strptime(filename[:-4], _FILE_FORMAT)
    except ValueError:
        when = datetime.fromtimestamp(mtime)
    return when.strftime("%a %d %b %Y, %H:%M:%S")


# ------------------------------------------------------------- durations
_BITRATES_V1 = [0, 32, 40, 48, 56, 64, 80, 96, 112, 128, 160, 192, 224, 256, 320]   # kbps
_BITRATES_V2 = [0, 8, 16, 24, 32, 40, 48, 56, 64, 80, 96, 112, 128, 144, 160]       # kbps
_SAMPLE_RATES = {3: [44100, 48000, 32000], 2: [22050, 24000, 16000], 0: [11025, 12000, 8000]}
_duration_cache = {}


def _mp3_duration(path: str):
    """Length of an MP3 (Layer III) in seconds, read from its frame headers.
    Needs no extra packages. Returns None if the file can't be understood."""
    try:
        with open(path, "rb") as fh:
            size = os.fstat(fh.fileno()).st_size
            pos = 0
            head = fh.read(10)
            if len(head) == 10 and head[:3] == b"ID3":          # skip ID3v2 tag
                tag = ((head[6] & 0x7F) << 21) | ((head[7] & 0x7F) << 14) \
                    | ((head[8] & 0x7F) << 7) | (head[9] & 0x7F)
                pos = 10 + tag + (10 if head[5] & 0x10 else 0)
            total, first, lost = 0.0, True, 0
            while pos + 4 <= size and lost < 65536:
                fh.seek(pos)
                h = fh.read(4)
                if len(h) < 4:
                    break
                version, layer = (h[1] >> 3) & 3, (h[1] >> 1) & 3
                br_idx, sr_idx, pad = h[2] >> 4, (h[2] >> 2) & 3, (h[2] >> 1) & 1
                if (h[0] != 0xFF or (h[1] & 0xE0) != 0xE0 or version == 1 or layer != 1
                        or br_idx in (0, 15) or sr_idx == 3):
                    pos += 1                                     # not a frame: resync
                    lost += 1
                    continue
                mpeg1 = version == 3
                bitrate = (_BITRATES_V1 if mpeg1 else _BITRATES_V2)[br_idx] * 1000
                rate = _SAMPLE_RATES[version][sr_idx]
                samples = 1152 if mpeg1 else 576
                frame_len = (144 if mpeg1 else 72) * bitrate // rate + pad
                if first:
                    first = False
                    mono = (h[3] >> 6) == 3
                    side_info = (17 if mono else 32) if mpeg1 else (9 if mono else 17)
                    fh.seek(pos + 4 + side_info)
                    tag = fh.read(12)
                    if tag[:4] in (b"Xing", b"Info"):            # encoder's info frame
                        if len(tag) == 12 and tag[7] & 1:        # it states the frame count
                            return int.from_bytes(tag[8:12], "big") * samples / rate
                        pos += frame_len                         # not audio, skip it
                        continue
                total += samples / rate
                pos += frame_len
                lost = 0
            return total if total > 0 else None
    except OSError:
        return None


def _soxi_duration(path: str):
    try:
        out = subprocess.run(["soxi", "-D", path], capture_output=True, text=True, timeout=10)
        return float(out.stdout.strip()) if out.returncode == 0 else None
    except (OSError, ValueError, subprocess.TimeoutExpired):
        return None


def duration_of(path: str):
    """Length of an audio file in seconds (cached), or None if unknown."""
    try:
        st = os.stat(path)
    except OSError:
        return None
    key = (path, st.st_mtime_ns, st.st_size)
    if key not in _duration_cache:
        dur = _mp3_duration(path)
        if dur is None:
            dur = _soxi_duration(path)
        if len(_duration_cache) > 5000:
            _duration_cache.clear()
        _duration_cache[key] = dur
    return _duration_cache[key]


def list_audios() -> list:
    """Every .mp3 in the audios folder, newest first."""
    try:
        names = os.listdir(AUDIO_DIR)
    except OSError:
        return []
    meta = _load_meta()
    found = []
    for name in names:
        if name.startswith(".") or not name.lower().endswith(".mp3"):
            continue
        try:
            mtime = os.path.getmtime(os.path.join(AUDIO_DIR, name))
        except OSError:
            continue
        found.append((mtime, name))
    found.sort(reverse=True)
    items = []
    for mtime, name in found:
        secs = duration_of(os.path.join(AUDIO_DIR, name))
        items.append({
            "file": name,
            "url": "/audios/" + urllib.parse.quote(name),
            "voice": meta.get(name, "Unknown"),
            "when": _pretty_when(name, mtime),
            "duration": round(secs, 2) if secs is not None else None,
        })
    return items


def _new_audio_path() -> str:
    os.makedirs(AUDIO_DIR, exist_ok=True)
    base = datetime.now().strftime(_FILE_FORMAT)
    path = os.path.join(AUDIO_DIR, base + ".mp3")
    n = 1
    while os.path.exists(path):          # only if two clips land in one second
        path = os.path.join(AUDIO_DIR, f"{base}_{n}.mp3")
        n += 1
    return path


# --------------------------------------------- next voice + speaker control
_next_lock = threading.Lock()
_next_voice = None


def set_next_voice(name) -> bool:
    """Choose the voice for the next clip only (None = back to random)."""
    global _next_voice
    if name is not None and name not in [v[0] for v in VOICES]:
        return False
    with _next_lock:
        _next_voice = name
    return True


def get_next_voice():
    with _next_lock:
        return _next_voice


_speaker_lock = threading.Lock()       # held while anything plays on the device
_stored_lock = threading.Lock()
_stored = {"file": None, "proc": None, "stop": False}
_mic_muted_until = 0.0


def speaker_file():
    """Name of the stored audio currently playing on the device, or None."""
    with _stored_lock:
        return _stored["file"]


def speaker_busy() -> bool:
    """True while a stored audio plays on the device (and just after), so the
    microphone doesn't hear it and treat it as a visitor."""
    return speaker_file() is not None or time.time() < _mic_muted_until


def _play_stored_worker(path: str) -> None:
    global _mic_muted_until
    try:
        proc = subprocess.Popen(["play", "-q", path, *_padding()], env=_audio_env(),
                                stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        with _stored_lock:
            _stored["proc"] = proc
            if _stored["stop"]:
                proc.terminate()
        proc.wait()
    except FileNotFoundError:
        print("  !! 'play' not found. Run: sudo apt install sox libsox-fmt-all")
    finally:
        with _stored_lock:
            _stored.update(file=None, proc=None, stop=False)
        _mic_muted_until = time.time() + MIC_COOLDOWN_SECS
        _speaker_lock.release()


def play_stored(name: str):
    """Play a saved MP3 on the device's speaker. Returns (ok, error, http_status)."""
    if (not name or name != os.path.basename(name) or name.startswith(".")
            or not name.lower().endswith(".mp3")):
        return False, "Unknown recording", 404
    path = os.path.join(AUDIO_DIR, name)
    if not os.path.isfile(path):
        return False, "Unknown recording", 404
    if not _speaker_lock.acquire(blocking=False):
        return False, "The speaker is busy, try again in a moment", 409
    with _stored_lock:
        _stored.update(file=name, proc=None, stop=False)
    threading.Thread(target=_play_stored_worker, args=(path,), daemon=True).start()
    return True, "", 200


def stop_stored() -> None:
    with _stored_lock:
        proc = _stored["proc"]
        if proc is not None:
            proc.terminate()
        elif _stored["file"] is not None:
            _stored["stop"] = True


# ------------------------------------------------------------ web server
class Handler(BaseHTTPRequestHandler):
    server_version = "HalloweenMonster/1.0"

    def log_message(self, fmt, *args):      # keep the terminal quiet
        pass

    # -- helpers
    def _send(self, body: bytes, ctype: str, status: int = 200, cache: str = "no-store"):
        self.send_response(status)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", cache)
        self.end_headers()
        self.wfile.write(body)

    def _json(self, obj, status: int = 200):
        self._send(json.dumps(obj).encode("utf-8"), "application/json; charset=utf-8", status)

    def _not_found(self):
        self._send(b"Not found", "text/plain; charset=utf-8", 404)

    def _serve_file(self, filepath: str, ctype: str):
        """Serve a file, with Range support (needed by Safari/iOS for audio)."""
        try:
            size = os.path.getsize(filepath)
        except OSError:
            return self._not_found()
        start, end, status = 0, size - 1, 200
        rng = self.headers.get("Range")
        if rng:
            m = re.fullmatch(r"bytes=(\d*)-(\d*)", rng.strip())
            if m and (m.group(1) or m.group(2)):
                first, last = m.groups()
                if first == "":                       # suffix range: last N bytes
                    start = max(0, size - int(last))
                else:
                    start = int(first)
                    if last:
                        end = min(int(last), size - 1)
                if start > end or start >= size:
                    self.send_response(416)
                    self.send_header("Content-Range", f"bytes */{size}")
                    self.send_header("Content-Length", "0")
                    self.end_headers()
                    return
                status = 206
        length = end - start + 1
        self.send_response(status)
        self.send_header("Content-Type", ctype)
        self.send_header("Accept-Ranges", "bytes")
        self.send_header("Content-Length", str(length))
        self.send_header("Cache-Control", "public, max-age=300")
        if status == 206:
            self.send_header("Content-Range", f"bytes {start}-{end}/{size}")
        self.end_headers()
        try:
            with open(filepath, "rb") as fh:
                fh.seek(start)
                remaining = length
                while remaining > 0:
                    chunk = fh.read(min(65536, remaining))
                    if not chunk:
                        break
                    self.wfile.write(chunk)
                    remaining -= len(chunk)
        except (BrokenPipeError, ConnectionResetError):
            pass

    def _serve_art(self, name: str):
        name = urllib.parse.unquote(name)
        if re.fullmatch(r"[A-Za-z0-9_-]{1,32}", name):
            for ext, ctype in _IMAGE_TYPES.items():
                custom = os.path.join(IMAGES_DIR, name + ext)
                if os.path.isfile(custom):
                    return self._serve_file(custom, ctype)
        svg = ART.get(name, ART["Unknown"])
        self._send(svg.encode("utf-8"), "image/svg+xml", cache="public, max-age=300")

    # -- routes
    def do_GET(self):
        path = urllib.parse.urlparse(self.path).path
        try:
            if path == "/":
                self._send(MAIN_HTML, "text/html; charset=utf-8")
            elif path == "/history":
                self._send(HISTORY_HTML, "text/html; charset=utf-8")
            elif path == "/api/last":
                items = list_audios()
                self._json(items[0] if items else {"file": None})
            elif path == "/api/audios":
                self._json(list_audios())
            elif path == "/api/next":
                self._json({"next": get_next_voice(), "voices": [v[0] for v in VOICES]})
            elif path == "/api/speaker":
                self._json({"file": speaker_file()})
            elif path.startswith("/art/"):
                self._serve_art(path[len("/art/"):])
            elif path.startswith("/audios/"):
                name = urllib.parse.unquote(path[len("/audios/"):])
                if (name != os.path.basename(name) or name.startswith(".")
                        or not name.lower().endswith(".mp3")):
                    return self._not_found()
                full = os.path.join(AUDIO_DIR, name)
                if not os.path.isfile(full):
                    return self._not_found()
                self._serve_file(full, "audio/mpeg")
            else:
                self._not_found()
        except (BrokenPipeError, ConnectionResetError):
            pass

    def do_POST(self):
        path = urllib.parse.urlparse(self.path).path
        try:
            length = int(self.headers.get("Content-Length") or 0)
        except ValueError:
            length = 0
        if length > 4096:
            return self._json({"ok": False, "error": "Request too large"}, 413)
        try:
            data = json.loads(self.rfile.read(length) or b"{}")
            if not isinstance(data, dict):
                raise ValueError("not an object")
        except ValueError:
            return self._json({"ok": False, "error": "Bad request"}, 400)
        try:
            if path == "/api/next":
                voice = data.get("voice")
                if voice in (None, "", "random"):
                    set_next_voice(None)
                elif not set_next_voice(str(voice)):
                    return self._json({"ok": False, "error": "Unknown voice"}, 400)
                self._json({"ok": True, "next": get_next_voice()})
            elif path == "/api/play":
                ok, error, status = play_stored(str(data.get("file", "")))
                self._json({"ok": ok, "error": error, "file": speaker_file()}, status)
            elif path == "/api/stop":
                stop_stored()
                self._json({"ok": True})
            else:
                self._not_found()
        except (BrokenPipeError, ConnectionResetError):
            pass


def _local_ip() -> str:
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("10.255.255.255", 1))
        ip = s.getsockname()[0]
        s.close()
        return ip
    except OSError:
        return "localhost"


def start_web_server() -> None:
    if not WEB_ENABLED:
        return
    try:
        httpd = ThreadingHTTPServer((WEB_HOST, WEB_PORT), Handler)
    except PermissionError:
        print(f"Web interface NOT started: port {WEB_PORT} needs permission. Run this once, "
              "then start the monster again:\n"
              "  echo 'net.ipv4.ip_unprivileged_port_start=80' | "
              "sudo tee /etc/sysctl.d/99-web80.conf && sudo sysctl --system")
        return
    except OSError as err:
        print(f"Web interface NOT started (port {WEB_PORT}): {err}")
        return
    httpd.daemon_threads = True
    threading.Thread(target=httpd.serve_forever, daemon=True).start()
    suffix = "" if WEB_PORT == 80 else f":{WEB_PORT}"
    print(f"Web interface:  http://{_local_ip()}{suffix}/   "
          f"(or http://{socket.gethostname()}.local{suffix}/)")


# ------------------------------------------------------------ voices/audio
_voice_bag = []
_last_voice = None


def pick_voice():
    """Choose the voice for the next clip.

    If someone picked a voice on the web page, use it once. Otherwise use a
    shuffle bag: every voice plays once, in random order, before any voice
    repeats, and never the same voice twice in a row."""
    global _voice_bag, _last_voice
    forced = get_next_voice()
    if forced:
        set_next_voice(None)               # one-shot: back to random afterwards
        for voice in VOICES:
            if voice[0] == forced:
                _voice_bag = [v for v in _voice_bag if v[0] != forced]  # counts as its turn
                _last_voice = forced
                return voice
    if not _voice_bag:
        _voice_bag = VOICES[:]
        random.shuffle(_voice_bag)
    # take from the end, skipping the voice that just played
    idx = next((i for i in range(len(_voice_bag) - 1, -1, -1)
                if _voice_bag[i][0] != _last_voice), len(_voice_bag) - 1)
    voice = _voice_bag.pop(idx)
    _last_voice = voice[0]
    return voice


def rms(block: np.ndarray) -> float:
    return float(np.sqrt(np.mean(block.astype(np.float32) ** 2)))


def open_stream():
    """Try the preferred device at each sample rate, then the fallback.
    Returns (started_stream, rate, blocksize)."""
    last_error = None
    for device in (INPUT_DEVICE, FALLBACK_DEVICE):
        for rate in RATES_TO_TRY:
            blocksize = int(rate * BLOCK_SECS)
            try:
                stream = sd.InputStream(
                    device=device, samplerate=rate, channels=1,
                    dtype="int16", blocksize=blocksize,
                )
                stream.start()
                name = sd.query_devices(stream.device)["name"]
                print(f"Using input: {name} at {rate} Hz")
                return stream, rate, blocksize
            except Exception as err:  # noqa: BLE001
                last_error = err
        print(f"Could not open '{device}', trying next option...")
    raise SystemExit(f"No usable input device found: {last_error}")


def save_wav(path: str, frames: list, rate: int) -> None:
    audio = np.concatenate(frames).astype(np.int16)
    with wave.open(path, "wb") as wf:
        wf.setnchannels(1)
        wf.setsampwidth(2)
        wf.setframerate(rate)
        wf.writeframes(audio.tobytes())


def _padding() -> list:
    """SoX effect that adds silence at the start/end of what we play."""
    if PLAYBACK_LEAD_IN_SECS > 0 or PLAYBACK_TAIL_SECS > 0:
        return ["pad", str(PLAYBACK_LEAD_IN_SECS), str(PLAYBACK_TAIL_SECS)]
    return []


def _audio_env() -> dict:
    env = os.environ.copy()
    if AUDIO_DRIVER:
        env["AUDIODRIVER"] = AUDIO_DRIVER
        if PLAY_LATENCY_MSEC > 0:
            env["PULSE_LATENCY_MSEC"] = str(PLAY_LATENCY_MSEC)
    return env


_keepalive_proc = None


def start_keepalive() -> None:
    """Play endless digital silence so the speaker's audio link stays open."""
    global _keepalive_proc
    if not KEEP_SPEAKER_AWAKE or not AUDIO_DRIVER:      # only for the PipeWire/Bluetooth path
        return
    try:
        _keepalive_proc = subprocess.Popen(
            ["pacat", "--playback", "--rate=48000", "--channels=2", "--format=s16le",
             "--latency-msec=100", "--stream-name=monster-keepalive"],
            stdin=open("/dev/zero", "rb"), stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL)
        print("Keeping the speaker awake (silent stream running).")
    except FileNotFoundError:
        print("  !! 'pacat' not found. Run: sudo apt install pulseaudio-utils")


def stop_keepalive() -> None:
    global _keepalive_proc
    if _keepalive_proc is not None:
        _keepalive_proc.terminate()
        _keepalive_proc = None


# ----------------------------------------------------- bluetooth speaker care
def _run(cmd: list, timeout: int = 15):
    try:
        return subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    except (OSError, subprocess.TimeoutExpired):
        return None


def _bt_sink_name():
    """PipeWire name of the Bluetooth speaker's output, or None if not connected."""
    key = "bluez_output." + BLUETOOTH_SPEAKER.replace(":", "_")
    result = _run(["pactl", "list", "short", "sinks"])
    if result and result.returncode == 0:
        for line in result.stdout.splitlines():
            parts = line.split("\t")
            if len(parts) > 1 and parts[1].startswith(key):
                return parts[1]
    return None


def ensure_speaker(wait_secs: float = 0) -> bool:
    """Connect the Bluetooth speaker and make it the default output.
    Returns True when it is connected and selected."""
    if not BLUETOOTH_SPEAKER or not AUDIO_DRIVER:
        return True
    deadline = time.time() + wait_secs
    while True:
        sink = _bt_sink_name()
        if sink is None:
            _run(["bluetoothctl", "connect", BLUETOOTH_SPEAKER], timeout=25)
            for _ in range(8):                  # the audio output appears a moment later
                time.sleep(1)
                sink = _bt_sink_name()
                if sink:
                    break
        if sink:
            current = _run(["pactl", "get-default-sink"])
            if not current or current.stdout.strip() != sink:
                _run(["pactl", "set-default-sink", sink])
            return True
        if time.time() >= deadline:
            return False
        time.sleep(3)


def _speaker_watchdog() -> None:
    """Background check: reconnect the speaker if it drops, and keep it the default
    output (plugging in a USB headset would otherwise steal it)."""
    announced_down = False
    while True:
        time.sleep(BLUETOOTH_CHECK_SECS)
        present = _bt_sink_name() is not None
        if not present and not announced_down:
            print("Bluetooth speaker disconnected, trying to reconnect...")
            announced_down = True
        ok = ensure_speaker(0)
        if ok and not present:
            print("Bluetooth speaker is back.")
            announced_down = False
            stop_keepalive()
            start_keepalive()                   # reattach the silent stream to it


def prepare_speaker() -> None:
    if not BLUETOOTH_SPEAKER or not AUDIO_DRIVER:
        return
    print(f"Connecting to the Bluetooth speaker {BLUETOOTH_SPEAKER}...")
    if ensure_speaker(BLUETOOTH_WAIT_SECS):
        print("Bluetooth speaker ready.")
    else:
        print("Bluetooth speaker not found yet. Carrying on, will keep trying.")
    threading.Thread(target=_speaker_watchdog, daemon=True).start()


def render_mp3(wav_path: str, mp3_path: str, effects: list) -> bool:
    """Apply the voice effects and write the result as an MP3."""
    has_tail = any(e in ("reverb", "echo") for e in effects)
    room = ["pad", "0", str(RENDER_TAIL_SECS)] if has_tail and RENDER_TAIL_SECS > 0 else []
    cmd = ["sox", wav_path, "-C", MP3_BITRATE, mp3_path, *room, *effects, "gain", "-n", "-2"]
    try:
        result = subprocess.run(cmd, capture_output=True, text=True)
    except FileNotFoundError:
        print("  !! 'sox' not found. Run: sudo apt install sox libsox-fmt-all")
        return False
    if result.returncode != 0 or not os.path.isfile(mp3_path):
        print("  !! Could not write the MP3:", (result.stderr or "").strip()[-300:])
        print("     (is MP3 support installed?  sudo apt install libsox-fmt-all)")
        try:
            os.remove(mp3_path)
        except OSError:
            pass
        return False
    return True


def play_file(path: str, effects: list = ()) -> None:
    with _speaker_lock:                    # wait if a stored audio is playing
        try:
            subprocess.run(["play", "-q", path, *effects, "gain", "-n", "-2", *_padding()],
                           env=_audio_env(), check=False)
        except FileNotFoundError:
            print("  !! 'play' not found. Run: sudo apt install sox libsox-fmt-all")


def handle_clip(wav_path: str) -> None:
    """Pick a voice, save the result as an MP3, play it."""
    name, effects = pick_voice()
    print(f"  -> {name} voice")
    mp3_path = _new_audio_path()
    # render under a hidden name so the web pages never list a half-written file
    tmp_path = os.path.join(AUDIO_DIR, "." + os.path.basename(mp3_path))
    if render_mp3(wav_path, tmp_path, effects):
        _remember_voice(os.path.basename(mp3_path), name)
        os.replace(tmp_path, mp3_path)                      # the web page picks it up now
        secs = duration_of(mp3_path)
        extra = f" ({secs:.1f} s)" if secs else ""
        print(f"  saved {os.path.relpath(mp3_path, BASE_DIR)}{extra}")
        play_file(mp3_path)
    else:
        play_file(wav_path, effects)       # couldn't save, but still scare them


def calibrate(stream, blocksize: int) -> float:
    print("Calibrating background noise (stay quiet for 2 seconds)...")
    levels = []
    end = time.time() + 2
    while time.time() < end:
        data, _ = stream.read(blocksize)
        levels.append(rms(data))
    floor = float(np.mean(levels))
    threshold = max(floor * THRESHOLD_MULTIPLIER, MIN_THRESHOLD)
    print(f"Noise floor {floor:.0f}, trigger threshold {threshold:.0f}")
    if floor < 5:
        print("  Warning: very low level. Is the right mic selected and unmuted?")
    return threshold


def main() -> None:
    os.makedirs(AUDIO_DIR, exist_ok=True)
    start_web_server()
    prepare_speaker()
    start_keepalive()

    stream, rate, blocksize = open_stream()
    block_secs = blocksize / rate
    silence_blocks = int(SILENCE_SECS / block_secs)
    max_blocks = int(MAX_SECS / block_secs)
    tail_blocks = max(1, int(TAIL_KEEP_SECS / block_secs))

    try:
        threshold = calibrate(stream, blocksize)
        stop_threshold = threshold * STOP_FACTOR
        preroll = deque(maxlen=PREROLL_BLOCKS)
        print("Monster is awake. Speak to it...")

        while True:
            data, _ = stream.read(blocksize)
            if speaker_busy():             # a stored audio is playing on the speaker
                preroll.clear()
                continue
            preroll.append(data.copy())

            if rms(data) < threshold:
                continue

            # Someone started talking: record until they have been quiet for a while.
            # Stopping uses a LOWER level than starting, so soft words and endings
            # that trail off are not mistaken for silence.
            frames = list(preroll)
            quiet = 0
            interrupted = False
            overflows = 0
            while len(frames) < max_blocks and quiet < silence_blocks:
                data, overflowed = stream.read(blocksize)
                if speaker_busy():
                    interrupted = True
                    break
                overflows += bool(overflowed)
                frames.append(data.copy())
                quiet = quiet + 1 if rms(data) < stop_threshold else 0
            preroll.clear()
            if interrupted:
                continue

            reason = "silence" if quiet >= silence_blocks else "maximum length"
            keep = min(quiet, tail_blocks)        # keep a short natural tail, drop the rest
            if quiet > keep:
                frames = frames[:len(frames) - (quiet - keep)]
            if (len(frames) - keep) * block_secs < MIN_SECS:
                continue
            print(f"  recorded {len(frames) * block_secs:.1f} s, stopped on {reason} "
                  f"(start level {threshold:.0f}, stop level {stop_threshold:.0f})")
            if overflows:
                print(f"  !! {overflows} input overflow(s): audio was lost because the Pi "
                      "was too busy to read the mic in time")

            with tempfile.NamedTemporaryFile(suffix=".wav") as tmp:
                save_wav(tmp.name, frames, rate)
                if SAVE_RAW_RECORDING:
                    raw_dir = os.path.join(AUDIO_DIR, "raw")
                    os.makedirs(raw_dir, exist_ok=True)
                    shutil.copy(tmp.name, os.path.join(
                        raw_dir, datetime.now().strftime(_FILE_FORMAT) + ".wav"))
                print("Heard something, responding...")
                stream.stop()             # mute mic during processing and playback
                handle_clip(tmp.name)
                stream.start()

            time.sleep(0.3)               # let the room settle
    finally:
        stop_keepalive()
        stream.close()


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\nMonster sleeps.")
