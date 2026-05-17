#!/usr/bin/env python3
"""
SyncClip — Professional waveform sync tool for Premiere Pro
- Visual timeline like PluralEyes
- Smart filename-based device grouping
- Drag clips between device lanes to reassign
- Accurate Premiere XML export
"""

# ── Version — bump this number every time you upload a new version to GitHub ──
VERSION = "1.0"
GITHUB_RAW_URL = "https://raw.githubusercontent.com/hatchandsmith/syncclip/main/app.py"

import json
import os
import re
import subprocess
import sys
import tempfile
import threading
import time
from multiprocessing import Pool, cpu_count
from pathlib import Path
from urllib.parse import quote

import numpy as np
from scipy.signal import correlate

try:
    import tkinter as tk
    from tkinter import ttk, filedialog, messagebox
except ImportError:
    print("tkinter not found."); sys.exit(1)

try:
    from tkinterdnd2 import DND_FILES, TkinterDnD
    HAS_DND = True
except ImportError:
    HAS_DND = False

# ── Constants ──────────────────────────────────────────────────────────────────
SAMPLE_RATE = 16000
SUPPORTED   = {".mp4",".mov",".mxf",".avi",".mkv",
               ".mp3",".wav",".aac",".m4a",".aiff",".flac"}
AUDIO_EXT   = {".mp3",".wav",".aac",".m4a",".aiff",".flac"}

# ── ffmpeg / ffprobe path resolution ──────────────────────────────────────────
# When bundled as a .app via PyInstaller, the executables live next to the
# frozen binary (sys._MEIPASS). Fall back to PATH for normal script usage.

def _find_tool(name: str) -> str:
    """Return the best path for ffmpeg or ffprobe."""
    # 1. Bundled inside PyInstaller .app
    if getattr(sys, "frozen", False):
        bundle_dir = Path(sys._MEIPASS)  # type: ignore[attr-defined]
        candidate  = bundle_dir / name
        if candidate.exists():
            return str(candidate)
    # 2. Same folder as app.py (developer convenience)
    local = Path(__file__).parent / name
    if local.exists():
        return str(local)
    # 3. Homebrew default locations (Mac)
    for brew_path in [f"/opt/homebrew/bin/{name}", f"/usr/local/bin/{name}"]:
        if Path(brew_path).exists():
            return brew_path
    # 4. Rely on PATH
    return name

FFMPEG  = _find_tool("ffmpeg")
FFPROBE = _find_tool("ffprobe")

# ── Palette — Teenage Engineering: black, chalk, OP-1 orange ─────────────────
C_BG        = "#0A0A0A"   # near-black
C_BG2       = "#111111"   # panel
C_BG3       = "#181818"   # table / lane even
C_BG4       = "#222222"   # hover / selected
C_BORDER    = "#2A2A2A"   # subtle rule
C_AMBER     = "#FF6600"   # OP-1 orange
C_AMBER_D   = "#CC4400"   # pressed
C_CREAM     = "#E8E4DC"   # chalk white
C_CREAM_DIM = "#888880"   # secondary
C_CREAM_MUT = "#404040"   # muted / placeholder
C_GREEN     = "#00CC66"   # sync OK
C_YELLOW    = "#CCAA00"   # caution
C_RED       = "#CC2200"   # error
C_BLUE      = "#4488CC"   # anchor

# Lane colours — all within the TE palette: orange, dim, variants of same hue
LANE_COLORS = [
    ("#FF6600", "#2A1200"),   # OP-1 orange
    ("#CC4400", "#1E0A00"),   # burnt orange
    ("#FF8833", "#2E1500"),   # light orange
    ("#AA3300", "#180800"),   # dark rust
    ("#FF5500", "#280F00"),   # red-orange
    ("#884400", "#120800"),   # deep amber
]

# ── Fonts — monospace everything, like TE product displays ────────────────────
F_DISPLAY = ("Menlo",  15, "bold")   # logo / titles
F_LABEL   = ("Menlo",  11)
F_LABEL_B = ("Menlo",  11, "bold")
F_SMALL   = ("Menlo",  10)
F_MONO_SM = ("Menlo",  10)

# ── Custom white hand cursor ───────────────────────────────────────────────────
# XBM bitmaps written to a temp dir on first use, then referenced via tkinter's
# "@path" cursor syntax. Shape = white, mask = black outline.

_HAND_XBM = """\
#define cursor_width 16
#define cursor_height 16
#define cursor_x_hot 5
#define cursor_y_hot 0
static unsigned char cursor_bits[] = {
  0x18, 0x00, 0x34, 0x00, 0x34, 0x00, 0x34, 0x00, 0xb4, 0x0d, 0xb4, 0x0d,
  0xb5, 0x0d, 0xf7, 0x0f, 0xff, 0x0f, 0xff, 0x0f, 0xfe, 0x0f, 0xfe, 0x0f,
  0xfe, 0x07, 0xfc, 0x07, 0xfc, 0x03, 0x00, 0x00
};"""

_HAND_MASK_XBM = """\
#define mask_width 16
#define mask_height 16
#define mask_x_hot 5
#define mask_y_hot 0
static unsigned char mask_bits[] = {
  0x18, 0x00, 0x3c, 0x00, 0x3c, 0x00, 0xbc, 0x0d, 0xfc, 0x1f, 0xfc, 0x1f,
  0xff, 0x1f, 0xff, 0x1f, 0xff, 0x1f, 0xff, 0x1f, 0xfe, 0x1f, 0xfe, 0x1f,
  0xfe, 0x0f, 0xfc, 0x0f, 0xfc, 0x03, 0x00, 0x00
};"""

_CURSOR_DIR  = Path(tempfile.gettempdir()) / "syncclip_cursors"
_CURSOR_PATH = _CURSOR_DIR / "hand.xbm"
_MASK_PATH   = _CURSOR_DIR / "hand_mask.xbm"
_HAND_CURSOR = None   # set on first call to _get_hand_cursor()

def _get_hand_cursor():
    """Return tkinter cursor spec for the custom white hand. Falls back to hand2."""
    global _HAND_CURSOR
    if _HAND_CURSOR is not None:
        return _HAND_CURSOR
    try:
        _CURSOR_DIR.mkdir(parents=True, exist_ok=True)
        _CURSOR_PATH.write_text(_HAND_XBM)
        _MASK_PATH.write_text(_HAND_MASK_XBM)
        _HAND_CURSOR = (f"@{_CURSOR_PATH}", str(_MASK_PATH), "white", "black")
    except Exception:
        _HAND_CURSOR = "hand2"   # safe fallback
    return _HAND_CURSOR

# ── Audio/device keyword hints ─────────────────────────────────────────────────
AUDIO_KW = {"audio","sound","lav","lavmic","boom","recorder","zoom","tascam",
             "h4n","h5","h6","dr","mic","mix","field","ambience","ambient","atmos"}

def guess_device_type(path: Path) -> str:
    if path.suffix.lower() in AUDIO_EXT: return "audio"
    for kw in AUDIO_KW:
        if kw in path.stem.lower(): return "audio"
    return "camera"

def filename_signature(path: Path) -> str:
    """
    Extract the 'base camera signature' from a filename.
    e.g. A7III_0042.MP4 → 'a7iii'
         GH5_clip001.mov → 'gh5'
         ZOOM_001.wav    → 'zoom'
         interview_cam2_take3.mp4 → 'interview_cam2'
    Strategy: strip trailing numeric sequences and common take/clip suffixes.
    """
    stem = path.stem
    # Remove trailing numbers, underscores, 'take', 'clip', 'scene', 'part'
    sig = re.sub(r'[\-_]*(take|clip|scene|part|cut|reel|roll|seq|sequence)[\-_]*\d*$', '',
                 stem, flags=re.IGNORECASE)
    sig = re.sub(r'[\-_]*\d+$', '', sig)
    sig = sig.strip("_- ").lower()
    return sig if sig else stem.lower()


# ── Sync engine ────────────────────────────────────────────────────────────────

def _count_audio_channels(clip_path: str) -> int:
    """Return the number of audio channels in a file."""
    try:
        cmd = [FFPROBE,"-v","error",
               "-select_streams","a:0",
               "-show_entries","stream=channels",
               "-of","default=noprint_wrappers=1:nokey=1",
               clip_path]
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=10)
        val = r.stdout.strip()
        return int(val) if val else 1
    except Exception:
        return 1

def extract_audio_channel(clip_path: str, channel: int = 0,
                          sample_rate: int = SAMPLE_RATE) -> np.ndarray:
    """
    Extract a single audio channel as float32.
    Uses 'pan' filter to pick a specific channel index.
    Falls back to simple mono downmix if channel index is 0.
    No loudnorm — we normalise manually after so both signals stay comparable.
    """
    if channel == 0:
        # Downmix all channels to mono — good for room audio
        af = "aresample=resampler=swr"
        mix = ["-ac","1"]
    else:
        # Pick a specific channel by index (0-based pan filter)
        af = f"pan=mono|c0=c{channel},aresample=resampler=swr"
        mix = ["-ac","1"]

    cmd = [FFMPEG,"-i", clip_path,
           "-af", af,
           "-ar", str(sample_rate),
           ] + mix + [
           "-f","f32le","-",
           "-loglevel","error","-nostdin"]
    r = subprocess.run(cmd, capture_output=True)
    if r.returncode != 0:
        raise RuntimeError(r.stderr.decode())
    audio = np.frombuffer(r.stdout, dtype=np.float32)
    # Manual peak normalise (safe — avoids loudnorm distortion on quiet clips)
    peak = np.max(np.abs(audio))
    if peak > 0:
        audio = audio / peak
    return audio

def extract_audio(clip_path) -> np.ndarray:
    """Simple mono extract used for the anchor — downmixes all channels."""
    return extract_audio_channel(str(clip_path), channel=0)

def _correlate_pair(a: np.ndarray, b: np.ndarray,
                    sample_rate: int) -> tuple[float, float]:
    """
    FFT cross-correlation between two mono signals.
    Returns (offset_seconds, confidence).
    Confidence is the normalised peak correlation value.
    """
    cap = sample_rate * 600   # max 10 minutes per clip
    a = a[:cap].astype(np.float64)
    b = b[:cap].astype(np.float64)

    corr  = correlate(a, b, mode="full", method="fft")
    lag   = np.argmax(corr) - (len(b) - 1)
    offset = lag / sample_rate

    na, nb = np.linalg.norm(a), np.linalg.norm(b)
    if na == 0 or nb == 0:
        return offset, 0.0
    conf = float(np.max(corr) / (na * nb))
    conf = min(max(conf, 0.0), 1.0)
    return offset, conf

def compute_offset(args):
    """
    Worker: try syncing clip against anchor using multiple strategies.
    Strategy 1: mono downmix of all channels (catches room audio)
    Strategy 2: each individual channel (catches dedicated recorder feeds)
    Returns the best result across all attempts.
    Best = highest confidence score.
    """
    clip_str, anchor_audio, sr = args
    best_offset = 0.0
    best_conf   = 0.0
    last_error  = None

    try:
        n_channels = _count_audio_channels(clip_str)
        channels_to_try = list(dict.fromkeys([0] + list(range(n_channels))))
        # channel 0 = mono downmix, then individual channels 0,1,2…

        for ch in channels_to_try:
            try:
                clip_audio = extract_audio_channel(clip_str, ch, sr)
            except RuntimeError as e:
                last_error = str(e)
                continue

            offset, conf = _correlate_pair(anchor_audio, clip_audio, sr)

            if conf > best_conf:
                best_conf   = conf
                best_offset = offset

            # Good enough — stop trying more channels
            if best_conf >= 0.5:
                break

    except Exception as e:
        return (clip_str, None, 0.0, str(e))

    if best_conf == 0.0 and last_error:
        return (clip_str, None, 0.0, last_error)

    return (clip_str, best_offset, best_conf, None)

def to_tc(seconds, fps=29.97):
    if seconds is None: return "—"
    tf   = round(abs(seconds)*fps)
    sign = "-" if seconds < 0 else "+"
    ff   = tf % round(fps)
    ss   = (tf//round(fps)) % 60
    mm   = (tf//round(fps)//60) % 60
    hh   =  tf//round(fps)//3600
    return f"{sign}{hh:02d}:{mm:02d}:{ss:02d}:{ff:02d}"


# ── Styled button ──────────────────────────────────────────────────────────────

class Btn(tk.Frame):
    STYLES = {
        "primary": (C_AMBER,    "#0A0A0A",   C_AMBER_D),
        "normal":  (C_BG3,      C_CREAM,     C_BG4),
        "ghost":   (C_BG2,      C_CREAM_DIM, C_AMBER),   # hover → orange
        "danger":  ("#2A0808",  C_RED,       "#3A1010"),
    }
    def __init__(self, parent, text, cmd, style="normal", **kw):
        super().__init__(parent, bg=parent.cget("bg"), **kw)
        self._cmd   = cmd
        self._style = style
        bg_n, fg_n, bg_h = self.STYLES.get(style, self.STYLES["normal"])
        self._bg, self._bg_h, self._fg_n = bg_n, bg_h, fg_n
        # ghost hover also changes text colour to black for contrast on orange
        self._fg_h = "#0A0A0A" if style == "ghost" else fg_n
        self._hand_cur = _get_hand_cursor()
        self._lbl = tk.Label(self, text=text, bg=bg_n, fg=fg_n,
                             font=F_LABEL_B, padx=16, pady=8,
                             cursor=self._hand_cur)
        self._lbl.pack()
        self._lbl.bind("<Enter>",    self._on_enter)
        self._lbl.bind("<Leave>",    self._on_leave)
        self._lbl.bind("<Button-1>", self._on_click)
        self._lbl.bind("<ButtonRelease-1>", self._on_release_click)

    def _on_enter(self, e=None):
        self._lbl.config(bg=self._bg_h, fg=self._fg_h)

    def _on_leave(self, e=None):
        self._lbl.config(bg=self._bg, fg=self._fg_n)

    def _on_click(self, e=None):
        self._lbl.config(bg=C_CREAM, fg="#0A0A0A")
        # Defer by 1ms — lets the click event fully resolve before any dialog opens
        self._lbl.after(1, self._cmd)

    def _on_release_click(self, e=None):
        # Snap back to hover state (mouse is still over it)
        self._lbl.config(bg=self._bg_h, fg=self._fg_h)

    def set_text(self, t): self._lbl.config(text=t)
    def enable(self, on):
        if on:
            self._lbl.config(bg=self._bg, fg=self._fg_n, cursor=self._hand_cur)
            self._lbl.bind("<Enter>",           self._on_enter)
            self._lbl.bind("<Leave>",           self._on_leave)
            self._lbl.bind("<Button-1>",        self._on_click)
            self._lbl.bind("<ButtonRelease-1>", self._on_release_click)
        else:
            self._lbl.config(bg=C_BG2, fg=C_CREAM_MUT, cursor="arrow")
            for ev in ("<Enter>","<Leave>","<Button-1>","<ButtonRelease-1>"):
                self._lbl.unbind(ev)


# ── Timeline Canvas ────────────────────────────────────────────────────────────

LANE_H      = 44    # px height of each device lane
RULER_H     = 26    # px height of timecode ruler
LABEL_W     = 130   # px width of left device-label column
MIN_BAR_W   = 6     # minimum clip bar width in px

class Timeline(tk.Frame):
    """
    Draws device lanes + clip bars on a canvas.
    Supports drag-and-drop reassignment between lanes.
    Two-finger trackpad scrolling. Scrollbar auto-hides when not needed.
    """
    def __init__(self, parent, app, **kw):
        super().__init__(parent, bg=C_BG2, **kw)
        self.app = app

        # Label column (fixed left)
        self.label_canvas = tk.Canvas(self, bg=C_BG2, width=LABEL_W,
                                      highlightthickness=0, bd=0)
        self.label_canvas.pack(side="left", fill="y")

        # Right side: canvas + optional scrollbar stacked vertically
        self._right = tk.Frame(self, bg=C_BG2)
        self._right.pack(side="left", fill="both", expand=True)

        self.canvas = tk.Canvas(self._right, bg=C_BG3, highlightthickness=0, bd=0)
        self.canvas.pack(fill="both", expand=True)

        # Scrollbar — hidden by default, shown only when content overflows
        self.hbar = ttk.Scrollbar(self._right, orient="horizontal",
                                  command=self.canvas.xview)
        self.canvas.configure(xscrollcommand=self._on_xscroll)
        self._hbar_visible = False

        # Drag state
        self._drag_item      = None
        self._drag_clip      = None
        self._drag_start     = (0, 0)
        self._drag_orig_lane = None

        self.canvas.bind("<ButtonPress-1>",   self._on_press)
        self.canvas.bind("<B1-Motion>",       self._on_drag)
        self.canvas.bind("<ButtonRelease-1>", self._on_release)
        self.canvas.bind("<Configure>",       lambda e: self._redraw())

        # Two-finger trackpad horizontal scroll (macOS sends MouseWheel on X axis)
        self.canvas.bind("<MouseWheel>",   self._on_mousewheel_y)
        self.canvas.bind("<Shift-MouseWheel>", self._on_mousewheel_x)
        # macOS trackpad two-finger swipe fires as Button-4/5 on some tk builds
        self.canvas.bind("<Button-4>",  lambda e: self.canvas.xview_scroll(-1, "units"))
        self.canvas.bind("<Button-5>",  lambda e: self.canvas.xview_scroll( 1, "units"))

        self._pixels_per_sec = 50.0
        self._total_secs     = 60.0
        self._zoom_level     = 1.0   # 1.0 = fit-to-width; >1 = zoomed in

        # Waveform cache: str(path) → np.ndarray peak envelope (0..1), or None if failed
        self._waveform_cache   = {}
        self._waveform_loading = set()   # paths currently being extracted

        # Ctrl+scroll or Command+scroll → zoom in/out
        self.canvas.bind("<Control-MouseWheel>", self._on_zoom)
        self.canvas.bind("<Command-MouseWheel>", self._on_zoom)

    def _on_zoom(self, event):
        factor = 1.15 if event.delta > 0 else (1/1.15)
        self._zoom_level = max(1.0, min(self._zoom_level * factor, 30.0))
        self._apply_zoom()

    def _apply_zoom(self):
        canvas_w = self.canvas.winfo_width() or 800
        fit_pps  = max(4.0, (canvas_w - 20) / max(self._total_secs, 1.0))
        self._pixels_per_sec = fit_pps * self._zoom_level
        self._redraw()

    # ── Waveform extraction ────────────────────────────────────────────────────

    def request_waveform(self, clip_path: Path):
        """
        Start background extraction of waveform envelope for clip_path.
        When done, schedules a redraw via root.after.
        No-op if already cached or in progress.
        """
        key = str(clip_path)
        if key in self._waveform_cache or key in self._waveform_loading:
            return
        self._waveform_loading.add(key)
        threading.Thread(target=self._extract_waveform_worker,
                         args=(clip_path,), daemon=True).start()

    def _extract_waveform_worker(self, clip_path: Path):
        """
        Background: extract peak envelope using ffmpeg raw PCM.
        Produces ~800 values (one per visual column of a full-width bar).
        """
        key = str(clip_path)
        try:
            # Extract mono audio at very low sample rate — enough for visual envelope
            # 400 Hz gives ~1 sample per 2.5ms — plenty for a waveform thumbnail
            cmd = [FFMPEG, "-i", str(clip_path),
                   "-ac", "1", "-ar", "400",
                   "-f", "f32le", "-",
                   "-loglevel", "error", "-nostdin"]
            r = subprocess.run(cmd, capture_output=True, timeout=30)
            if r.returncode != 0 or not r.stdout:
                self._waveform_cache[key] = None
                return

            raw = np.frombuffer(r.stdout, dtype=np.float32)
            if len(raw) == 0:
                self._waveform_cache[key] = None
                return

            # Build peak envelope: divide into N buckets, take max abs per bucket
            N = 800   # target number of envelope points
            bucket = max(1, len(raw) // N)
            trimmed = raw[:len(raw) - (len(raw) % bucket)]
            if len(trimmed) == 0:
                trimmed = raw
            peaks = np.abs(trimmed.reshape(-1, bucket)).max(axis=1)

            # Normalise to 0..1
            mx = peaks.max()
            if mx > 0:
                peaks = peaks / mx

            self._waveform_cache[key] = peaks.astype(np.float32)

        except Exception:
            self._waveform_cache[key] = None
        finally:
            self._waveform_loading.discard(key)
            # Trigger a redraw on the main thread
            try:
                self.canvas.after(0, self._redraw)
            except Exception:
                pass

    def _draw_waveform(self, x1: int, x2: int, y_top: int, y_bot: int,
                       clip_path: Path, color_bar: str, unsynced: bool):
        """
        Draw a mini waveform inside the clip bar bounds.
        Uses cached envelope data — no-ops if not ready yet.
        """
        key = str(clip_path)
        envelope = self._waveform_cache.get(key)
        if envelope is None or len(envelope) == 0:
            return

        bar_w = x2 - x1
        bar_h = y_bot - y_top
        pad   = 6   # vertical padding inside bar
        mid_y = (y_top + y_bot) / 2
        draw_h = (bar_h / 2) - pad   # half-height available for waveform

        if bar_w < 4 or draw_h < 2:
            return

        # Sample envelope to bar width (one point per pixel column)
        n_points = max(2, bar_w)
        indices  = np.linspace(0, len(envelope) - 1, n_points).astype(int)
        sampled  = envelope[indices]

        # Build polygon points: top half mirror of bottom half
        # Points go left→right across top, then right→left across bottom
        pts = []
        for i, amp in enumerate(sampled):
            px = x1 + i
            h  = amp * draw_h
            pts.append((px, mid_y - h))

        for i, amp in enumerate(reversed(sampled)):
            px = x2 - i
            h  = amp * draw_h
            pts.append((px, mid_y + h))

        if len(pts) < 3:
            return

        # Flatten to tkinter polygon format
        flat = [coord for pt in pts for coord in pt]

        # Waveform fill: slightly lighter/darker than bar colour
        wv_fill  = "#FFFFFF22" if not unsynced else "#FFFFFF0A"
        wv_out   = color_bar

        try:
            self.canvas.create_polygon(
                flat,
                fill=wv_fill, outline="",
                smooth=True,
                tags=(f"clip_{id(clip_path)}",)
            )
        except Exception:
            pass   # polygon needs ≥3 points — already checked but guard anyway

    def _on_xscroll(self, first, last):
        """Auto-show/hide the horizontal scrollbar based on whether content overflows."""
        first, last = float(first), float(last)
        if first <= 0.0 and last >= 1.0:
            # Content fits — hide scrollbar
            if self._hbar_visible:
                self.hbar.pack_forget()
                self._hbar_visible = False
        else:
            # Content overflows — show scrollbar
            if not self._hbar_visible:
                self.hbar.pack(fill="x")
                self._hbar_visible = True
        self.hbar.set(first, last)

    def _on_mousewheel_y(self, event):
        """Vertical mousewheel — treat as horizontal scroll on the timeline."""
        self.canvas.xview_scroll(int(-event.delta / 20), "units")

    def _on_mousewheel_x(self, event):
        """Shift+scroll — also horizontal."""
        self.canvas.xview_scroll(int(-event.delta / 20), "units")

    # ── Public API ─────────────────────────────────────────────────────────────

    def draw(self, devices: list, clips_by_device: dict,
             results_by_path: dict, total_secs: float):
        self._devices         = devices
        self._clips_by_device = clips_by_device
        self._results         = results_by_path
        self._total_secs      = max(total_secs, 10.0)
        self._zoom_level      = 1.0   # reset to fit-to-width on new data
        self._apply_zoom()

    def _redraw(self):
        if not hasattr(self, "_devices"): return
        self.canvas.delete("all")
        self.label_canvas.delete("all")

        # Recalculate pps to respect current zoom (fit-to-width × zoom_level)
        canvas_w_vis = self.canvas.winfo_width() or 800
        fit_pps      = max(4.0, (canvas_w_vis - 20) / max(self._total_secs, 1.0))
        self._pixels_per_sec = fit_pps * getattr(self, "_zoom_level", 1.0)

        n_lanes  = len(self._devices)
        total_h  = RULER_H + n_lanes * LANE_H + 10
        canvas_w = max(int(self._total_secs * self._pixels_per_sec) + 40, canvas_w_vis)
        self.canvas.configure(scrollregion=(0, 0, canvas_w, total_h))

        self._draw_ruler(canvas_w)
        for i, dev_label in enumerate(self._devices):
            self._draw_lane(i, dev_label, canvas_w)

    def _draw_ruler(self, canvas_w):
        # Ruler background
        self.canvas.create_rectangle(0, 0, canvas_w, RULER_H,
                                     fill=C_BG2, outline="")
        # Tick marks — pick a sensible interval
        pps = self._pixels_per_sec
        intervals = [1,2,5,10,15,30,60,120,300]
        interval  = next((i for i in intervals if i*pps >= 60), 300)

        t = 0.0
        while t <= self._total_secs + interval:
            x = int(t * pps)
            self.canvas.create_line(x, RULER_H-8, x, RULER_H,
                                    fill=C_CREAM_MUT, width=1)
            label = self._fmt_time(t)
            self.canvas.create_text(x+3, RULER_H//2, text=label,
                                    anchor="w", fill=C_CREAM_DIM,
                                    font=F_MONO_SM)
            t += interval

        # Ruler bottom border
        self.canvas.create_line(0, RULER_H, canvas_w, RULER_H,
                                fill=C_BORDER, width=1)

    def _draw_lane(self, index: int, dev_label: str, canvas_w: int):
        y_top = RULER_H + index * LANE_H
        y_bot = y_top + LANE_H
        color_bar, color_dark = LANE_COLORS[index % len(LANE_COLORS)]

        # Lane background — alternating subtle tones
        lane_bg = C_BG3 if index % 2 == 0 else C_BG2
        self.canvas.create_rectangle(0, y_top, canvas_w, y_bot,
                                     fill=lane_bg, outline="")
        self.canvas.create_line(0, y_bot, canvas_w, y_bot,
                                fill=C_BORDER, width=1)

        # Left label panel
        lbl_bg = C_BG2 if index % 2 == 0 else C_BG3
        self.label_canvas.create_rectangle(0, y_top, LABEL_W, y_bot,
                                           fill=lbl_bg, outline="")
        self.label_canvas.create_line(0, y_bot, LABEL_W, y_bot,
                                      fill=C_BORDER, width=1)

        # Colour swatch
        self.label_canvas.create_rectangle(8, y_top+12, 14, y_bot-12,
                                           fill=color_bar, outline="")

        # Device name (truncated)
        short = dev_label if len(dev_label) <= 14 else dev_label[:13]+"…"
        self.label_canvas.create_text(20, y_top + LANE_H//2,
                                      text=short, anchor="w",
                                      fill=C_CREAM, font=F_LABEL_B)

        # Draw clips for this lane
        clips = self._clips_by_device.get(dev_label, [])
        for clip_path in clips:
            r = self._results.get(str(clip_path))
            if not r: continue
            self._draw_clip_bar(clip_path, r, y_top, y_bot,
                                color_bar, color_dark, index)

    def _draw_clip_bar(self, clip_path, result, y_top, y_bot,
                       color_bar, color_dark, lane_idx):
        pps      = self._pixels_per_sec
        offset   = result.get("offset_seconds") or 0.0
        dur      = result.get("duration_secs")  or max(self._total_secs * 0.1, 5.0)
        conf     = result.get("confidence", 0.0)
        unsynced = result.get("unsynced", False)

        x1 = int(offset * pps)
        x2 = max(x1 + MIN_BAR_W, int((offset + dur) * pps))
        pad = 5

        # Bar fill
        fill = color_dark if unsynced else color_bar
        tag  = f"clip_{id(clip_path)}"

        # Shadow
        self.canvas.create_rectangle(x1+2, y_top+pad+2, x2+2, y_bot-pad+2,
                                     fill="#000000", outline="", tags=(tag,))
        # Main bar
        self.canvas.create_rectangle(x1, y_top+pad, x2, y_bot-pad,
                                     fill=fill, outline=color_bar,
                                     width=1, tags=(tag,))

        # Waveform — drawn on top of bar fill, clipped to bar bounds
        self._draw_waveform(x1, x2, y_top+pad, y_bot-pad,
                            clip_path, color_bar, unsynced)
        # Kick off background extraction if not yet cached
        self.request_waveform(clip_path)

        # Confidence pip — small coloured dot top-right of bar
        if not unsynced and (x2 - x1) > 16:
            pip = C_GREEN if conf >= 0.4 else (C_YELLOW if conf >= 0.1 else C_RED)
            self.canvas.create_oval(x2-10, y_top+pad+3, x2-4, y_top+pad+9,
                                    fill=pip, outline="", tags=(tag,))

        # Clip name label (only if bar is wide enough)
        bar_w = x2 - x1
        if bar_w > 30:
            name  = clip_path.stem
            chars = max(1, (bar_w - 8) // 6)
            label = name if len(name) <= chars else name[:chars-1]+"…"
            self.canvas.create_text(x1+5, y_top + LANE_H//2,
                                    text=label, anchor="w",
                                    fill=C_CREAM if not unsynced else C_CREAM_MUT,
                                    font=F_MONO_SM, tags=(tag,))

        # Store tag → (clip_path, lane_idx) for drag
        self.canvas.tag_bind(tag, "<Enter>",
                             lambda e, p=clip_path, r=result: self._on_hover(p, r))
        self.canvas.tag_bind(tag, "<Leave>",  lambda e: self._on_leave())

        # Store clip metadata on canvas item for drag
        for item in self.canvas.find_withtag(tag):
            self.canvas.itemconfigure(item, tags=(tag, f"lane_{lane_idx}",
                                                   f"path_{id(clip_path)}"))
        self._clip_tag_map = getattr(self, "_clip_tag_map", {})
        self._clip_tag_map[tag] = (clip_path, lane_idx)

    def _fmt_time(self, seconds: float) -> str:
        m = int(seconds) // 60
        s = int(seconds) % 60
        return f"{m}:{s:02d}"

    # ── Hover tooltip ──────────────────────────────────────────────────────────

    def _on_hover(self, clip_path, result):
        conf  = result.get("confidence", 0)
        off   = result.get("offset_seconds", 0)
        status = result.get("status_label","—")
        tip   = f"{clip_path.name}  |  {to_tc(off)}  |  {status}  ({conf*100:.0f}%)"
        self.app.status_var.set(tip)

    def _on_leave(self):
        self.app.status_var.set("READY")

    # ── Drag to reassign ───────────────────────────────────────────────────────

    def _on_press(self, event):
        cx = self.canvas.canvasx(event.x)
        cy = self.canvas.canvasy(event.y)
        items = self.canvas.find_overlapping(cx-2, cy-2, cx+2, cy+2)
        if not items: return
        # Find topmost item that belongs to a clip
        for item in reversed(items):
            tags = self.canvas.gettags(item)
            clip_tag = next((t for t in tags if t.startswith("clip_")), None)
            if clip_tag and clip_tag in getattr(self,"_clip_tag_map",{}):
                self._drag_item  = item
                self._drag_tag   = clip_tag
                self._drag_start = (cx, cy)
                clip_path, lane_idx = self._clip_tag_map[clip_tag]
                self._drag_clip      = clip_path
                self._drag_orig_lane = lane_idx
                self.canvas.config(cursor="fleur")
                return

    def _on_drag(self, event):
        if self._drag_item is None: return
        cy = self.canvas.canvasy(event.y)
        # Highlight the lane the cursor is over
        lane = self._y_to_lane(cy)
        if lane is not None and lane != self._drag_orig_lane:
            self.canvas.config(cursor="exchange")
        else:
            self.canvas.config(cursor="fleur")

    def _on_release(self, event):
        if self._drag_clip is None:
            self._drag_item = None; return
        cy   = self.canvas.canvasy(event.y)
        lane = self._y_to_lane(cy)
        if lane is not None and lane != self._drag_orig_lane:
            # Reassign clip to new device
            old_label = self._devices[self._drag_orig_lane]
            new_label = self._devices[lane]
            self.app.reassign_clip(self._drag_clip, old_label, new_label)
        self._drag_item = None; self._drag_clip = None
        self.canvas.config(cursor="")

    def _y_to_lane(self, cy: float):
        idx = int((cy - RULER_H) / LANE_H)
        if 0 <= idx < len(getattr(self,"_devices",[])):
            return idx
        return None

    def animate_clip_to(self, clip_path: Path, new_offset: float,
                        duration_secs: float, confidence: float):
        """
        Smoothly slide a clip bar to its synced position.
        Called from the main thread (via root.after) as each clip result arrives.
        """
        tag = f"clip_{id(clip_path)}"
        items = self.canvas.find_withtag(tag)
        if not items:
            return  # clip not drawn yet — will appear on full redraw

        pps = self._pixels_per_sec
        target_x1 = int(new_offset * pps)
        dur_px     = max(MIN_BAR_W, int(duration_secs * pps))

        # Get current x position of the first rect in the tag group
        try:
            coords = self.canvas.coords(items[0])
            if not coords: return
            current_x1 = int(coords[0])
        except Exception:
            return

        # Pick colour based on confidence
        _, color_dark = LANE_COLORS[0]   # fallback
        meta = getattr(self, "_clip_tag_map", {}).get(tag)
        if meta:
            _, lane_idx = meta
            color_bar, color_dark = LANE_COLORS[lane_idx % len(LANE_COLORS)]
        else:
            color_bar = C_AMBER

        fill = color_bar if confidence >= 0.04 else color_dark

        # Animate: 8 steps over ~200ms
        steps = 8
        delta = (target_x1 - current_x1) / steps

        def _step(n, cur_x):
            if n <= 0:
                # Final position — redraw cleanly
                self._update_clip_bar_position(items, cur_x, dur_px, fill)
                return
            next_x = cur_x + delta
            self._update_clip_bar_position(items, int(next_x), dur_px, fill)
            self.canvas.after(25, lambda: _step(n-1, next_x))

        _step(steps, current_x1)

    def _update_clip_bar_position(self, items, x1: int, dur_px: int, fill: str):
        """Move all canvas items belonging to a clip tag to a new x1 position."""
        if not items: return
        try:
            # Items: [shadow_rect, main_rect, (pip oval), (text)]
            # We reposition by computing dx from the first item
            coords = self.canvas.coords(items[0])
            if not coords: return
            old_x1 = coords[0]
            dx = x1 - old_x1
            for item in items:
                self.canvas.move(item, dx, 0)
            # Update fill on the main bar (second item = main rect)
            if len(items) > 1:
                self.canvas.itemconfig(items[1], fill=fill)
        except Exception:
            pass


# ── Main App ───────────────────────────────────────────────────────────────────

class App:
    def __init__(self):
        self.root = TkinterDnD.Tk() if HAS_DND else tk.Tk()
        self.root.title("SyncClip")
        self.root.configure(bg=C_BG)
        self.root.resizable(True, True)
        self.root.minsize(860, 600)

        # ── Center on screen ──────────────────────────────────────────────────
        w, h = 1100, 820
        self.root.update_idletasks()
        sw = self.root.winfo_screenwidth()
        sh = self.root.winfo_screenheight()
        x  = (sw - w) // 2
        y  = (sh - h) // 2
        self.root.geometry(f"{w}x{h}+{x}+{y}")

        # ── Data model ──
        self.clips      = []    # [Path] in add order
        self.clip_meta  = {}    # str(path) → {device_type, device_label, signature, duration_secs}

        # Device registry
        self.devices    = []    # ordered list of device labels (str)
        self.device_type= {}    # label → "camera"|"audio"

        # Clips per device (for timeline)
        self.clips_by_device = {}   # label → [Path]

        self.results    = []    # list of result dicts after sync
        self.results_by_path = {}  # str(path) → result dict

        self.anchor_var = tk.StringVar()
        self.fps_var    = tk.StringVar(value="23.976")
        self.running    = False

        self._build()
        self._style_widgets()

    # ── UI Construction ────────────────────────────────────────────────────────

    def _build(self):
        # ── Topbar ──
        top = tk.Frame(self.root, bg=C_BG2,
                       highlightbackground=C_BORDER, highlightthickness=1)
        top.pack(fill="x", side="top")
        ti = tk.Frame(top, bg=C_BG2)
        ti.pack(fill="x", padx=22, pady=10)

        tk.Label(ti, text="SyncClip", font=F_DISPLAY,
                 bg=C_BG2, fg=C_AMBER).pack(side="left")
        tk.Label(ti, text="  /  waveform sync",
                 font=F_SMALL, bg=C_BG2, fg=C_CREAM_MUT).pack(side="left", pady=2)

        # Persistent completion indicator — hidden until sync finishes
        self.done_indicator = tk.Label(ti, text="  [OK] SYNC COMPLETE",
                                       font=F_LABEL_B, bg=C_BG2, fg=C_GREEN)
        # not packed yet — shown on sync complete

        rc = tk.Frame(ti, bg=C_BG2); rc.pack(side="right")

        def combo_field(parent, lbl, var, vals, w):
            tk.Label(parent, text=lbl, font=F_SMALL,
                     bg=C_BG2, fg=C_CREAM_DIM).pack(side="left", padx=(0,4))
            f = tk.Frame(parent, bg=C_BG3,
                         highlightbackground=C_BORDER, highlightthickness=1)
            f.pack(side="left", padx=(0,14))
            cb = ttk.Combobox(f, textvariable=var, values=vals,
                              width=w, font=F_MONO_SM, state="readonly")
            cb.pack(padx=2, pady=2)
            return cb

        combo_field(rc, "FPS", self.fps_var,
                    ["23.976","24","25","29.97","30","59.94","60"], 6)
        self.anchor_combo = combo_field(rc, "Anchor", self.anchor_var,
                                        ["Auto (largest file)"], 24)

        # Version + update button (far right of topbar)
        tk.Label(rc, text=f"v{VERSION}", font=F_SMALL,
                 bg=C_BG2, fg=C_CREAM_MUT).pack(side="left", padx=(0, 8))
        self.update_btn = tk.Label(rc, text="[ UPDATE ]",
                                   font=F_SMALL, bg=C_BG2, fg=C_CREAM_MUT,
                                   padx=8, pady=4, cursor=_get_hand_cursor())
        self.update_btn.pack(side="left")
        self.update_btn.bind("<Enter>",    lambda e: self.update_btn.config(bg=C_AMBER, fg="#0A0A0A"))
        self.update_btn.bind("<Leave>",    lambda e: self.update_btn.config(bg=C_BG2,   fg=C_CREAM_MUT))
        self.update_btn.bind("<Button-1>", lambda e: self.root.after(1, self._check_for_update))

        # ── Bottom bar (pack from bottom so it's always visible) ──
        bb = tk.Frame(self.root, bg=C_BG2,
                      highlightbackground=C_BORDER, highlightthickness=1)
        bb.pack(fill="x", side="bottom")
        bbi = tk.Frame(bb, bg=C_BG2)
        bbi.pack(fill="x", padx=22, pady=10)

        self.run_btn = Btn(bbi, "[ RUN SYNC ]", self._start_sync, "primary")
        self.run_btn.pack(side="left", padx=(0,10))

        self.export_btn = Btn(bbi, "[ EXPORT XML ]", self._export_xml, "ghost")
        self.export_btn.pack(side="left")
        self.export_btn.enable(False)

        self.status_var = tk.StringVar(value="READY")
        self.status_bar = tk.Label(bbi, textvariable=self.status_var, font=F_SMALL,
                 bg=C_BG2, fg=C_CREAM_DIM, anchor="e")
        self.status_bar.pack(side="right")

        # Progress bar (hidden until sync)
        self.progress = ttk.Progressbar(self.root, mode="determinate")

        # ── Main paned area (top: clip list + drop zone, bottom: timeline) ──
        self.paned = tk.PanedWindow(self.root, orient="vertical",
                                    bg=C_BG, sashwidth=6,
                                    sashrelief="flat", sashpad=0,
                                    handlepad=60, handlesize=8)
        self.paned.pack(fill="both", expand=True, padx=0, pady=0)

        # ── Top pane: drop zone + clip table ──
        top_pane = tk.Frame(self.paned, bg=C_BG)
        self.paned.add(top_pane, minsize=180, stretch="always")

        # Drop zone
        dz_outer = tk.Frame(top_pane, bg=C_BG, padx=18, pady=10)
        dz_outer.pack(fill="x")

        dz = tk.Frame(dz_outer, bg=C_BG2,
                      highlightbackground=C_BORDER, highlightthickness=1)
        dz.pack(fill="x")
        dzi = tk.Frame(dz, bg=C_BG2)
        dzi.pack(pady=14, padx=20)

        tk.Label(dzi, text="[ DROP ]", font=("Helvetica Neue",26),
                 bg=C_BG2, fg=C_AMBER).pack()
        tk.Label(dzi,
                 text="DROP FILES HERE",
                 font=("Georgia",12), bg=C_BG2, fg=C_CREAM).pack(pady=(4,2))
        tk.Label(dzi,
                 text="files stay in place  /  mp4  mov  mxf  wav  aiff  mp3  m4a  flac",
                 font=F_SMALL, bg=C_BG2, fg=C_CREAM_MUT).pack(pady=(0,8))

        br = tk.Frame(dzi, bg=C_BG2); br.pack()
        Btn(br, "[+] ADD FILES",  self._browse_files,  "normal").pack(side="left", padx=4)
        Btn(br, "[+] ADD FOLDER", self._browse_folder, "normal").pack(side="left", padx=4)
        Btn(br, "[x] CLEAR",   self._clear,          "danger").pack(side="left", padx=4)

        if HAS_DND:
            for w in (dz, dzi):
                w.drop_target_register(DND_FILES)
                w.dnd_bind("<<Drop>>", self._on_drop)
        else:
            dz.bind("<Button-1>", lambda e: self._browse_files())

        # Clip table
        tbl_frame = tk.Frame(top_pane, bg=C_BG, padx=18)
        tbl_frame.pack(fill="both", expand=True, pady=(0,4))

        self.count_lbl = tk.Label(tbl_frame, text="No clips loaded",
                                  font=F_SMALL, bg=C_BG, fg=C_CREAM_MUT)
        self.count_lbl.pack(anchor="w", pady=(0,3))

        tf = tk.Frame(tbl_frame, bg=C_BG3,
                      highlightbackground=C_BORDER, highlightthickness=1)
        tf.pack(fill="both", expand=True)

        cols = ("device","file","location","offset","timecode","confidence","status")
        self.tree = ttk.Treeview(tf, columns=cols, show="headings", selectmode="browse")
        for cid, hdr, w, anc in [
            ("device",     "Device",      148, "w"),
            ("file",       "File",        215, "w"),
            ("location",   "Location",    185, "w"),
            ("offset",     "Offset",       76, "center"),
            ("timecode",   "Timecode",    110, "center"),
            ("confidence", "Confidence",   84, "center"),
            ("status",     "Status",      100, "center"),
        ]:
            self.tree.heading(cid, text=hdr)
            self.tree.column(cid, width=w, anchor=anc, minwidth=40)

        self._tree_sb = ttk.Scrollbar(tf, orient="vertical", command=self.tree.yview)
        self._tree_sb_visible = False

        def _tree_yscroll(first, last):
            first, last = float(first), float(last)
            if first <= 0.0 and last >= 1.0:
                if self._tree_sb_visible:
                    self._tree_sb.pack_forget()
                    self._tree_sb_visible = False
            else:
                if not self._tree_sb_visible:
                    self._tree_sb.pack(side="right", fill="y")
                    self._tree_sb_visible = True
            self._tree_sb.set(first, last)

        self.tree.configure(yscrollcommand=_tree_yscroll)
        self.tree.pack(fill="both", expand=True)

        # ── Bottom pane: timeline ──
        tl_pane = tk.Frame(self.paned, bg=C_BG2)
        self.paned.add(tl_pane, minsize=100, stretch="always")

        tl_header = tk.Frame(tl_pane, bg=C_BG2)
        tl_header.pack(fill="x", padx=14, pady=(6,2))
        tk.Label(tl_header, text="TIMELINE",
                 font=F_SMALL, bg=C_BG2, fg=C_CREAM_MUT).pack(side="left")
        tk.Label(tl_header,
                 text="  drag bar between lanes to reassign  /  cmd+scroll to zoom",
                 font=F_SMALL, bg=C_BG2, fg=C_CREAM_MUT).pack(side="left")

        self.timeline = Timeline(tl_pane, self)
        self.timeline.pack(fill="both", expand=True, padx=8, pady=(0,6))

    def _style_widgets(self):
        s = ttk.Style(); s.theme_use("default")
        s.configure("Treeview",
                    background=C_BG3, foreground=C_CREAM,
                    fieldbackground=C_BG3, rowheight=28,
                    font=F_MONO_SM, borderwidth=0, relief="flat")
        s.configure("Treeview.Heading",
                    background=C_BG2, foreground=C_CREAM_DIM,
                    font=F_SMALL, relief="flat", borderwidth=0)
        s.map("Treeview",
              background=[("selected", C_BG4)],
              foreground=[("selected", C_CREAM)])
        s.configure("TProgressbar", troughcolor=C_BG2,
                    background=C_AMBER, thickness=3)
        s.configure("TCombobox",
                    fieldbackground=C_BG3, background=C_BG3,
                    foreground=C_CREAM, selectbackground=C_BG4,
                    arrowcolor=C_AMBER, borderwidth=0)
        s.map("TCombobox",
              fieldbackground=[("readonly", C_BG3)],
              selectbackground=[("readonly", C_BG3)],
              foreground=[("readonly", C_CREAM)])
        s.configure("Sash", sashthickness=6)

        self.tree.tag_configure("anchor",   foreground=C_BLUE)
        self.tree.tag_configure("high",     foreground=C_GREEN)
        self.tree.tag_configure("med",      foreground=C_YELLOW)
        self.tree.tag_configure("low",      foreground=C_RED)
        self.tree.tag_configure("unsynced", foreground=C_CREAM_MUT)
        self.tree.tag_configure("error",    foreground=C_RED)
        self.tree.tag_configure("even",     background=C_BG3)
        self.tree.tag_configure("odd",      background=C_BG2)

    # ── Device / clip management ───────────────────────────────────────────────

    def _add_paths(self, paths):
        added = 0
        for p in paths:
            path = Path(str(p).strip())
            if path.suffix.lower() not in SUPPORTED: continue
            if path in self.clips: continue

            self.clips.append(path)
            dtype = guess_device_type(path)
            sig   = filename_signature(path)

            # Find existing device with same signature + type
            matched_label = None
            for lbl, meta_list in self._device_clips_meta().items():
                if (self.device_type.get(lbl) == dtype and
                        any(m["signature"] == sig for m in meta_list)):
                    matched_label = lbl
                    break

            if matched_label:
                label = matched_label
            else:
                # New device
                prefix = "Camera" if dtype == "camera" else "Audio Recorder"
                n = sum(1 for l in self.devices if l.startswith(prefix)) + 1
                label = f"{prefix} {n}"
                self.devices.append(label)
                self.device_type[label] = dtype
                self.clips_by_device[label] = []

            self.clips_by_device[label].append(path)
            self.clip_meta[str(path)] = {
                "device_label": label,
                "device_type":  dtype,
                "signature":    sig,
                "duration_secs": None,
            }
            added += 1

        if added:
            self._refresh_table()
            self._refresh_timeline_pending()
            self._auto_detect_fps()
            self.status_var.set(f"Added {added} clip(s)  ·  {len(self.clips)} total")

    def _device_clips_meta(self) -> dict:
        """Return {label: [meta_dict, ...]} for building signature lookup."""
        result = {}
        for path_str, meta in self.clip_meta.items():
            lbl = meta["device_label"]
            result.setdefault(lbl, []).append(meta)
        return result

    def reassign_clip(self, clip_path: Path, old_label: str, new_label: str):
        """Move a clip from one device lane to another (called by Timeline drag)."""
        if old_label not in self.clips_by_device: return
        if new_label not in self.clips_by_device: return
        self.clips_by_device[old_label] = [
            c for c in self.clips_by_device[old_label] if c != clip_path]
        self.clips_by_device[new_label].append(clip_path)
        self.clip_meta[str(clip_path)]["device_label"] = new_label
        self.clip_meta[str(clip_path)]["device_type"]  = self.device_type[new_label]
        self._refresh_table()
        self._rebuild_timeline()
        self.status_var.set(f"Moved {clip_path.name} → {new_label}")

    def _on_drop(self, event):
        paths = [m.group(1) or m.group(2)
                 for m in re.finditer(r'\{([^}]+)\}|(\S+)', event.data)]
        self._add_paths(paths)

    def _browse_files(self):
        self._add_paths(filedialog.askopenfilenames(
            title="Select clips",
            filetypes=[("Video & Audio",
                        "*.mp4 *.mov *.mxf *.avi *.mkv "
                        "*.wav *.mp3 *.aac *.m4a *.aiff *.flac"),
                       ("All files","*.*")]))

    def _browse_folder(self):
        d = filedialog.askdirectory(title="Select folder")
        if d:
            self._add_paths(sorted(Path(d).iterdir()))

    def _clear(self):
        self.clips.clear(); self.clip_meta.clear()
        self.devices.clear(); self.device_type.clear()
        self.clips_by_device.clear()
        self.results.clear(); self.results_by_path.clear()
        self.timeline._waveform_cache.clear()
        self.timeline._waveform_loading.clear()
        self._refresh_table()
        self.timeline.canvas.delete("all")
        self.timeline.label_canvas.delete("all")
        self.export_btn.enable(False)
        self.fps_var.set("23.976")
        self.done_indicator.pack_forget()
        self.status_var.set("CLEARED")

    def _ffprobe_fps(self, path: str) -> float | None:
        """Return the frame rate of a video file, or None if unavailable/audio-only."""
        try:
            cmd = [FFPROBE, "-v", "error",
                   "-select_streams", "v:0",
                   "-show_entries", "stream=r_frame_rate",
                   "-of", "default=noprint_wrappers=1:nokey=1",
                   path]
            r = subprocess.run(cmd, capture_output=True, text=True, timeout=10)
            raw = r.stdout.strip()
            if not raw: return None
            # r_frame_rate comes back as a fraction e.g. "24000/1001" or "30/1"
            if "/" in raw:
                num, den = raw.split("/")
                val = float(num) / float(den)
            else:
                val = float(raw)
            return round(val, 3) if val > 0 else None
        except Exception:
            return None

    # Known frame rate buckets — map a raw fps to the nearest standard value
    _FPS_BUCKETS = [
        (23.976, 23.0, 24.5),
        (24.0,   24.5, 24.9),
        (25.0,   24.9, 25.5),
        (29.97,  29.0, 30.0),
        (30.0,   30.0, 30.5),
        (47.952, 47.0, 48.5),
        (48.0,   48.5, 49.0),
        (50.0,   49.0, 51.0),
        (59.94,  59.0, 60.0),
        (60.0,   60.0, 61.0),
    ]

    def _snap_fps(self, raw: float) -> str:
        for standard, lo, hi in self._FPS_BUCKETS:
            if lo <= raw < hi:
                return str(standard)
        return f"{raw:.3f}"

    def _auto_detect_fps(self):
        """
        Check all loaded video clips via ffprobe.
        If every clip reports the same frame rate AND it's higher than the
        current setting, update the FPS selector automatically.
        Only runs on video files (skips audio-only clips).
        """
        video_clips = [p for p in self.clips
                       if p.suffix.lower() not in AUDIO_EXT]
        if not video_clips:
            return

        fps_values = set()
        for p in video_clips:
            fps = self._ffprobe_fps(str(p))
            if fps is not None:
                fps_values.add(self._snap_fps(fps))

        if len(fps_values) != 1:
            # Mixed or unknown — leave setting alone
            return

        detected = fps_values.pop()
        current  = self.fps_var.get()

        # Only auto-update if detected fps differs from current
        if detected != current:
            valid_fps = ["23.976","24","25","29.97","30","47.952","48","50","59.94","60"]
            if detected in valid_fps:
                self.fps_var.set(detected)
                self.status_var.set(
                    f"Added {len(self.clips)} clip(s)  ·  "
                    f"FPS auto-detected: {detected}"
                )

    def _short(self, p: Path, n=36) -> str:
        s = str(p).replace(str(Path.home()), "~")
        return ("…" + s[-(n-1):]) if len(s) > n else s

    # ── Table rendering ────────────────────────────────────────────────────────

    def _refresh_table(self):
        for r in self.tree.get_children(): self.tree.delete(r)

        # Sort: cameras first, then audio; within each group by device label
        def sort_key(p):
            meta = self.clip_meta.get(str(p), {})
            dtype = 0 if meta.get("device_type") == "camera" else 1
            return (dtype, meta.get("device_label",""), p.name)

        row = 0
        for path in sorted(self.clips, key=sort_key):
            meta   = self.clip_meta.get(str(path), {})
            result = self.results_by_path.get(str(path))
            off    = f"{result['offset_seconds']:+.4f}s" if result and result.get("offset_seconds") is not None else "—"
            tc     = result.get("timecode","—") if result else "—"
            conf   = f"{result.get('confidence',0)*100:.0f}%" if result and not result.get("is_anchor") else ("—" if not result else "ANCHOR")
            status = result.get("status_label","Pending") if result else "Pending"

            if not result:                          tag = "even" if row%2==0 else "odd"
            elif result.get("is_anchor"):           tag = "anchor"
            elif result.get("unsynced"):            tag = "unsynced"
            elif result.get("confidence",0)>=0.4:  tag = "high"
            elif result.get("confidence",0)>=0.1:  tag = "med"
            else:                                   tag = "low"

            self.tree.insert("", "end",
                             values=(meta.get("device_label","—"), path.name,
                                     self._short(path.parent),
                                     off, tc, conf, status),
                             tags=(tag,))
            row += 1

        # Summary
        nc = sum(1 for d in self.devices if self.device_type.get(d)=="camera")
        na = sum(1 for d in self.devices if self.device_type.get(d)=="audio")
        parts = []
        if nc: parts.append(f"{nc} camera{'s' if nc>1 else ''}")
        if na: parts.append(f"{na} audio recorder{'s' if na>1 else ''}")
        self.count_lbl.config(
            text=(f"{len(self.clips)} clips  ·  {', '.join(parts)}"
                  if self.clips else "No clips loaded"))

        # Anchor combo
        opts = ["Auto (largest file)"] + [c.name for c in self.clips]
        self.anchor_combo["values"] = opts
        if self.anchor_var.get() not in opts: self.anchor_var.set("Auto (largest file)")

    # ── Timeline rendering ─────────────────────────────────────────────────────

    def _refresh_timeline_pending(self):
        """Draw timeline with clips at t=0 (before sync runs)."""
        if not self.clips: return
        # Build a placeholder results_by_path with offset=0 and rough duration
        placeholder = {}
        for p in self.clips:
            placeholder[str(p)] = {
                "offset_seconds": 0.0,
                "duration_secs":  30.0,
                "confidence":     0.0,
                "status_label":   "Pending",
                "unsynced":       True,
            }
        self.timeline.draw(
            devices=self.devices,
            clips_by_device=self.clips_by_device,
            results_by_path=placeholder,
            total_secs=max(len(self.clips)*5.0, 30.0),
        )

    def _rebuild_timeline(self):
        """Redraw timeline with real sync results (or placeholder if not synced yet)."""
        if self.results_by_path:
            results = self.results_by_path
            min_off = min((r.get("offset_seconds") or 0) for r in results.values())
            max_end = max(
                ((r.get("offset_seconds") or 0) - min_off + (r.get("duration_secs") or 10))
                for r in results.values()
            )
            # Normalise offsets
            norm = {}
            for k, r in results.items():
                nr = dict(r)
                nr["offset_seconds"] = (r.get("offset_seconds") or 0) - min_off
                norm[k] = nr
            self.timeline.draw(
                devices=self.devices,
                clips_by_device=self.clips_by_device,
                results_by_path=norm,
                total_secs=max(max_end, 10.0),
            )
        else:
            self._refresh_timeline_pending()

    # ── Sync ──────────────────────────────────────────────────────────────────

    def _start_sync(self):
        if self.running: return
        if len(self.clips) < 2:
            messagebox.showwarning("Not enough clips","Add at least 2 clips first.")
            return
        self.running = True
        self.done_indicator.pack_forget()
        self.export_btn.enable(False)
        self.progress.pack(fill="x", side="bottom")
        self.progress.configure(value=0, maximum=len(self.clips)-1)

        self._spinner_frames  = ["[|]", "[/]", "[-]", "[\\]"]
        self._spinner_idx     = 0
        self._sync_start_time = time.time()
        self._sync_phase      = "INIT"
        self._sync_in_loop    = False
        self.status_bar.config(bg=C_BG2, fg=C_AMBER)   # orange text while syncing
        self._tick_spinner()

        threading.Thread(target=self._sync_thread, daemon=True).start()

    def _tick_spinner(self):
        """Animates the run button and status bar while sync is running."""
        if not self.running:
            return
        frame = self._spinner_frames[self._spinner_idx % len(self._spinner_frames)]
        self._spinner_idx += 1
        elapsed = int(time.time() - self._sync_start_time)
        m, s    = divmod(elapsed, 60)
        t_str   = f"{m}:{s:02d}" if m else f"0:{s:02d}"
        self.run_btn.set_text(f"{frame} SYNCING  {t_str}")
        self.run_btn.enable(False)
        if not self._sync_in_loop:
            self.status_var.set(self._sync_phase)
        self.root.after(120, self._tick_spinner)

    def _sync_thread(self):
        try:
            if self.anchor_var.get() == "Auto (largest file)":
                anchor = max(self.clips, key=lambda c: c.stat().st_size)
            else:
                anchor = next((c for c in self.clips
                               if c.name==self.anchor_var.get()), self.clips[0])

            fps = float(self.fps_var.get())
            total = len(self.clips)

            # ── Phase 1: extract anchor audio ──────────────────────────────
            self._sync_in_loop = False
            self.root.after(0, lambda: setattr(self, "_sync_phase",
                f"READING ANCHOR  /  {anchor.name[:30]}"))

            anchor_audio = extract_audio(anchor)
            others = [c for c in self.clips if c != anchor]
            ameta  = self.clip_meta.get(str(anchor), {})
            anchor_dur = self._ffprobe_duration(str(anchor))
            self.clip_meta[str(anchor)]["duration_secs"] = anchor_dur

            results = []
            anchor_result = {
                "clip": anchor.name, "path": str(anchor),
                "device_type":    ameta.get("device_type","camera"),
                "device_label":   ameta.get("device_label","Camera 1"),
                "offset_seconds": 0.0,
                "duration_secs":  anchor_dur,
                "timecode":       "+00:00:00:00",
                "confidence":     1.0,
                "status_label":   "Anchor",
                "is_anchor":      True,
                "unsynced":       False,
                "error":          None,
            }
            results.append(anchor_result)

            # ── Phase 2: sync all other clips ──────────────────────────────
            self._sync_in_loop  = True
            loop_start          = time.time()
            done                = [0]
            n_others            = len(others)

            with Pool(processes=min(cpu_count(), n_others)) as pool:
                for clip_str, offset, conf, error in \
                        pool.imap_unordered(compute_offset,
                                            [(str(c), anchor_audio, SAMPLE_RATE)
                                             for c in others]):
                    clip  = Path(clip_str)
                    meta  = self.clip_meta.get(clip_str, {})
                    done[0] += 1
                    unsynced = False

                    if error or conf < 0.04:
                        final_off = 0.0
                        tc        = to_tc(0.0, fps)
                        status    = "⚠ Auto-placed"
                        unsynced  = True
                        conf      = conf if not error else 0.0
                    else:
                        final_off = offset
                        tc        = to_tc(offset, fps)
                        if conf >= 0.4:   status = "✓ Synced"
                        elif conf >= 0.1: status = "~ Synced"
                        else:             status = "? Low conf"

                    dur = self._ffprobe_duration(clip_str)
                    self.clip_meta[clip_str]["duration_secs"] = dur

                    results.append({
                        "clip": clip.name, "path": clip_str,
                        "device_type":    meta.get("device_type","camera"),
                        "device_label":   meta.get("device_label","—"),
                        "offset_seconds": round(final_off, 6),
                        "duration_secs":  dur,
                        "timecode":       tc,
                        "confidence":     round(conf, 4),
                        "status_label":   status,
                        "is_anchor":      False,
                        "unsynced":       unsynced,
                        "error":          error,
                    })

                    # ── Rich progress update ───────────────────────────────
                    n         = done[0]
                    pct       = int(n / n_others * 100)
                    elapsed_l = time.time() - loop_start
                    if n > 0:
                        secs_per  = elapsed_l / n
                        remaining = max(0, (n_others - n) * secs_per)
                        rm, rs    = divmod(int(remaining), 60)
                        eta_str   = f"eta {rm}:{rs:02d}" if rm else f"eta 0:{rs:02d}"
                    else:
                        eta_str = ""

                    name_short = clip.name[:24] + ".." if len(clip.name) > 26 else clip.name
                    status_msg = f"{n}/{n_others}  {pct}%  /  {name_short}  /  {eta_str}"

                    # Animate clip sliding to its position on the timeline
                    normalized_off = round(final_off, 6)
                    self.root.after(0, lambda msg=status_msg, v=n,
                                          cp=clip, off=normalized_off,
                                          d=dur, c=round(conf,4): (
                        self.status_var.set(msg),
                        self.progress.configure(value=v),
                        self.timeline.animate_clip_to(cp, off, d, c)
                    ))

            self.results         = results
            self.results_by_path = {r["path"]: r for r in results}
            self._sync_in_loop   = False
            self.root.after(0, self._sync_done)

        except Exception as e:
            self._sync_in_loop = False
            self.root.after(0, lambda: self._sync_error(str(e)))

    def _ffprobe_duration(self, path: str) -> float:
        try:
            cmd = [FFPROBE,"-v","error",
                   "-show_entries","format=duration",
                   "-of","default=noprint_wrappers=1:nokey=1", path]
            r = subprocess.run(cmd, capture_output=True, text=True, timeout=15)
            return max(0.1, float(r.stdout.strip()))
        except Exception:
            return 60.0

    def _dialog(self, title: str, message: str, kind: str = "info"):
        """
        Branded centered dialog with animated waveform graphic.
        kind: 'info' | 'error' | 'warning'
        """
        dlg = tk.Toplevel(self.root)
        dlg.title("")           # no OS title bar text
        dlg.configure(bg=C_BG)
        dlg.resizable(False, False)
        dlg.transient(self.root)
        dlg.grab_set()

        accent = C_GREEN if kind == "info" else (C_RED if kind == "error" else C_AMBER)

        # ── Top accent bar ────────────────────────────────────────────────────
        tk.Frame(dlg, bg=accent, height=3).pack(fill="x")

        # ── Header row ────────────────────────────────────────────────────────
        hdr = tk.Frame(dlg, bg=C_BG2)
        hdr.pack(fill="x")

        tk.Label(hdr, text="SYNCCLIP", font=("Menlo", 9),
                 bg=C_BG2, fg=C_CREAM_MUT, padx=20, pady=(12,2)).pack(side="left", anchor="w")
        tk.Label(hdr, text=f"/ {title}", font=("Menlo", 9, "bold"),
                 bg=C_BG2, fg=accent, pady=(12,2)).pack(side="left", anchor="w")

        # ── Animated waveform canvas ──────────────────────────────────────────
        W, H = 400, 56
        wave_canvas = tk.Canvas(dlg, width=W, height=H, bg=C_BG,
                                highlightthickness=0, bd=0)
        wave_canvas.pack(fill="x", padx=0, pady=0)

        # Draw static grid lines
        for y_frac in [0.25, 0.5, 0.75]:
            wave_canvas.create_line(0, int(H * y_frac), W, int(H * y_frac),
                                    fill=C_BORDER, width=1)
        for x in range(0, W, 40):
            wave_canvas.create_line(x, 0, x, H, fill=C_BORDER, width=1)

        # Animated waveform — sinusoidal with noise, scrolls left
        wave_line = wave_canvas.create_line(0, H//2, W, H//2,
                                            fill=accent, width=2, smooth=True)
        anim_running = [True]
        phase        = [0.0]

        def _animate_wave():
            if not anim_running[0]:
                return
            phase[0] += 0.18
            pts = []
            for x in range(0, W, 3):
                t   = x / W * 4 * 3.14159 + phase[0]
                amp = (H * 0.28) * (
                    0.6 * __import__("math").sin(t) +
                    0.25 * __import__("math").sin(t * 2.3 + 1.1) +
                    0.15 * __import__("math").sin(t * 0.7 - 0.5)
                )
                pts.extend([x, H//2 - amp])
            if len(pts) >= 4:
                wave_canvas.coords(wave_line, *pts)
            dlg.after(40, _animate_wave)   # ~25fps

        _animate_wave()

        # ── Divider ───────────────────────────────────────────────────────────
        tk.Frame(dlg, bg=C_BORDER, height=1).pack(fill="x")

        # ── Message body ──────────────────────────────────────────────────────
        body = tk.Frame(dlg, bg=C_BG2)
        body.pack(fill="x", padx=22, pady=(14, 10))

        for line in message.strip().split("\n"):
            if not line.strip():
                tk.Frame(body, bg=C_BG2, height=6).pack()
                continue
            # Lines that look like labels (all caps / short) get orange accent
            is_label = line.isupper() and len(line) < 40
            tk.Label(body, text=line,
                     font=("Menlo", 10, "bold") if is_label else ("Menlo", 10),
                     bg=C_BG2,
                     fg=accent if is_label else C_CREAM,
                     anchor="w", justify="left",
                     wraplength=356).pack(fill="x", anchor="w")

        # ── Bottom bar with OK button ─────────────────────────────────────────
        tk.Frame(dlg, bg=C_BORDER, height=1).pack(fill="x")

        bot = tk.Frame(dlg, bg=C_BG)
        bot.pack(fill="x", padx=20, pady=12)

        # Subtle version stamp on the left
        tk.Label(bot, text="syncclip / waveform sync",
                 font=("Menlo", 8), bg=C_BG, fg=C_CREAM_MUT).pack(side="left")

        ok_btn = tk.Label(bot, text="[ OK ]", font=("Menlo", 11, "bold"),
                          bg=C_BG3, fg=accent, padx=18, pady=7,
                          cursor=_get_hand_cursor())
        ok_btn.pack(side="right")
        ok_btn.bind("<Enter>",    lambda e: ok_btn.config(bg=accent, fg="#0A0A0A"))
        ok_btn.bind("<Leave>",    lambda e: ok_btn.config(bg=C_BG3, fg=accent))
        ok_btn.bind("<Button-1>", lambda e: (
            setattr(anim_running, 0, False) or True) and dlg.destroy())

        # Also close on Enter key
        dlg.bind("<Return>", lambda e: dlg.destroy())
        dlg.bind("<Escape>", lambda e: dlg.destroy())

        # ── Center over app window ────────────────────────────────────────────
        dlg.update_idletasks()
        rw = self.root.winfo_width()
        rh = self.root.winfo_height()
        rx = self.root.winfo_rootx()
        ry = self.root.winfo_rooty()
        dw = dlg.winfo_reqwidth()
        dh = dlg.winfo_reqheight()
        dlg.geometry(f"{W+2}x{dh}+{rx + (rw - (W+2))//2}+{ry + (rh - dh)//2}")

        self.root.wait_window(dlg)
        anim_running[0] = False

    def _sync_done(self):
        self.running = False
        self.run_btn.set_text("[ RUN SYNC ]"); self.run_btn.enable(True)
        self.export_btn.enable(True)
        self.progress.pack_forget()
        self._refresh_table()
        self._rebuild_timeline()
        synced   = sum(1 for r in self.results if not r["unsynced"] and not r["is_anchor"])
        unsynced = sum(1 for r in self.results if r["unsynced"])

        # ── Persistent green indicator in topbar ──────────────────────────────
        self.done_indicator.config(
            text=f"  [OK] {synced}/{len(self.clips)-1} SYNCED"
        )
        self.done_indicator.pack(side="left", pady=2)

        # ── Status bar flash ──────────────────────────────────────────────────
        msg = f"DONE  {synced}/{len(self.clips)-1} SYNCED"
        if unsynced: msg += f"  /  {unsynced} PLACED"
        self.status_var.set(msg)
        self.status_bar.config(bg=C_GREEN, fg="#000000")
        self.root.after(4000, lambda: self.status_bar.config(bg=C_BG2, fg=C_CREAM_DIM))
        # ── Sound — afplay is built into every Mac, no install needed ─────────
        threading.Thread(
            target=lambda: subprocess.run(
                ["afplay", "/System/Library/Sounds/Glass.aiff"],
                capture_output=True
            ), daemon=True
        ).start()

        # ── macOS notification — works even when app is in background ─────────
        notif_title   = "SyncClip"
        notif_body    = f"{synced} clips synced. Ready to export."
        threading.Thread(
            target=lambda: subprocess.run(
                ["osascript", "-e",
                 f'display notification "{notif_body}" with title "{notif_title}"'],
                capture_output=True
            ), daemon=True
        ).start()

        # ── Dialog ────────────────────────────────────────────────────────────
        detail = f"{synced} clip{'s' if synced!=1 else ''} synced."
        if unsynced:
            detail += f"\n{unsynced} clip{'s' if unsynced!=1 else ''} auto-placed at timeline start."
        detail += "\n\nPress [ EXPORT XML ] to continue."
        self._dialog("SYNC COMPLETE", detail, "info")

    def _sync_error(self, msg):
        self.running = False
        self.run_btn.set_text("[ RUN SYNC ]"); self.run_btn.enable(True)
        self.progress.pack_forget()
        self.status_bar.config(bg=C_BG2, fg=C_RED)
        self.status_var.set(f"ERROR  /  {msg}")
        self.root.after(5000, lambda: self.status_bar.config(fg=C_CREAM_DIM))
        self._dialog("SYNC ERROR", msg, "error")

    # ── Premiere XML export ────────────────────────────────────────────────────

    def _get_clip_info(self, file_path: str, fps: float) -> dict:
        dur_frames = int(fps * 3600); channels = 2
        try:
            cmd = [FFPROBE,"-v","error",
                   "-show_entries","format=duration:stream=channels,codec_type",
                   "-of","json", file_path]
            r = subprocess.run(cmd, capture_output=True, text=True, timeout=15)
            data = json.loads(r.stdout)
            d = float(data.get("format",{}).get("duration",0))
            if d > 0: dur_frames = max(1, round(d * fps))
            for s in data.get("streams",[]):
                if s.get("codec_type") == "audio":
                    ch = s.get("channels")
                    if ch and int(ch) > 0: channels = int(ch)
                    break
        except Exception: pass
        return {"dur_frames": dur_frames, "channel_count": channels}

    def _path_to_url(self, file_path: str) -> str:
        p = Path(file_path)
        parts = [quote(part, safe="") for part in p.parts]
        return "file:///" + "/".join(parts).lstrip("/")

    def _export_xml(self):
        if not self.results:
            messagebox.showwarning("No results","Run sync first."); return
        save_path = filedialog.asksaveasfilename(
            title="Save Premiere XML", defaultextension=".xml",
            filetypes=[("Premiere Pro XML","*.xml")],
            initialfile="SyncClip_sequence.xml")
        if not save_path: return

        fps     = float(self.fps_var.get())
        fps_int = round(fps)
        ntsc    = "TRUE" if fps_int in (24, 30, 60) and fps != fps_int else "FALSE"

        # Separate synced vs unsynced
        synced_results   = [r for r in self.results if not r.get("unsynced")]
        unsynced_results = [r for r in self.results if r.get("unsynced")]
        n_synced   = sum(1 for r in synced_results if not r.get("is_anchor"))
        n_unsynced = len(unsynced_results)

        # ── Sequence name ─────────────────────────────────────────────────────
        date_str = time.strftime("%b %d %Y")
        time_str = time.strftime("%I:%M %p").lstrip("0")
        if n_unsynced:
            seq_name = f"SyncClip — {n_synced} synced, {n_unsynced} unsynced — {date_str} {time_str}"
        else:
            seq_name = f"SyncClip — {n_synced} clips synced — {date_str} {time_str}"

        self.status_var.set("Reading clip metadata for export…")
        self.root.update()

        # ── Work out unsynced placement: end of last synced clip on same device ─
        # Build a map: device_label → end_seconds of last synced clip
        device_end_secs = {}
        for r in synced_results:
            lbl = r.get("device_label", "")
            end = (r.get("offset_seconds") or 0.0) + (r.get("duration_secs") or 0.0)
            if end > device_end_secs.get(lbl, 0.0):
                device_end_secs[lbl] = end

        # Assign offsets for unsynced clips: place sequentially after last synced
        # on their device. If no synced clip on that device, place after end of timeline.
        global_end = max(
            ((r.get("offset_seconds") or 0.0) + (r.get("duration_secs") or 0.0))
            for r in synced_results
        ) if synced_results else 0.0

        device_cursor = {}   # tracks current placement cursor per device
        for r in unsynced_results:
            lbl = r.get("device_label", "")
            if lbl not in device_cursor:
                # Start after last synced clip on this device, or end of timeline
                device_cursor[lbl] = device_end_secs.get(lbl, global_end)
            r["offset_seconds"] = device_cursor[lbl]
            dur = r.get("duration_secs") or 0.0
            device_cursor[lbl] += dur  # next unsynced clip follows this one

        # All results with updated offsets
        all_results = synced_results + unsynced_results
        min_off = min(r["offset_seconds"] for r in all_results)

        # ── Per-clip info from ffprobe ────────────────────────────────────────
        clip_infos = []
        seq_dur = 0
        for i, r in enumerate(all_results):
            info = self._get_clip_info(r["path"], fps)
            sf   = max(0, round((r["offset_seconds"] - min_off) * fps))
            df   = info["dur_frames"]
            ch   = info["channel_count"]
            ef   = sf + df
            seq_dur = max(seq_dur, ef)

            # Use the original filename (without extension) as the display name in
            # Premiere — this is what shows up on the clip in the timeline
            raw_name  = Path(r["path"]).name          # e.g. A7S30028.MP4
            stem_name = Path(r["path"]).stem          # e.g. A7S30028

            def xml_escape(s):
                return (s.replace("&","&amp;").replace("<","&lt;")
                         .replace(">","&gt;").replace('"',"&quot;"))

            clip_infos.append({
                "idx":       i + 1,
                "result":    r,
                "sf":        sf,
                "ef":        ef,
                "df":        df,
                "channels":  ch,
                "url":       self._path_to_url(r["path"]),
                "name":      xml_escape(stem_name),   # display name in Premiere
                "filename":  xml_escape(raw_name),    # full filename for <file><n>
                "unsynced":  r.get("unsynced", False),
            })

        # ── Group clips by device, preserving order ───────────────────────────
        device_order     = []
        clips_per_device = {}
        for c in clip_infos:
            lbl = c["result"].get("device_label", "Camera 1")
            if lbl not in clips_per_device:
                device_order.append(lbl)
                clips_per_device[lbl] = []
            clips_per_device[lbl].append(c)

        # ── Build tracks ──────────────────────────────────────────────────────
        rate_block   = f"<rate><timebase>{fps_int}</timebase><ntsc>{ntsc}</ntsc></rate>"
        video_tracks = ""
        audio_tracks = ""

        for t_idx, lbl in enumerate(device_order):
            clips = clips_per_device[lbl]
            dtype = self.device_type.get(lbl, "camera")

            v_items = ""
            a_items = ""

            for c in clips:
                i    = c["idx"]
                rate = rate_block

                file_block = f"""<file id="file-{i}">
                        <n>{c['filename']}</n>
                        <pathurl>{c['url']}</pathurl>
                        {rate}
                        <duration>{c['df']}</duration>
                        <media>
                            <video>
                                <samplecharacteristics>
                                    {rate}
                                    <width>1920</width>
                                    <height>1080</height>
                                    <pixelaspectratio>square</pixelaspectratio>
                                    <fielddominance>none</fielddominance>
                                </samplecharacteristics>
                            </video>
                            <audio>
                                <channelcount>{c['channels']}</channelcount>
                                <samplecharacteristics>
                                    <depth>16</depth>
                                    <samplerate>48000</samplerate>
                                </samplecharacteristics>
                            </audio>
                        </media>
                    </file>"""

                if dtype == "camera":
                    v_items += f"""
                <clipitem id="v{t_idx}-{i}">
                    <n>{c['name']}</n>
                    <enabled>TRUE</enabled>
                    <duration>{c['df']}</duration>
                    {rate}
                    <start>{c['sf']}</start>
                    <end>{c['ef']}</end>
                    <in>0</in>
                    <out>{c['df']}</out>
                    {file_block}
                </clipitem>"""

                a_file_ref = file_block if dtype == "audio" else f'<file id="file-{i}"/>'
                a_items += f"""
                <clipitem id="a{t_idx}-{i}">
                    <n>{c['name']}</n>
                    <enabled>TRUE</enabled>
                    <duration>{c['df']}</duration>
                    {rate}
                    <start>{c['sf']}</start>
                    <end>{c['ef']}</end>
                    <in>0</in>
                    <out>{c['df']}</out>
                    {a_file_ref}
                </clipitem>"""

            if dtype == "camera":
                video_tracks += f"""
            <track>
                <enabled>TRUE</enabled>
                <locked>FALSE</locked>{v_items}
            </track>"""

            audio_tracks += f"""
            <track>
                <enabled>TRUE</enabled>
                <locked>FALSE</locked>{a_items}
            </track>"""

        # ── Final XML ─────────────────────────────────────────────────────────
        def xml_escape_name(s):
            return (s.replace("&","&amp;").replace("<","&lt;")
                     .replace(">","&gt;").replace('"',"&quot;"))

        xml = f"""<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE xmeml>
<xmeml version="5">
    <sequence>
        <n>{xml_escape_name(seq_name)}</n>
        <duration>{seq_dur}</duration>
        {rate_block}
        <media>
            <video>
                <format>
                    <samplecharacteristics>
                        {rate_block}
                        <width>1920</width>
                        <height>1080</height>
                        <pixelaspectratio>square</pixelaspectratio>
                        <fielddominance>none</fielddominance>
                    </samplecharacteristics>
                </format>{video_tracks}
            </video>
            <audio>
                <format>
                    <samplecharacteristics>
                        <depth>16</depth>
                        <samplerate>48000</samplerate>
                    </samplecharacteristics>
                </format>{audio_tracks}
            </audio>
        </media>
    </sequence>
</xmeml>
"""
        with open(save_path, "w", encoding="utf-8") as f:
            f.write(xml)

        self.status_var.set(f"EXPORTED  {Path(save_path).name}")
        n_total = len(all_results)
        msg = f"Saved to:\n{save_path}\n\n{n_synced} clips synced"
        if n_unsynced:
            msg += f"\n{n_unsynced} unsynced clips placed after their device's last synced clip"
        msg += "\n\nIn Premiere: File > Import > select this XML file."
        self._dialog("EXPORT COMPLETE", msg, "info")

    # ── Updater ───────────────────────────────────────────────────────────────

    def _check_for_update(self):
        """
        Fetch latest app.py from GitHub, compare VERSION, offer to update.
        Runs network request in background thread so UI doesn't freeze.
        """
        self.update_btn.config(text="[ ... ]", fg=C_AMBER)
        self.status_var.set("Checking for updates...")
        threading.Thread(target=self._update_thread, daemon=True).start()

    def _update_thread(self):
        try:
            import urllib.request
            with urllib.request.urlopen(GITHUB_RAW_URL, timeout=10) as resp:
                remote_src = resp.read().decode("utf-8")

            # Extract VERSION from remote file
            remote_version = None
            for line in remote_src.splitlines():
                if line.startswith("VERSION"):
                    # e.g.  VERSION = "1.3"
                    val = line.split("=")[1].strip().strip('"').strip("'")
                    remote_version = val
                    break

            self.root.after(0, lambda: self._update_result(remote_src, remote_version))

        except Exception as e:
            self.root.after(0, lambda: self._update_error(str(e)))

    def _update_result(self, remote_src: str, remote_version: str | None):
        self.update_btn.config(text="[ UPDATE ]", fg=C_CREAM_MUT)

        if remote_version is None:
            self.status_var.set("Update check failed — could not read version")
            return

        def _ver_tuple(v):
            try: return tuple(int(x) for x in v.split("."))
            except: return (0,)

        if _ver_tuple(remote_version) <= _ver_tuple(VERSION):
            self.status_var.set(f"Up to date  /  v{VERSION}")
            self._dialog("UP TO DATE",
                         f"You are running the latest version.\n\nv{VERSION}",
                         "info")
            return

        # Newer version available — ask to install
        msg = (f"New version available!\n\n"
               f"Current:  v{VERSION}\n"
               f"Latest:    v{remote_version}\n\n"
               f"Download and restart now?")

        # Custom yes/no dialog
        dlg = tk.Toplevel(self.root)
        dlg.title("")
        dlg.configure(bg=C_BG)
        dlg.resizable(False, False)
        dlg.transient(self.root)
        dlg.grab_set()

        tk.Frame(dlg, bg=C_AMBER, height=3).pack(fill="x")

        hdr = tk.Frame(dlg, bg=C_BG2)
        hdr.pack(fill="x")
        tk.Label(hdr, text="SYNCCLIP  / UPDATE AVAILABLE",
                 font=("Menlo", 9, "bold"), bg=C_BG2, fg=C_AMBER,
                 padx=20, pady=12).pack(side="left")

        tk.Frame(dlg, bg=C_BORDER, height=1).pack(fill="x")

        body = tk.Frame(dlg, bg=C_BG2)
        body.pack(fill="x", padx=22, pady=16)
        for line in msg.strip().split("\n"):
            is_label = line.startswith("Current") or line.startswith("Latest")
            tk.Label(body, text=line,
                     font=("Menlo", 10, "bold") if is_label else ("Menlo", 10),
                     bg=C_BG2,
                     fg=C_AMBER if is_label else C_CREAM,
                     anchor="w").pack(fill="x", anchor="w")

        tk.Frame(dlg, bg=C_BORDER, height=1).pack(fill="x")

        btn_row = tk.Frame(dlg, bg=C_BG)
        btn_row.pack(fill="x", padx=20, pady=12)

        def _cancel():
            dlg.destroy()
            self.status_var.set("Update cancelled")

        def _install():
            dlg.destroy()
            self._install_update(remote_src)

        cancel = tk.Label(btn_row, text="[ CANCEL ]", font=("Menlo", 11),
                          bg=C_BG3, fg=C_CREAM_DIM, padx=14, pady=7,
                          cursor=_get_hand_cursor())
        cancel.pack(side="left")
        cancel.bind("<Enter>",    lambda e: cancel.config(bg=C_BG4))
        cancel.bind("<Leave>",    lambda e: cancel.config(bg=C_BG3))
        cancel.bind("<Button-1>", lambda e: _cancel())

        ok = tk.Label(btn_row, text="[ DOWNLOAD & RESTART ]",
                      font=("Menlo", 11, "bold"),
                      bg=C_AMBER, fg="#0A0A0A", padx=14, pady=7,
                      cursor=_get_hand_cursor())
        ok.pack(side="right")
        ok.bind("<Enter>",    lambda e: ok.config(bg=C_AMBER_D))
        ok.bind("<Leave>",    lambda e: ok.config(bg=C_AMBER))
        ok.bind("<Button-1>", lambda e: _install())
        dlg.bind("<Escape>",  lambda e: _cancel())

        dlg.update_idletasks()
        rw = self.root.winfo_width();  rx = self.root.winfo_rootx()
        rh = self.root.winfo_height(); ry = self.root.winfo_rooty()
        dw = dlg.winfo_reqwidth();     dh = dlg.winfo_reqheight()
        dlg.geometry(f"+{rx+(rw-dw)//2}+{ry+(rh-dh)//2}")

    def _install_update(self, new_src: str):
        """Write the new source over this file and relaunch."""
        self.status_var.set("Installing update...")
        try:
            this_file = Path(__file__).resolve()
            # Write to a temp file first, then replace atomically
            tmp = this_file.with_suffix(".tmp")
            tmp.write_text(new_src, encoding="utf-8")
            tmp.replace(this_file)
        except Exception as e:
            self._dialog("UPDATE FAILED",
                         f"Could not write update:\n{e}\n\n"
                         "Try running the app from a folder you own (e.g. Desktop).",
                         "error")
            return

        # Relaunch
        self.status_var.set("Restarting...")
        self.root.after(400, lambda: (
            os.execv(sys.executable, [sys.executable, str(Path(__file__).resolve())])
        ))

    def _update_error(self, msg: str):
        self.update_btn.config(text="[ UPDATE ]", fg=C_CREAM_MUT)
        self.status_var.set("Update check failed")
        self._dialog("UPDATE FAILED",
                     f"Could not reach GitHub:\n{msg}\n\nCheck your internet connection.",
                     "error")

    def run(self): self.root.mainloop()


if __name__ == "__main__":
    if subprocess.run([FFMPEG,"-version"], capture_output=True).returncode != 0:
        print("❌  ffmpeg not found. Run: brew install ffmpeg"); sys.exit(1)
    App().run()
