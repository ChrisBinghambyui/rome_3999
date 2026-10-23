"""
Rome 3999 (Arcade 3.x), Tron: Legacy look

Screens: main menu, mode select, options, game (with pause and results).
Modes: Gladiator (16 arena levels), Endless (survive as long as you can),
Campaign (one mission so far) and Custom (placeholder for now).
Gladiator's first 8 levels fit on one screen (rectangle, circle, octagon).
Levels 9 to 16 are big arenas built from rooms and doorways, and the camera
follows you smoothly. Enemies in those levels hunt you through the rooms.
Endless lets you pick any arena, how many enemies, and how many lives.
Your records there are the longest time survived and the most kills.
Campaign mission 1 starts with a long corridor. At the end of it you step into
a big circular arena, an announcer opens the match (you can't move during it),
and the obstacles draw themselves in before the fight starts.

Controls in game:
    WASD         move
    Mouse        aim
    Left click   throw disc (only when you are holding it)
    Space        recall disc (it flies back to you so you can catch it)
    ESC          pause
Anywhere:
    F11          toggle fullscreen (the window can also be resized freely)

Install:
    pip install arcade

Progress, settings and records are saved to rome_3999_save.json next to this file.
"""

import bisect
import heapq
import json
import math
import os
import random
import arcade
from arcade.shape_list import ShapeElementList, create_polygon

WIDTH = 1000   # logical size; the window scales this to fit
HEIGHT = 680
TITLE = "Rome 3999"

ARENA_MARGIN = 60
ARENA_LEFT = ARENA_MARGIN
ARENA_RIGHT = WIDTH - ARENA_MARGIN
ARENA_BOTTOM = ARENA_MARGIN
ARENA_TOP = HEIGHT - ARENA_MARGIN
DEFAULT_BOUNDS = (ARENA_LEFT, ARENA_BOTTOM, ARENA_RIGHT, ARENA_TOP)
CENTER_X = WIDTH / 2
CENTER_Y = HEIGHT / 2
ARENA_RADIUS = 280     # circle radius, octagon apothem (levels can override with "radius")
CIRCLE_SIDES = 72      # the circle is a 72 sided polygon under the hood

GRID = 40  # floor grid spacing, centered on the arena

PLAYER_SPEED = 260
PLAYER_RADIUS = 14

DISC_RADIUS = 12
DISC_SPEED = 520
RECALL_SPEED = 700
CATCH_RADIUS = 30
CATCH_DELAY = 0.25  # seconds after a throw before it can be caught
HOLD_DISTANCE = 30

RESPAWN_TIME = 1.5
FRIENDLY_FIRE = False  # set True if your own rebounds should be able to kill you
LIVES = 3

STREAK_BRIGHTNESS = 0.5  # how bright the moving floor lights are (1.0 = full)

FOLLOW_RATE = 6.0   # camera smoothing, higher is snappier (it is a per second rate)
LOOK_AHEAD = 0.12   # how far the camera leans toward the mouse (0 turns it off)

NAV_CELL = 32       # size of one square on the enemy navigation grid
HUNT_RANGE = 520    # hunting enemies stop chasing and start strafing inside this range

WALL = 36           # thickness of room walls in the big levels
PIP_COUNT = 8       # difficulty pips on the level cards
LEVELS_PER_PAGE = 8
ICON_MAX_SCALE = 0.085   # biggest scale for the little arena maps

MAX_TEXT_POINTS = 64     # text never renders bigger than this, huge fonts break

ENDLESS_MAX_ENEMIES = 6
ENDLESS_MAX_LIVES = 9
ENDLESS_RAMP_KILLS = 40  # kills it takes for enemies to reach full endless difficulty

# Campaign cutscene timing (seconds, except the typing speed)
CORRIDOR_EXIT_MARGIN = 70       # how far from the corridor's end the exit gate sits
FADE_OUT_TIME = 0.6
FADE_IN_TIME = 0.8
SPEECH_LEAD = 0.6               # quiet moment before the announcer starts
SPEECH_CHARS_PER_SECOND = 34
SPEECH_HOLD = 1.1               # how long a finished line stays up
REVEAL_TIME = 1.6               # obstacles trace in, then flash solid at the end
CUTSCENE_PHASES = ("fading_out", "fading_in", "speech", "reveal")

PLAYER_COLOR = (40, 215, 255)
ENEMY_COLORS = [(255, 130, 20), (255, 60, 90), (255, 200, 50), (190, 110, 255)]
ENEMY_COLOR = ENEMY_COLORS[0]
WHITE_HOT = (235, 250, 255)
CONDUIT_COLOR = (150, 225, 255)
TEXT_DIM = (120, 180, 210)
SLAB_COLOR = (10, 12, 19, 255)

FONT = ("Consolas", "Courier New", "monospace")

HELD = "held"
FLYING = "flying"
RETURNING = "returning"

# Avatar outline in local coordinates (x is forward, y is sideways)
BODY_POINTS = [(17, 0), (7, 10), (-6, 13), (-14, 7), (-14, -7), (-6, -13), (7, -10)]

# Navigation grid steps: (column change, row change, cost)
NAV_STEPS = [(1, 0, 1.0), (-1, 0, 1.0), (0, 1, 1.0), (0, -1, 1.0),
             (1, 1, 1.414), (1, -1, 1.414), (-1, 1, 1.414), (-1, -1, 1.414)]


# ------------------------------------------------------------------ level building helpers

def wall_h(y, x0, x1):
    return ("rect", (x0 + x1) / 2, y, x1 - x0, WALL)


def wall_v(x, y0, y1):
    return ("rect", x, (y0 + y1) / 2, WALL, y1 - y0)


def wall_h_gaps(y, x0, x1, gaps):
    # A horizontal wall with doorways. gaps is a sorted list of (center_x, width).
    specs = []
    start = x0
    for gap in gaps:
        low = gap[0] - gap[1] / 2
        if low > start:
            specs.append(wall_h(y, start, low))
        start = gap[0] + gap[1] / 2
    if start < x1:
        specs.append(wall_h(y, start, x1))
    return specs


def wall_v_gaps(x, y0, y1, gaps):
    # A vertical wall with doorways. gaps is a sorted list of (center_y, width).
    specs = []
    start = y0
    for gap in gaps:
        low = gap[0] - gap[1] / 2
        if low > start:
            specs.append(wall_v(x, start, low))
        start = gap[0] + gap[1] / 2
    if start < y1:
        specs.append(wall_v(x, start, y1))
    return specs


def room_walls(left, bottom, right, top, doors):
    # Four walls around a box. doors is a list of (side, center, width) where
    # side is "b", "t", "l" or "r" and center is x (b, t) or y (l, r).
    gaps = {"b": [], "t": [], "l": [], "r": []}
    for door in doors:
        gaps[door[0]].append((door[1], door[2]))
    half = WALL / 2
    specs = []
    specs.extend(wall_h_gaps(bottom, left - half, right + half, sorted(gaps["b"])))
    specs.extend(wall_h_gaps(top, left - half, right + half, sorted(gaps["t"])))
    specs.extend(wall_v_gaps(left, bottom + half, top - half, sorted(gaps["l"])))
    specs.extend(wall_v_gaps(right, bottom + half, top - half, sorted(gaps["r"])))
    return specs


def pillar_grid(xs, ys, size):
    specs = []
    for x in xs:
        for y in ys:
            specs.append(("rect", x, y, size, size))
    return specs


def rack_row(y, xs, width):
    specs = []
    for x in xs:
        specs.append(("rect", x, y, width, 44))
    return specs


def circle_ring(center_x, center_y, ring_radius, count, radius, start_angle):
    specs = []
    for i in range(count):
        angle = math.radians(start_angle) + i * math.tau / count
        specs.append(("circle", center_x + ring_radius * math.cos(angle),
                      center_y + ring_radius * math.sin(angle), radius))
    return specs


def pillar_ring(center_x, center_y, ring_radius, count, size, start_angle):
    # Square pillars spaced evenly around a circle.
    specs = []
    for i in range(count):
        angle = math.radians(start_angle) + i * math.tau / count
        specs.append(("rect", center_x + ring_radius * math.cos(angle),
                      center_y + ring_radius * math.sin(angle), size, size))
    return specs


# Obstacles: ("rect", center_x, center_y, width, height) or ("circle", center_x, center_y, radius)
# Optional level keys: "bounds" (left, bottom, right, top), "radius", "hunt" (enemies
# pathfind through rooms and only throw with a clear line of sight).
LEVELS = [
    {"name": "TRAINING GRID", "arena": "rect", "obstacles": [],
     "enemies": 1, "kills": 3, "interval": 2.6, "error": 0.40, "speed": 0,
     "difficulty": 1, "player_start": (180, 340), "enemy_starts": [(820, 340)]},

    {"name": "THE RING", "arena": "circle", "obstacles": [],
     "enemies": 1, "kills": 4, "interval": 2.0, "error": 0.26, "speed": 90,
     "difficulty": 2, "player_start": (270, 340), "enemy_starts": [(730, 340)]},

    {"name": "OCTAGON CELL", "arena": "octagon", "obstacles": [],
     "enemies": 1, "kills": 4, "interval": 1.7, "error": 0.20, "speed": 130,
     "difficulty": 2, "player_start": (270, 340), "enemy_starts": [(730, 340)]},

    {"name": "PILLAR HALL", "arena": "rect",
     "obstacles": [("rect", 340, 230, 64, 64), ("rect", 660, 230, 64, 64),
                   ("rect", 340, 450, 64, 64), ("rect", 660, 450, 64, 64)],
     "enemies": 1, "kills": 5, "interval": 1.5, "error": 0.16, "speed": 150,
     "difficulty": 3, "player_start": (170, 340), "enemy_starts": [(830, 340)]},

    {"name": "TWO ON ONE", "arena": "circle", "obstacles": [],
     "enemies": 2, "kills": 6, "interval": 2.2, "error": 0.24, "speed": 100,
     "difficulty": 3, "player_start": (270, 340),
     "enemy_starts": [(690, 430), (690, 250)]},

    {"name": "CROSSWORKS", "arena": "rect",
     "obstacles": [("rect", 500, 340, 300, 36), ("rect", 500, 340, 36, 300)],
     "enemies": 1, "kills": 5, "interval": 1.2, "error": 0.12, "speed": 190,
     "difficulty": 4, "player_start": (150, 340), "enemy_starts": [(850, 340)]},

    {"name": "BROKEN RING", "arena": "circle",
     "obstacles": [("circle", 500, 460, 32), ("circle", 396, 280, 32),
                   ("circle", 604, 280, 32)],
     "enemies": 2, "kills": 6, "interval": 1.6, "error": 0.18, "speed": 130,
     "difficulty": 4, "player_start": (270, 340),
     "enemy_starts": [(690, 400), (660, 230)]},

    {"name": "SYSTEM CORE", "arena": "octagon",
     "obstacles": [("rect", 500, 340, 70, 70), ("rect", 360, 200, 40, 40),
                   ("rect", 640, 200, 40, 40), ("rect", 360, 480, 40, 40),
                   ("rect", 640, 480, 40, 40)],
     "enemies": 3, "kills": 8, "interval": 2.0, "error": 0.14, "speed": 150,
     "difficulty": 5, "player_start": (260, 340),
     "enemy_starts": [(740, 340), (610, 540), (610, 140)]},

    # ---- big arenas with rooms: the camera follows you from here on

    {"name": "TWIN CHAMBERS", "arena": "rect", "bounds": (60, 60, 1660, 860),
     "obstacles": wall_v_gaps(860, 60, 860, [(260, 140), (660, 140)]) +
                  [("rect", 460, 460, 64, 64), ("rect", 1260, 460, 64, 64)],
     "enemies": 1, "kills": 6, "interval": 1.4, "error": 0.14, "speed": 170,
     "hunt": True, "difficulty": 5,
     "player_start": (180, 460), "enemy_starts": [(1540, 460)]},

    {"name": "THE CONCOURSE", "arena": "rect", "bounds": (60, 60, 2060, 760),
     "obstacles": pillar_grid([460, 860, 1260, 1660], [250, 570], 56) +
                  [wall_h(410, 700, 920), wall_h(410, 1200, 1420)],
     "enemies": 2, "kills": 8, "interval": 1.8, "error": 0.15, "speed": 160,
     "hunt": True, "difficulty": 5,
     "player_start": (160, 410), "enemy_starts": [(1960, 300), (1960, 520)]},

    {"name": "FOUR ROOMS", "arena": "rect", "bounds": (60, 60, 1460, 1060),
     "obstacles": wall_v_gaps(760, 60, 1060, [(310, 130), (810, 130)]) +
                  wall_h_gaps(560, 60, 742, [(410, 130)]) +
                  wall_h_gaps(560, 778, 1460, [(1110, 130)]) +
                  [("circle", 400, 300, 34), ("rect", 1110, 300, 60, 60),
                   ("rect", 400, 810, 60, 60), ("circle", 1110, 810, 34)],
     "enemies": 2, "kills": 8, "interval": 1.5, "error": 0.13, "speed": 170,
     "hunt": True, "difficulty": 6,
     "player_start": (200, 200), "enemy_starts": [(1260, 900), (1260, 200)]},

    {"name": "THE VAULT", "arena": "octagon", "bounds": (160, 60, 1440, 1340),
     "radius": 640,
     "obstacles": room_walls(620, 520, 980, 880,
                             [("b", 800, 120), ("t", 800, 120),
                              ("l", 700, 120), ("r", 700, 120)]) +
                  [("circle", 420, 320, 36), ("circle", 1180, 320, 36),
                   ("circle", 420, 1080, 36), ("circle", 1180, 1080, 36)],
     "enemies": 3, "kills": 9, "interval": 2.0, "error": 0.14, "speed": 150,
     "hunt": True, "difficulty": 6,
     "player_start": (800, 220),
     "enemy_starts": [(800, 1180), (260, 700), (1340, 700)]},

    {"name": "SERVER FARM", "arena": "rect", "bounds": (60, 60, 2060, 1160),
     "obstacles": rack_row(300, [400, 800, 1200, 1600], 300) +
                  rack_row(610, [600, 1000, 1400, 1800], 300) +
                  rack_row(920, [400, 800, 1200, 1600], 300),
     "enemies": 3, "kills": 10, "interval": 1.8, "error": 0.12, "speed": 160,
     "hunt": True, "difficulty": 7,
     "player_start": (160, 610),
     "enemy_starts": [(2005, 300), (2005, 610), (2005, 920)]},

    {"name": "THE ARCHIVE", "arena": "rect", "bounds": (60, 60, 1860, 1260),
     "obstacles": wall_v_gaps(660, 60, 1260, [(360, 130), (960, 130)]) +
                  wall_v_gaps(1260, 60, 1260, [(960, 130)]) +
                  wall_h_gaps(660, 60, 642, [(360, 130)]) +
                  [wall_h(660, 678, 1242)] +
                  wall_h_gaps(660, 1278, 1860, [(1560, 130)]) +
                  [("circle", 960, 960, 36), ("rect", 1560, 960, 60, 60),
                   ("rect", 360, 360, 60, 60), ("circle", 960, 360, 36),
                   ("rect", 1560, 360, 60, 60)],
     "enemies": 3, "kills": 10, "interval": 1.5, "error": 0.12, "speed": 175,
     "hunt": True, "difficulty": 7,
     "player_start": (160, 200),
     "enemy_starts": [(1700, 1100), (1700, 200), (960, 1150)]},

    {"name": "COLISEUM", "arena": "circle", "bounds": (200, 80, 1600, 1480),
     "radius": 700,
     "obstacles": circle_ring(900, 780, 270, 10, 30, 0) +
                  circle_ring(900, 780, 500, 6, 44, 0),
     "enemies": 4, "kills": 12, "interval": 2.4, "error": 0.16, "speed": 150,
     "hunt": True, "difficulty": 8,
     "player_start": (900, 200),
     "enemy_starts": [(900, 1360), (300, 780), (1500, 780), (900, 780)]},

    {"name": "THE FORUM", "arena": "rect", "bounds": (60, 60, 2260, 1460),
     "obstacles": room_walls(760, 460, 1560, 1060,
                             [("b", 1160, 160), ("t", 1160, 160),
                              ("l", 760, 160), ("r", 760, 160)]) +
                  room_walls(160, 160, 560, 440, [("r", 300, 130)]) +
                  room_walls(1760, 160, 2160, 440, [("l", 300, 130)]) +
                  room_walls(160, 1080, 560, 1360, [("r", 1220, 130)]) +
                  room_walls(1760, 1080, 2160, 1360, [("l", 1220, 130)]) +
                  [("rect", 1160, 260, 80, 80), ("rect", 1160, 1260, 80, 80),
                   ("rect", 460, 760, 80, 80), ("rect", 1860, 760, 80, 80),
                   ("circle", 1160, 760, 50)],
     "enemies": 4, "kills": 14, "interval": 2.0, "error": 0.12, "speed": 170,
     "hunt": True, "difficulty": 8,
     "player_start": (1160, 160),
     "enemy_starts": [(300, 300), (2060, 300), (300, 1220), (2060, 1220)]},
]

# Campaign missions. These work like the levels above, with a few extras:
#   "corridor"  the long hallway the mission starts in (bounds and player_start)
#   "obstacles" what is in the arena from the start (nothing here)
#   "reveal"    obstacles that draw themselves in after the announcer is done
#   "speech"    the announcer's lines, shown one at a time
# "player_start" and "enemy_starts" belong to the arena, not the corridor.
CAMPAIGN_LEVELS = [
    {"name": "THE LONG WALK", "arena": "circle", "bounds": (140, 140, 1260, 1260),
     "radius": 560,
     "corridor": {"bounds": (60, 60, 3060, 320), "player_start": (160, 190)},
     "obstacles": [],
     "reveal": pillar_ring(700, 700, 300, 6, 56, 0) + [("rect", 700, 700, 64, 64)],
     "speech": ["CITIZENS OF ROME 3999. WELCOME TO THE GRID.",
                "TONIGHT, A NEW CHALLENGER ENTERS THE ARENA.",
                "THE GLADIATOR MATCH IS ABOUT TO BEGIN.",
                "LET THE ARENA SHOW NO MERCY."],
     "enemies": 2, "kills": 6, "interval": 2.0, "error": 0.20, "speed": 130,
     "hunt": True, "difficulty": 3,
     "player_start": (200, 700), "enemy_starts": [(1130, 700), (900, 1020)]},
]


# ------------------------------------------------------------------ helpers

def with_alpha(color, alpha):
    return (color[0], color[1], color[2], int(max(0, min(255, alpha))))


def mix(color, other, amount):
    r = int(color[0] + (other[0] - color[0]) * amount)
    g = int(color[1] + (other[1] - color[1]) * amount)
    b = int(color[2] + (other[2] - color[2]) * amount)
    return (r, g, b)


def to_world(x, y, facing, local_x, local_y):
    c = math.cos(facing)
    s = math.sin(facing)
    return (x + local_x * c - local_y * s, y + local_x * s + local_y * c)


def level_label(index):
    number = index + 1
    if number < 10:
        return "0" + str(number)
    return str(number)


def format_time(seconds):
    # 83.4 becomes "1:23"
    total = int(seconds)
    minutes = total // 60
    secs = total % 60
    text = str(secs)
    if secs < 10:
        text = "0" + text
    return str(minutes) + ":" + text


def level_bounds(level):
    return level.get("bounds", DEFAULT_BOUNDS)


def level_radius(level):
    return level.get("radius", ARENA_RADIUS)


def endless_key(level_index, enemies, lives):
    # Records are kept per arena, enemy count and lives, so they compare fairly.
    return str(level_index) + ":" + str(enemies) + ":" + str(lives)


def glow_on():
    # Additive blending: overlapping light adds up instead of covering.
    ctx = arcade.get_window().ctx
    ctx.blend_func = ctx.SRC_ALPHA, ctx.ONE


def glow_off():
    ctx = arcade.get_window().ctx
    ctx.blend_func = ctx.BLEND_DEFAULT


def draw_light_pool(x, y, radius, color, strength):
    # Soft pool of light on the floor. Call between glow_on and glow_off.
    layers = [(1.0, 5), (0.75, 7), (0.5, 10), (0.28, 14)]
    for scale, alpha in layers:
        arcade.draw_circle_filled(x, y, radius * scale,
                                  with_alpha(color, alpha * strength))


def toggle_fullscreen(window):
    window.set_fullscreen(not window.fullscreen)
    window.save.set("fullscreen", window.fullscreen)


def segment_hits_box(x0, y0, x1, y1, left, right, bottom, top):
    # True if the line from (x0, y0) to (x1, y1) passes through the box.
    t0 = 0.0
    t1 = 1.0
    dx = x1 - x0
    dy = y1 - y0

    if abs(dx) < 0.000001:
        if x0 < left or x0 > right:
            return False
    else:
        ta = (left - x0) / dx
        tb = (right - x0) / dx
        if ta > tb:
            swap = ta
            ta = tb
            tb = swap
        t0 = max(t0, ta)
        t1 = min(t1, tb)
        if t0 > t1:
            return False

    if abs(dy) < 0.000001:
        if y0 < bottom or y0 > top:
            return False
    else:
        ta = (bottom - y0) / dy
        tb = (top - y0) / dy
        if ta > tb:
            swap = ta
            ta = tb
            tb = swap
        t0 = max(t0, ta)
        t1 = min(t1, tb)
        if t0 > t1:
            return False

    return True


class CrispText:
    # Lays out in logical coordinates, but renders at real pixel size so the
    # font stays sharp when the window is stretched. The label is rebuilt when
    # the size changes (resizing a pyglet label in place leaves it clipped or
    # invisible). The rendered size is capped at MAX_TEXT_POINTS. Only draw it
    # while the screen camera (not the world camera) is active.
    def __init__(self, text, x, y, color, size, anchor_x="center",
                 anchor_y="center", bold=False):
        self.x = x
        self.y = y
        self.size = size
        self.string = text
        self.rgba = color
        self.anchor_x_value = anchor_x
        self.anchor_y_value = anchor_y
        self.bold = bold
        self.label = None
        self.last_size = None
        self.dirty = True

    @property
    def text(self):
        return self.string

    @text.setter
    def text(self, value):
        if self.string != value:
            self.string = value
            self.dirty = True

    @property
    def color(self):
        return self.rgba

    @color.setter
    def color(self, value):
        if tuple(self.rgba) != tuple(value):
            self.rgba = value
            self.dirty = True

    @property
    def anchor_x(self):
        return self.anchor_x_value

    @anchor_x.setter
    def anchor_x(self, value):
        if self.anchor_x_value != value:
            self.anchor_x_value = value
            self.dirty = True

    def pick_size(self, scale):
        wanted = min(self.size * scale, MAX_TEXT_POINTS)
        if wanted < 20:
            size = int(round(wanted))
        else:
            size = int(round(wanted / 2)) * 2   # steps of 2 points when large
        if size < 6:
            size = 6
        return size

    def draw(self):
        screen = Screen.active
        if screen is None:
            return
        px, py = screen.to_pixels(self.x, self.y)
        size = self.pick_size(screen.scale)

        if self.label is None or size != self.last_size or self.dirty:
            self.label = arcade.Text(self.string, 0, 0, self.rgba, size,
                                     anchor_x=self.anchor_x_value,
                                     anchor_y=self.anchor_y_value,
                                     bold=self.bold, font_name=FONT)
            self.last_size = size
            self.dirty = False

        self.label.position = (int(round(px)), int(round(py)))
        screen.text_camera.use()
        self.label.draw()
        screen.camera.use()


def make_text(text, x, y, color, size, anchor_x="center", anchor_y="center", bold=False):
    return CrispText(text, x, y, color, size, anchor_x, anchor_y, bold)


# ------------------------------------------------------------------ save data

SAVE_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "rome_3999_save.json")

DEFAULTS = {
    "master_volume": 80,
    "music_volume": 70,
    "sfx_volume": 80,
    "fullscreen": False,
    "show_fps": False,
    "has_played": False,
    "current_level": 0,
    "unlocked": 1,
    "endless_level": 0,
    "endless_enemies": 2,
    "endless_lives": 3,
    "endless_records": {},
}
SETTING_KEYS = ["master_volume", "music_volume", "sfx_volume", "fullscreen", "show_fps"]


class SaveData:
    def __init__(self):
        self.data = dict(DEFAULTS)
        self.data["endless_records"] = {}
        self.load()

    def load(self):
        try:
            with open(SAVE_PATH, "r") as file:
                loaded = json.load(file)
        except (OSError, ValueError):
            return
        if not isinstance(loaded, dict):
            return
        for key in DEFAULTS:
            if key in loaded and type(loaded[key]) == type(DEFAULTS[key]):
                self.data[key] = loaded[key]
        for key in ["master_volume", "music_volume", "sfx_volume"]:
            self.data[key] = max(0, min(100, self.data[key]))
        self.data["unlocked"] = max(1, min(len(LEVELS), self.data["unlocked"]))
        self.data["current_level"] = max(0, min(self.data["unlocked"] - 1,
                                                self.data["current_level"]))
        self.data["endless_level"] = max(0, min(len(LEVELS) - 1, self.data["endless_level"]))
        self.data["endless_enemies"] = max(1, min(ENDLESS_MAX_ENEMIES, self.data["endless_enemies"]))
        self.data["endless_lives"] = max(1, min(ENDLESS_MAX_LIVES, self.data["endless_lives"]))

        # Each record is {"time": seconds survived, "kills": most kills}.
        clean_records = {}
        raw_records = self.data["endless_records"]
        for key in raw_records:
            value = raw_records[key]
            if not isinstance(key, str) or not isinstance(value, dict):
                continue
            best_time = value.get("time", 0)
            best_kills = value.get("kills", 0)
            if not isinstance(best_time, (int, float)) or not isinstance(best_kills, int):
                continue
            if best_time < 0 or best_kills < 0:
                continue
            clean_records[key] = {"time": float(best_time), "kills": best_kills}
        self.data["endless_records"] = clean_records

    def save(self):
        try:
            with open(SAVE_PATH, "w") as file:
                json.dump(self.data, file, indent=2)
        except OSError:
            pass

    def get(self, key):
        return self.data[key]

    def set(self, key, value):
        self.data[key] = value
        self.save()

    def endless_record(self, key):
        # The best time and most kills for one endless setup (zeros if never played).
        record = self.data["endless_records"].get(key)
        if record is None:
            return {"time": 0.0, "kills": 0}
        return record

    def reset_settings(self):
        for key in SETTING_KEYS:
            self.data[key] = DEFAULTS[key]
        self.save()

    def volume(self, kind):
        # Final 0.0 to 1.0 volume for "music" or "sfx". Use this when sounds get added.
        return (self.data["master_volume"] / 100) * (self.data[kind + "_volume"] / 100)


# ------------------------------------------------------------------ arena geometry

def arena_points(kind, bounds, radius):
    # Corner points of the arena, counter-clockwise.
    center_x = (bounds[0] + bounds[2]) / 2
    center_y = (bounds[1] + bounds[3]) / 2
    points = []
    if kind == "circle":
        for i in range(CIRCLE_SIDES):
            angle = i * math.tau / CIRCLE_SIDES
            points.append((center_x + radius * math.cos(angle),
                           center_y + radius * math.sin(angle)))
    elif kind == "octagon":
        corner_radius = radius / math.cos(math.pi / 8)
        for i in range(8):
            angle = math.pi / 8 + i * math.pi / 4
            points.append((center_x + corner_radius * math.cos(angle),
                           center_y + corner_radius * math.sin(angle)))
    else:
        points = [(bounds[0], bounds[1]), (bounds[2], bounds[1]),
                  (bounds[2], bounds[3]), (bounds[0], bounds[3])]
    return points


def offset_polygon(points, distance):
    # Pushes a convex counter-clockwise polygon outward by a fixed distance.
    count = len(points)
    normals = []
    for i in range(count):
        a = points[i]
        b = points[(i + 1) % count]
        dx = b[0] - a[0]
        dy = b[1] - a[1]
        length = math.hypot(dx, dy)
        normals.append((dy / length, -dx / length))  # outward
    result = []
    for i in range(count):
        n1 = normals[i - 1]
        n2 = normals[i]
        scale = distance / (1.0 + n1[0] * n2[0] + n1[1] * n2[1])
        result.append((points[i][0] + (n1[0] + n2[0]) * scale,
                       points[i][1] + (n1[1] + n2[1]) * scale))
    return result


class Edge:
    # One straight wall segment of the arena.
    def __init__(self, a, b, start):
        self.ax = a[0]
        self.ay = a[1]
        dx = b[0] - a[0]
        dy = b[1] - a[1]
        self.length = math.hypot(dx, dy)
        self.tx = dx / self.length
        self.ty = dy / self.length
        self.nx = -self.ty   # inward normal
        self.ny = self.tx
        self.start = start   # distance along the perimeter where this edge begins


class Obstacle:
    def __init__(self, spec):
        self.kind = spec[0]
        self.x = spec[1]
        self.y = spec[2]
        self.width = 0
        self.height = 0
        self.radius = 0
        if self.kind == "rect":
            self.width = spec[3]
            self.height = spec[4]
        else:
            self.radius = spec[3]
        self.flash = 0.0
        self.flash_color = CONDUIT_COLOR

    def is_visible(self, view):
        # view is (left, bottom, right, top) or None for "always draw".
        if view is None:
            return True
        half_w = self.radius + 20
        half_h = self.radius + 20
        if self.kind == "rect":
            half_w = self.width / 2 + 20
            half_h = self.height / 2 + 20
        if self.x + half_w < view[0] or self.x - half_w > view[2]:
            return False
        if self.y + half_h < view[1] or self.y - half_h > view[3]:
            return False
        return True

    def blocks_line(self, x0, y0, x1, y1, radius):
        # True if a circle of this radius, travelling the line, would hit the obstacle.
        if self.kind == "rect":
            return segment_hits_box(x0, y0, x1, y1,
                                    self.x - self.width / 2 - radius,
                                    self.x + self.width / 2 + radius,
                                    self.y - self.height / 2 - radius,
                                    self.y + self.height / 2 + radius)
        dx = x1 - x0
        dy = y1 - y0
        length_sq = dx * dx + dy * dy
        t = 0.0
        if length_sq > 0.000001:
            t = ((self.x - x0) * dx + (self.y - y0) * dy) / length_sq
            t = max(0.0, min(1.0, t))
        closest_x = x0 + dx * t
        closest_y = y0 + dy * t
        return math.hypot(self.x - closest_x, self.y - closest_y) < self.radius + radius

    def collide(self, x, y, radius):
        # Returns (normal_x, normal_y, depth, contact_x, contact_y) or None.
        if self.kind == "circle":
            dx = x - self.x
            dy = y - self.y
            dist = math.hypot(dx, dy)
            reach = radius + self.radius
            if dist >= reach:
                return None
            if dist < 0.0001:
                nx = 1.0
                ny = 0.0
            else:
                nx = dx / dist
                ny = dy / dist
            return (nx, ny, reach - dist, self.x + nx * self.radius, self.y + ny * self.radius)

        left = self.x - self.width / 2
        right = self.x + self.width / 2
        bottom = self.y - self.height / 2
        top = self.y + self.height / 2
        cx = max(left, min(right, x))
        cy = max(bottom, min(top, y))
        dx = x - cx
        dy = y - cy
        d2 = dx * dx + dy * dy
        if d2 >= radius * radius:
            return None
        if d2 > 0:
            dist = math.sqrt(d2)
            return (dx / dist, dy / dist, radius - dist, cx, cy)

        # center is inside the block: push out through the nearest face
        options = [(x - left, -1, 0, left, y), (right - x, 1, 0, right, y),
                   (y - bottom, 0, -1, x, bottom), (top - y, 0, 1, x, top)]
        best = options[0]
        for option in options:
            if option[0] < best[0]:
                best = option
        return (best[1], best[2], best[0] + radius, best[3], best[4])

    def draw(self):
        lit = mix(CONDUIT_COLOR, self.flash_color, self.flash)
        glow = 25 + 130 * self.flash
        if self.kind == "rect":
            left = self.x - self.width / 2
            right = self.x + self.width / 2
            bottom = self.y - self.height / 2
            top = self.y + self.height / 2
            glow_on()
            arcade.draw_lrbt_rectangle_outline(left, right, bottom, top,
                                               with_alpha(lit, glow * 0.5), 18)
            arcade.draw_lrbt_rectangle_outline(left, right, bottom, top,
                                               with_alpha(lit, glow), 8)
            glow_off()
            arcade.draw_lrbt_rectangle_filled(left, right, bottom, top, (8, 10, 18, 255))
            arcade.draw_lrbt_rectangle_outline(left, right, bottom, top, lit, 2)
            if self.width > 20 and self.height > 20:
                arcade.draw_lrbt_rectangle_outline(left + 7, right - 7, bottom + 7, top - 7,
                                                   with_alpha(lit, 70), 1)
        else:
            glow_on()
            arcade.draw_circle_outline(self.x, self.y, self.radius, with_alpha(lit, glow * 0.5), 18)
            arcade.draw_circle_outline(self.x, self.y, self.radius, with_alpha(lit, glow), 8)
            glow_off()
            arcade.draw_circle_filled(self.x, self.y, self.radius, (8, 10, 18, 255))
            arcade.draw_circle_outline(self.x, self.y, self.radius, lit, 2)
            arcade.draw_circle_outline(self.x, self.y, self.radius * 0.6, with_alpha(lit, 70), 1)


class Arena:
    # A convex arena shape plus obstacles (rooms are built from obstacle walls).
    # Handles walls, clipping the floor grid, line of sight, enemy pathfinding,
    # and the stretch of frame around it.
    def __init__(self, kind, obstacle_specs, bounds=None, radius=None):
        if bounds is None:
            bounds = DEFAULT_BOUNDS
        if radius is None:
            radius = ARENA_RADIUS
        self.kind = kind
        self.bounds = bounds
        self.cx = (bounds[0] + bounds[2]) / 2
        self.cy = (bounds[1] + bounds[3]) / 2
        # The solid frame around the arena. The camera never looks past this.
        self.frame = (bounds[0] - ARENA_MARGIN, bounds[1] - ARENA_MARGIN,
                      bounds[2] + ARENA_MARGIN, bounds[3] + ARENA_MARGIN)
        self.points = arena_points(kind, bounds, radius)
        count = len(self.points)

        self.edges = []
        self.starts = []
        total = 0.0
        for i in range(count):
            edge = Edge(self.points[i], self.points[(i + 1) % count], total)
            self.edges.append(edge)
            self.starts.append(total)
            total += edge.length
        self.perimeter = total

        self.outer_points = offset_polygon(self.points, 8)
        self.obstacles = []
        for spec in obstacle_specs:
            self.obstacles.append(Obstacle(spec))

        xs = []
        ys = []
        for p in self.points:
            xs.append(p[0])
            ys.append(p[1])
        self.min_x = min(xs)
        self.max_x = max(xs)
        self.min_y = min(ys)
        self.max_y = max(ys)

        self.nav_ready = False
        self.nav_cols = 0
        self.nav_rows = 0
        self.nav_free = []

        self.build_grid()
        self.build_slab()
        self.build_brackets()

    def add_obstacles(self, specs):
        # Adds obstacles after the arena was built (the campaign reveal uses this).
        for spec in specs:
            self.obstacles.append(Obstacle(spec))
        self.nav_ready = False   # enemies need a fresh map of what is walkable

    def clip_segment(self, p0, p1):
        # Trims a line so only the part inside the arena is left.
        t0 = 0.0
        t1 = 1.0
        dx = p1[0] - p0[0]
        dy = p1[1] - p0[1]
        for edge in self.edges:
            num = (p0[0] - edge.ax) * edge.nx + (p0[1] - edge.ay) * edge.ny
            den = dx * edge.nx + dy * edge.ny
            if abs(den) < 0.000001:
                if num < 0:
                    return None
            else:
                t = -num / den
                if den > 0:
                    t0 = max(t0, t)
                else:
                    t1 = min(t1, t)
            if t0 > t1:
                return None
        return ((p0[0] + dx * t0, p0[1] + dy * t0), (p0[0] + dx * t1, p0[1] + dy * t1))

    def build_grid(self):
        self.minor_lines = []
        self.major_lines = []
        self.streak_segments = []

        first_k = int(math.floor((self.min_x - self.cx) / GRID))
        last_k = int(math.ceil((self.max_x - self.cx) / GRID))
        for k in range(first_k, last_k + 1):
            x = self.cx + k * GRID
            clipped = self.clip_segment((x, self.min_y - 100), (x, self.max_y + 100))
            if clipped is None or abs(clipped[1][1] - clipped[0][1]) < 20:
                continue
            if k % 4 == 0:
                self.major_lines.append(clipped[0])
                self.major_lines.append(clipped[1])
            else:
                self.minor_lines.append(clipped[0])
                self.minor_lines.append(clipped[1])
            if abs(clipped[1][1] - clipped[0][1]) >= 120:
                self.streak_segments.append((False, x, clipped[0][1], clipped[1][1]))

        first_k = int(math.floor((self.min_y - self.cy) / GRID))
        last_k = int(math.ceil((self.max_y - self.cy) / GRID))
        for k in range(first_k, last_k + 1):
            y = self.cy + k * GRID
            clipped = self.clip_segment((self.min_x - 100, y), (self.max_x + 100, y))
            if clipped is None or abs(clipped[1][0] - clipped[0][0]) < 20:
                continue
            if k % 4 == 0:
                self.major_lines.append(clipped[0])
                self.major_lines.append(clipped[1])
            else:
                self.minor_lines.append(clipped[0])
                self.minor_lines.append(clipped[1])
            if abs(clipped[1][0] - clipped[0][0]) >= 120:
                self.streak_segments.append((True, y, clipped[0][0], clipped[1][0]))

    def build_slab(self):
        # Everything outside the arena is solid frame. Built once from wedges
        # that fan out from each wall, so any shape works.
        self.slab = ShapeElementList()
        far = 30
        count = len(self.points)
        for i in range(count):
            a = self.points[i]
            b = self.points[(i + 1) % count]
            a_far = (self.cx + (a[0] - self.cx) * far, self.cy + (a[1] - self.cy) * far)
            b_far = (self.cx + (b[0] - self.cx) * far, self.cy + (b[1] - self.cy) * far)
            self.slab.append(create_polygon([a, b, b_far, a_far], SLAB_COLOR))

    def build_brackets(self):
        # Where the heavy white corner brackets go (distance along the perimeter).
        self.bracket_distances = []
        if self.kind == "circle":
            self.bracket_length = 50
            for i in range(4):
                self.bracket_distances.append(self.perimeter * (i + 0.5) / 4)
        else:
            if self.kind == "octagon":
                self.bracket_length = 40
            else:
                self.bracket_length = 56
            for edge in self.edges:
                self.bracket_distances.append(edge.start)

    def point_at(self, distance, offset=0.0):
        # A point on the wall, by distance along the perimeter. A positive
        # offset moves it outward.
        d = distance % self.perimeter
        index = bisect.bisect_right(self.starts, d) - 1
        edge = self.edges[index]
        t = d - edge.start
        return (edge.ax + edge.tx * t - edge.nx * offset,
                edge.ay + edge.ty * t - edge.ny * offset)

    def constrain(self, x, y, radius):
        # Keeps a circle inside the walls and out of the obstacles.
        for i in range(3):
            for edge in self.edges:
                dist = (x - edge.ax) * edge.nx + (y - edge.ay) * edge.ny
                if dist < radius:
                    x += edge.nx * (radius - dist)
                    y += edge.ny * (radius - dist)
            for obstacle in self.obstacles:
                hit = obstacle.collide(x, y, radius)
                if hit is not None:
                    x += hit[0] * hit[2]
                    y += hit[1] * hit[2]
        return (x, y)

    def is_free(self, x, y, margin):
        for edge in self.edges:
            if (x - edge.ax) * edge.nx + (y - edge.ay) * edge.ny < margin:
                return False
        for obstacle in self.obstacles:
            if obstacle.collide(x, y, margin) is not None:
                return False
        return True

    def line_clear(self, x0, y0, x1, y1, radius):
        # True if a circle of this radius can travel the line without touching an obstacle.
        for obstacle in self.obstacles:
            if obstacle.blocks_line(x0, y0, x1, y1, radius):
                return False
        return True

    def random_point(self, margin, avoid_x, avoid_y, min_distance):
        for i in range(40):
            x = random.uniform(self.min_x, self.max_x)
            y = random.uniform(self.min_y, self.max_y)
            if not self.is_free(x, y, margin):
                continue
            if math.hypot(x - avoid_x, y - avoid_y) < min_distance:
                continue
            return (x, y)
        return None

    def nearby_point(self, x, y, radius, margin):
        # A free spot within reach that can be walked to in a straight line.
        for i in range(14):
            angle = random.uniform(0, math.tau)
            distance = random.uniform(radius * 0.4, radius)
            px = x + math.cos(angle) * distance
            py = y + math.sin(angle) * distance
            if not self.is_free(px, py, margin):
                continue
            if not self.line_clear(x, y, px, py, PLAYER_RADIUS + 2):
                continue
            return (px, py)
        return None

    # ------------------------------------------------------------ navigation grid

    def build_nav(self):
        self.nav_cols = int((self.max_x - self.min_x) / NAV_CELL) + 1
        self.nav_rows = int((self.max_y - self.min_y) / NAV_CELL) + 1
        self.nav_free = []
        for row in range(self.nav_rows):
            for col in range(self.nav_cols):
                x = self.min_x + (col + 0.5) * NAV_CELL
                y = self.min_y + (row + 0.5) * NAV_CELL
                self.nav_free.append(self.is_free(x, y, PLAYER_RADIUS + 6))
        self.nav_ready = True

    def cell_of(self, x, y):
        col = int((x - self.min_x) / NAV_CELL)
        row = int((y - self.min_y) / NAV_CELL)
        col = max(0, min(self.nav_cols - 1, col))
        row = max(0, min(self.nav_rows - 1, row))
        return (col, row)

    def cell_center(self, index):
        col = index % self.nav_cols
        row = index // self.nav_cols
        return (self.min_x + (col + 0.5) * NAV_CELL, self.min_y + (row + 0.5) * NAV_CELL)

    def nearest_free_cell(self, col, row):
        # Index of the closest walkable cell (searching a few rings out), or -1.
        for ring in range(0, 5):
            for dr in range(-ring, ring + 1):
                for dc in range(-ring, ring + 1):
                    if max(abs(dc), abs(dr)) != ring:
                        continue
                    c = col + dc
                    r = row + dr
                    if c < 0 or c >= self.nav_cols or r < 0 or r >= self.nav_rows:
                        continue
                    index = r * self.nav_cols + c
                    if self.nav_free[index]:
                        return index
        return -1

    def find_path(self, sx, sy, gx, gy):
        # A* over the navigation grid. Returns a list of (x, y) waypoints, or [].
        if not self.nav_ready:
            self.build_nav()
        cols = self.nav_cols
        rows = self.nav_rows
        free = self.nav_free

        start_cell = self.cell_of(sx, sy)
        goal_cell = self.cell_of(gx, gy)
        start = self.nearest_free_cell(start_cell[0], start_cell[1])
        goal = self.nearest_free_cell(goal_cell[0], goal_cell[1])
        if start < 0 or goal < 0:
            return []
        if start == goal:
            return [(gx, gy)]

        goal_col = goal % cols
        goal_row = goal // cols
        frontier = [(0.0, start)]
        came_from = {start: -1}
        cost = {start: 0.0}
        found = False

        while len(frontier) > 0:
            current = heapq.heappop(frontier)[1]
            if current == goal:
                found = True
                break
            col = current % cols
            row = current // cols
            for step in NAV_STEPS:
                nc = col + step[0]
                nr = row + step[1]
                if nc < 0 or nc >= cols or nr < 0 or nr >= rows:
                    continue
                index = nr * cols + nc
                if not free[index]:
                    continue
                if step[0] != 0 and step[1] != 0:
                    # no cutting corners around a wall
                    if not free[row * cols + nc] or not free[nr * cols + col]:
                        continue
                new_cost = cost[current] + step[2]
                if index not in cost or new_cost < cost[index]:
                    cost[index] = new_cost
                    dx = abs(nc - goal_col)
                    dy = abs(nr - goal_row)
                    estimate = (dx + dy) - 0.586 * min(dx, dy)
                    heapq.heappush(frontier, (new_cost + estimate, index))
                    came_from[index] = current

        if not found:
            return []

        path = []
        node = goal
        while node != start:
            path.append(self.cell_center(node))
            node = came_from[node]
        path.reverse()
        return path

    def update(self, delta_time):
        for obstacle in self.obstacles:
            obstacle.flash = max(0.0, obstacle.flash - delta_time * 3.0)


_default_arena = None


def default_arena():
    # The plain rectangle used behind the menus.
    global _default_arena
    if _default_arena is None:
        _default_arena = Arena("rect", [])
    return _default_arena


def make_arena(level):
    return Arena(level["arena"], level["obstacles"], level_bounds(level), level_radius(level))


# ------------------------------------------------------------------ effects

class Pulse:
    # An expanding ring that fades out.
    def __init__(self, x, y, color, max_radius, duration):
        self.x = x
        self.y = y
        self.color = color
        self.max_radius = max_radius
        self.duration = duration
        self.age = 0.0

    def update(self, delta_time):
        self.age += delta_time

    def is_done(self):
        return self.age >= self.duration

    def draw(self):
        t = self.age / self.duration
        radius = 4 + t * self.max_radius
        alpha = (1.0 - t) * 255
        arcade.draw_circle_outline(self.x, self.y, radius,
                                   with_alpha(self.color, alpha * 0.25), 12)
        arcade.draw_circle_outline(self.x, self.y, radius,
                                   with_alpha(self.color, alpha), 3)
        arcade.draw_circle_outline(self.x, self.y, radius * 0.7,
                                   with_alpha(self.color, alpha * 0.4), 2)


class ObstacleTrace:
    # The outline of an obstacle drawing itself in, with a bright head that
    # runs around the edge. It is only light: the real obstacle is added when
    # the trace is finished. Draw it between glow_on and glow_off.
    def __init__(self, spec, duration):
        self.spec = spec
        self.duration = duration
        self.age = 0.0

    def update(self, delta_time):
        self.age += delta_time

    def is_done(self):
        return self.age >= self.duration

    def draw_piece(self, x0, y0, x1, y1):
        arcade.draw_line(x0, y0, x1, y1, with_alpha(CONDUIT_COLOR, 60), 12)
        arcade.draw_line(x0, y0, x1, y1, WHITE_HOT, 2)

    def draw(self):
        # The last stretch holds the full outline so there is no gap before the flash.
        t = min(1.0, self.age / (self.duration * 0.85))
        spec = self.spec
        x = spec[1]
        y = spec[2]
        head = (x, y)

        if spec[0] == "rect":
            left = x - spec[3] / 2
            right = x + spec[3] / 2
            bottom = y - spec[4] / 2
            top = y + spec[4] / 2
            arcade.draw_lrbt_rectangle_filled(left, right, bottom, top,
                                              with_alpha(CONDUIT_COLOR, 40 * t))
            corners = [(left, bottom), (right, bottom), (right, top), (left, top), (left, bottom)]
            remaining = t * 2 * (spec[3] + spec[4])
            head = corners[0]
            for i in range(4):
                if remaining <= 0:
                    break
                a = corners[i]
                b = corners[i + 1]
                length = math.hypot(b[0] - a[0], b[1] - a[1])
                portion = min(1.0, remaining / length)
                end = (a[0] + (b[0] - a[0]) * portion, a[1] + (b[1] - a[1]) * portion)
                self.draw_piece(a[0], a[1], end[0], end[1])
                head = end
                remaining -= length
        else:
            radius = spec[3]
            sweep = 360 * t
            arcade.draw_circle_filled(x, y, radius, with_alpha(CONDUIT_COLOR, 40 * t))
            if sweep > 1:
                arcade.draw_arc_outline(x, y, radius * 2, radius * 2,
                                        with_alpha(CONDUIT_COLOR, 60), 0, sweep, 12)
                arcade.draw_arc_outline(x, y, radius * 2, radius * 2,
                                        WHITE_HOT, 0, sweep, 2)
            angle = math.radians(sweep)
            head = (x + radius * math.cos(angle), y + radius * math.sin(angle))

        if t < 1.0:
            arcade.draw_circle_filled(head[0], head[1], 9, with_alpha(WHITE_HOT, 70))
            arcade.draw_circle_filled(head[0], head[1], 3.5, WHITE_HOT)


class WallFlash:
    # A stretch of wall lights up where a disc hit it, then fades.
    # It follows the wall, so it bends around circles and octagons.
    def __init__(self, arena, distance, color):
        self.arena = arena
        self.distance = distance
        self.color = color
        self.age = 0.0
        self.duration = 0.55

    def update(self, delta_time):
        self.age += delta_time

    def is_done(self):
        return self.age >= self.duration

    def draw(self):
        t = self.age / self.duration
        fade = (1.0 - t) * (1.0 - t)
        half = 50 + t * 130
        hot = mix(self.color, WHITE_HOT, 0.6)
        step = 12
        count = int(half * 2 / step)
        previous = None
        previous_weight = 0.0
        for i in range(count + 1):
            s = -half + i * step
            point = self.arena.point_at(self.distance + s)
            weight = 1.0 - abs(s) / half
            if previous is not None:
                w = (weight + previous_weight) / 2
                arcade.draw_line(previous[0], previous[1], point[0], point[1],
                                 with_alpha(self.color, 70 * w * fade), 14)
                arcade.draw_line(previous[0], previous[1], point[0], point[1],
                                 with_alpha(hot, 255 * w * fade), 3)
            previous = point
            previous_weight = weight


class Derez:
    # Tron-style shatter: the avatar breaks into little glowing cubes.
    def __init__(self, x, y, color):
        self.age = 0.0
        self.duration = 1.1
        self.shards = []
        for i in range(48):
            angle = random.uniform(0, math.tau)
            speed = random.uniform(50, 320)
            shard = {
                "x": x + random.uniform(-8, 8),
                "y": y + random.uniform(-8, 8),
                "vx": math.cos(angle) * speed,
                "vy": math.sin(angle) * speed,
                "size": random.uniform(3, 8),
                "life": random.uniform(0.5, 1.1),
                "color": mix(color, WHITE_HOT, random.uniform(0.0, 0.6)),
            }
            self.shards.append(shard)

    def update(self, delta_time):
        self.age += delta_time
        drag = 0.96
        for shard in self.shards:
            shard["x"] += shard["vx"] * delta_time
            shard["y"] += shard["vy"] * delta_time
            shard["vx"] *= drag
            shard["vy"] *= drag

    def is_done(self):
        return self.age >= self.duration

    def draw(self):
        for shard in self.shards:
            t = self.age / shard["life"]
            if t >= 1.0:
                continue
            size = shard["size"] * (1.0 - t * 0.5)
            arcade.draw_lbwh_rectangle_filled(shard["x"] - size / 2,
                                              shard["y"] - size / 2,
                                              size, size,
                                              with_alpha(shard["color"], (1.0 - t) * 255))


class DataStreak:
    # A pulse of light that runs along a floor grid line.
    def __init__(self, arena):
        self.arena = arena
        self.reset(True)

    def reset(self, first=False):
        segment = random.choice(self.arena.streak_segments)
        self.horizontal = segment[0]
        self.line = segment[1]
        self.start = segment[2]
        self.end = segment[3]
        self.direction = random.choice([-1, 1])
        self.speed = random.uniform(160, 340)
        self.length = random.uniform(80, 170)

        if first:
            self.pos = random.uniform(self.start, self.end)
        elif self.direction == 1:
            self.pos = self.start - random.uniform(0, 300)
        else:
            self.pos = self.end + random.uniform(0, 300)

    def update(self, delta_time):
        self.pos += self.direction * self.speed * delta_time
        if self.direction == 1 and self.pos - self.length > self.end:
            self.reset()
        elif self.direction == -1 and self.pos + self.length < self.start:
            self.reset()

    def point(self, along):
        if self.horizontal:
            return (along, self.line)
        return (self.line, along)

    def is_visible(self, view):
        # view is (left, bottom, right, top) or None for "always draw".
        if view is None:
            return True
        tail = self.pos - self.direction * self.length
        low = min(self.pos, tail)
        high = max(self.pos, tail)
        if self.horizontal:
            if self.line < view[1] or self.line > view[3]:
                return False
            return high >= view[0] and low <= view[2]
        if self.line < view[0] or self.line > view[2]:
            return False
        return high >= view[1] and low <= view[3]

    def draw(self):
        segments = 8
        step = self.length / segments
        dim = STREAK_BRIGHTNESS
        for i in range(segments):
            a0 = self.pos - self.direction * i * step
            a1 = self.pos - self.direction * (i + 1) * step
            p0 = self.point(a0)
            p1 = self.point(a1)
            alpha = (1.0 - i / segments) * 200 * dim
            arcade.draw_line(p0[0], p0[1], p1[0], p1[1],
                             with_alpha(CONDUIT_COLOR, alpha * 0.3), 6)
            arcade.draw_line(p0[0], p0[1], p1[0], p1[1],
                             with_alpha(CONDUIT_COLOR, alpha), 2)
        head = self.point(self.pos)
        arcade.draw_circle_filled(head[0], head[1], 6, with_alpha(WHITE_HOT, 90 * dim))
        arcade.draw_circle_filled(head[0], head[1], 2.5, with_alpha(WHITE_HOT, 255 * dim))


class PerimeterLight:
    # Light that flows around the border conduit like liquid.
    def __init__(self, arena, start, speed):
        self.arena = arena
        self.distance = start
        self.speed = speed

    def update(self, delta_time):
        self.distance += self.speed * delta_time

    def draw(self):
        segments = 16
        step = 10
        for i in range(segments):
            p0 = self.arena.point_at(self.distance - i * step)
            p1 = self.arena.point_at(self.distance - (i + 1) * step)
            alpha = (1.0 - i / segments) * 255
            arcade.draw_line(p0[0], p0[1], p1[0], p1[1],
                             with_alpha(CONDUIT_COLOR, alpha * 0.3), 9)
            arcade.draw_line(p0[0], p0[1], p1[0], p1[1],
                             with_alpha(WHITE_HOT, alpha), 3)


# ------------------------------------------------------------------ game objects

class Disc:
    def __init__(self, owner):
        self.owner = owner
        self.x = owner.x
        self.y = owner.y
        self.vx = 0.0
        self.vy = 0.0
        self.state = HELD
        self.age = 0.0
        self.flash = 0.0  # brightness boost after hitting a wall
        self.spin = 0.0
        self.trail = []

    def throw(self, angle):
        self.state = FLYING
        self.age = 0.0
        self.vx = math.cos(angle) * DISC_SPEED
        self.vy = math.sin(angle) * DISC_SPEED

    def recall(self):
        if self.state == FLYING:
            self.state = RETURNING

    def update(self, delta_time, effects, aim_angle, arena):
        self.flash = max(0.0, self.flash - delta_time * 3.0)

        if self.state == HELD:
            self.spin += 100 * delta_time
            self.trail = []
            self.x = self.owner.x + math.cos(aim_angle) * HOLD_DISTANCE
            self.y = self.owner.y + math.sin(aim_angle) * HOLD_DISTANCE
            return

        self.spin += 620 * delta_time
        self.age += delta_time

        if self.state == RETURNING:
            dx = self.owner.x - self.x
            dy = self.owner.y - self.y
            dist = math.hypot(dx, dy)
            if dist > 0:
                self.vx = dx / dist * RECALL_SPEED
                self.vy = dy / dist * RECALL_SPEED

        self.x += self.vx * delta_time
        self.y += self.vy * delta_time

        # A recalled disc phases through obstacles so it can always find its owner.
        self.bounce(effects, arena, self.state != RETURNING)

        self.trail.append((self.x, self.y))
        if len(self.trail) > 12:
            self.trail.pop(0)

        # Catching
        if self.owner.alive and self.age > CATCH_DELAY:
            dist_to_owner = math.hypot(self.owner.x - self.x, self.owner.y - self.y)
            if dist_to_owner < CATCH_RADIUS:
                self.state = HELD
                self.vx = 0.0
                self.vy = 0.0
                self.flash = 1.0
                effects.append(Pulse(self.owner.x, self.owner.y,
                                     self.owner.color, 50, 0.3))

    def bounce(self, effects, arena, with_obstacles):
        color = self.owner.color
        hit = False

        for edge in arena.edges:
            dist = (self.x - edge.ax) * edge.nx + (self.y - edge.ay) * edge.ny
            if dist < DISC_RADIUS:
                self.x += edge.nx * (DISC_RADIUS - dist)
                self.y += edge.ny * (DISC_RADIUS - dist)
                speed_in = self.vx * edge.nx + self.vy * edge.ny
                if speed_in < 0:
                    self.vx -= 2 * speed_in * edge.nx
                    self.vy -= 2 * speed_in * edge.ny
                    along = (self.x - edge.ax) * edge.tx + (self.y - edge.ay) * edge.ty
                    along = max(0.0, min(edge.length, along))
                    effects.append(WallFlash(arena, edge.start + along, color))
                    hit = True

        if with_obstacles:
            for obstacle in arena.obstacles:
                result = obstacle.collide(self.x, self.y, DISC_RADIUS)
                if result is None:
                    continue
                nx = result[0]
                ny = result[1]
                self.x += nx * result[2]
                self.y += ny * result[2]
                speed_in = self.vx * nx + self.vy * ny
                if speed_in < 0:
                    self.vx -= 2 * speed_in * nx
                    self.vy -= 2 * speed_in * ny
                    obstacle.flash = 1.0
                    obstacle.flash_color = color
                    effects.append(Pulse(result[3], result[4], color, 50, 0.35))
                    hit = True

        if hit:
            self.flash = 1.0
            effects.append(Pulse(self.x, self.y, color, 60, 0.4))

    def draw_trail(self):
        # Ghost rings left behind a flying disc. Call between glow_on and glow_off.
        count = len(self.trail)
        for i in range(count):
            t = (i + 1) / count
            tx = self.trail[i][0]
            ty = self.trail[i][1]
            arcade.draw_circle_outline(tx, ty, DISC_RADIUS * (0.5 + 0.5 * t),
                                       with_alpha(self.owner.color, 80 * t * t), 3)

    def draw(self):
        color = self.owner.color
        bright = mix(color, WHITE_HOT, 0.45)
        r = DISC_RADIUS
        boost = 1.0 + self.flash * 0.9

        glow_on()
        arcade.draw_circle_outline(self.x, self.y, r, with_alpha(color, 22 * boost), 22)
        arcade.draw_circle_outline(self.x, self.y, r, with_alpha(color, 45 * boost), 13)
        arcade.draw_circle_outline(self.x, self.y, r, with_alpha(color, 110 * boost), 7)
        glow_off()

        # dark face, bright rim, thin inner ring, three spinning arcs
        arcade.draw_circle_filled(self.x, self.y, r, (4, 6, 12, 255))
        arcade.draw_circle_outline(self.x, self.y, r, bright, 3)
        arcade.draw_circle_outline(self.x, self.y, r * 0.5, with_alpha(color, 220), 2)
        for i in range(3):
            start = self.spin + i * 120
            arcade.draw_arc_outline(self.x, self.y, r * 1.5, r * 1.5,
                                    with_alpha(bright, 230), start, start + 60, 2)


class Fighter:
    def __init__(self, x, y, color, team):
        self.start_x = x
        self.start_y = y
        self.x = x
        self.y = y
        self.color = color
        self.team = team
        self.alive = True
        self.respawn_timer = 0.0
        self.facing = 0.0
        self.trail = []
        self.trail_decay = 0.0
        self.disc = Disc(self)

    def kill(self, effects):
        self.alive = False
        self.respawn_timer = RESPAWN_TIME
        self.trail = []
        effects.append(Derez(self.x, self.y, self.color))
        effects.append(Pulse(self.x, self.y, self.color, 130, 0.6))
        effects.append(Pulse(self.x, self.y, WHITE_HOT, 70, 0.35))

    def respawn(self):
        self.alive = True
        self.x = self.start_x
        self.y = self.start_y
        self.trail = []
        self.disc.state = HELD
        self.disc.vx = 0.0
        self.disc.vy = 0.0

    def update_trail(self, delta_time, moved):
        if moved:
            self.trail.append((self.x, self.y))
            if len(self.trail) > 18:
                self.trail.pop(0)
        else:
            self.trail_decay += delta_time
            if self.trail_decay > 0.03 and len(self.trail) > 0:
                self.trail.pop(0)
                self.trail_decay = 0.0

    def draw_trail(self):
        # Light left behind while moving. Call between glow_on and glow_off.
        count = len(self.trail)
        for i in range(1, count):
            t = i / count
            a = self.trail[i - 1]
            b = self.trail[i]
            arcade.draw_line(a[0], a[1], b[0], b[1],
                             with_alpha(self.color, 70 * t), 8)
            arcade.draw_line(a[0], a[1], b[0], b[1],
                             with_alpha(mix(self.color, WHITE_HOT, 0.5), 170 * t), 2)

    def draw(self):
        if not self.alive:
            return

        points = []
        for local in BODY_POINTS:
            points.append(to_world(self.x, self.y, self.facing, local[0], local[1]))

        bright = mix(self.color, WHITE_HOT, 0.3)

        glow_on()
        arcade.draw_polygon_outline(points, with_alpha(self.color, 35), 12)
        arcade.draw_polygon_outline(points, with_alpha(self.color, 90), 6)
        glow_off()

        # dark suit with a lit outline
        arcade.draw_polygon_filled(points, (6, 8, 14, 255))
        arcade.draw_polygon_outline(points, bright, 2)

        # circuit stripes down the back, one spine, one on each side
        stripes = [(-12, 0, 11, 0), (-10, 5, 6, 5), (-10, -5, 6, -5)]
        for s in stripes:
            a = to_world(self.x, self.y, self.facing, s[0], s[1])
            b = to_world(self.x, self.y, self.facing, s[2], s[3])
            arcade.draw_line(a[0], a[1], b[0], b[1], with_alpha(self.color, 200), 1.5)

        # helmet
        helmet = to_world(self.x, self.y, self.facing, 4, 0)
        arcade.draw_circle_filled(helmet[0], helmet[1], 5.5, (6, 8, 14, 255))
        arcade.draw_circle_outline(helmet[0], helmet[1], 5.5, bright, 2)
        visor = to_world(self.x, self.y, self.facing, 6.5, 0)
        arcade.draw_circle_filled(visor[0], visor[1], 1.8, WHITE_HOT)


class EnemyBrain:
    # Placeholder AI for one enemy. Small levels: roams (if the level says so),
    # aims at the player with some error, throws, then recalls the disc.
    # Levels with "hunt": the enemy pathfinds through the rooms toward the
    # player, strafes once it has a clear line of sight, and only throws when
    # it can actually see you. Swap this out for real dodging later.
    def __init__(self, fighter, level, arena, delay):
        self.fighter = fighter
        self.level = level
        self.arena = arena
        self.hunt = level.get("hunt", False)
        self.aim = math.pi
        self.move_angle = math.pi
        self.think_timer = level["interval"] + delay
        self.prev_state = HELD
        self.target_x = fighter.x
        self.target_y = fighter.y
        self.move_timer = 0.0
        self.path = []
        self.path_timer = random.uniform(0.0, 0.5)
        self.strafing = False
        self.has_los = True
        self.had_los = False

    def update(self, delta_time, player):
        fighter = self.fighter

        self.has_los = True
        if self.hunt and fighter.alive and player.alive:
            self.has_los = self.arena.line_clear(fighter.x, fighter.y,
                                                 player.x, player.y, DISC_RADIUS)

        moved = False
        if fighter.alive:
            if self.hunt:
                moved = self.update_hunt_movement(delta_time, player)
            else:
                moved = self.update_movement(delta_time, player)
        fighter.update_trail(delta_time, moved)
        if not fighter.alive:
            return

        if player.alive:
            if self.has_los:
                self.aim = math.atan2(player.y - fighter.y, player.x - fighter.x)
            else:
                self.aim = self.move_angle
        fighter.facing = self.aim

        disc = fighter.disc
        if self.prev_state != HELD and disc.state == HELD:
            self.think_timer = self.level["interval"]
        self.prev_state = disc.state

        # A short reaction delay when the player first comes into view.
        if self.hunt and self.has_los and not self.had_los:
            self.think_timer = max(self.think_timer, 0.35)
        self.had_los = self.has_los

        self.think_timer -= delta_time
        if self.think_timer <= 0:
            if disc.state == HELD:
                if player.alive and self.has_los:
                    error = random.uniform(-self.level["error"], self.level["error"])
                    disc.throw(self.aim + error)
                    self.think_timer = 0.9
            elif disc.state == FLYING:
                disc.recall()
                self.think_timer = 0.4

    def update_movement(self, delta_time, player):
        speed = self.level["speed"]
        if speed <= 0:
            return False
        fighter = self.fighter
        self.move_timer -= delta_time
        dx = self.target_x - fighter.x
        dy = self.target_y - fighter.y
        dist = math.hypot(dx, dy)
        if self.move_timer <= 0 or dist < 6:
            point = self.arena.random_point(PLAYER_RADIUS + 16, player.x, player.y, 160)
            if point is not None:
                self.target_x = point[0]
                self.target_y = point[1]
            self.move_timer = random.uniform(1.2, 2.4)
            return False
        step = min(dist, speed * delta_time)
        fighter.x += dx / dist * step
        fighter.y += dy / dist * step
        fighter.x, fighter.y = self.arena.constrain(fighter.x, fighter.y, PLAYER_RADIUS)
        return True

    # ------------------------------------------------------------ hunting

    def step_toward(self, target_x, target_y, speed, delta_time):
        fighter = self.fighter
        dx = target_x - fighter.x
        dy = target_y - fighter.y
        dist = math.hypot(dx, dy)
        if dist < 0.001:
            return False
        step = min(dist, speed * delta_time)
        fighter.x += dx / dist * step
        fighter.y += dy / dist * step
        self.move_angle = math.atan2(dy, dx)
        fighter.x, fighter.y = self.arena.constrain(fighter.x, fighter.y, PLAYER_RADIUS)
        return True

    def update_hunt_movement(self, delta_time, player):
        speed = self.level["speed"]
        if speed <= 0 or not player.alive:
            return False
        fighter = self.fighter
        dist = math.hypot(player.x - fighter.x, player.y - fighter.y)
        if self.has_los and dist < HUNT_RANGE:
            return self.strafe(delta_time, speed)
        return self.follow_path(delta_time, player, speed)

    def strafe(self, delta_time, speed):
        fighter = self.fighter
        if not self.strafing:
            self.strafing = True
            self.move_timer = 0.0
        self.move_timer -= delta_time
        dist = math.hypot(self.target_x - fighter.x, self.target_y - fighter.y)
        if self.move_timer <= 0 or dist < 6:
            point = self.arena.nearby_point(fighter.x, fighter.y, 170, PLAYER_RADIUS + 16)
            if point is not None:
                self.target_x = point[0]
                self.target_y = point[1]
            else:
                self.target_x = fighter.x
                self.target_y = fighter.y
            self.move_timer = random.uniform(0.8, 1.6)
            return False
        return self.step_toward(self.target_x, self.target_y, speed * 0.8, delta_time)

    def follow_path(self, delta_time, player, speed):
        fighter = self.fighter
        arena = self.arena
        self.strafing = False

        self.path_timer -= delta_time
        if self.path_timer <= 0:
            self.path = arena.find_path(fighter.x, fighter.y, player.x, player.y)
            self.path_timer = 0.5

        # Skip waypoints that can be reached in a straight line.
        while len(self.path) > 1 and arena.line_clear(fighter.x, fighter.y,
                                                      self.path[1][0], self.path[1][1],
                                                      PLAYER_RADIUS + 2):
            self.path.pop(0)

        if len(self.path) == 0:
            return False
        target = self.path[0]
        if math.hypot(target[0] - fighter.x, target[1] - fighter.y) < 10:
            self.path.pop(0)
            return False
        return self.step_toward(target[0], target[1], speed, delta_time)


class DemoOwner:
    # Stand-in owner so menu screens can bounce discs around with no fighter.
    def __init__(self, color):
        self.x = 0.0
        self.y = 0.0
        self.color = color
        self.alive = False


# ------------------------------------------------------------------ screen scaling and camera

class Screen:
    # Keeps the 1000x680 logical layout and scales it to whatever the window is.
    # Menus and the HUD use the fixed camera. The game world uses a second
    # camera that can be moved around (see FollowCamera). Text uses a third
    # camera that works in real window pixels (see CrispText).
    active = None   # the screen currently being drawn

    def __init__(self):
        self.camera = arcade.Camera2D()
        self.world_camera = arcade.Camera2D()
        self.text_camera = arcade.Camera2D()
        self.scale = 1.0
        self.pixel_width = WIDTH
        self.pixel_height = HEIGHT
        self.view_width = WIDTH
        self.view_height = HEIGHT
        self.update_size(WIDTH, HEIGHT)

    def configure(self, camera):
        camera.match_window(viewport=True, projection=False, position=False)
        camera.projection = arcade.LRBT(-self.view_width / 2, self.view_width / 2,
                                        -self.view_height / 2, self.view_height / 2)

    def configure_text(self):
        # One unit is one real pixel, with (0, 0) at the bottom left.
        self.text_camera.match_window(viewport=True, projection=False, position=False)
        self.text_camera.projection = arcade.LRBT(-self.pixel_width / 2, self.pixel_width / 2,
                                                  -self.pixel_height / 2, self.pixel_height / 2)
        self.text_camera.position = (self.pixel_width / 2, self.pixel_height / 2)

    def update_size(self, width, height):
        self.pixel_width = max(1, width)
        self.pixel_height = max(1, height)
        self.scale = min(self.pixel_width / WIDTH, self.pixel_height / HEIGHT)
        self.view_width = self.pixel_width / self.scale
        self.view_height = self.pixel_height / self.scale
        self.configure(self.camera)
        self.configure(self.world_camera)
        self.configure_text()
        self.camera.position = (WIDTH / 2, HEIGHT / 2)

    def use(self):
        Screen.active = self
        self.camera.use()

    def use_world(self, x, y):
        Screen.active = self
        self.world_camera.position = (x, y)
        self.world_camera.use()

    def view_rect(self, x, y, pad):
        # What the world camera can see (left, bottom, right, top), plus padding.
        half_w = self.view_width / 2 + pad
        half_h = self.view_height / 2 + pad
        return (x - half_w, y - half_h, x + half_w, y + half_h)

    def to_logical(self, x, y):
        lx = (x - self.pixel_width / 2) / self.scale + WIDTH / 2
        ly = (y - self.pixel_height / 2) / self.scale + HEIGHT / 2
        return (lx, ly)

    def to_pixels(self, lx, ly):
        px = (lx - WIDTH / 2) * self.scale + self.pixel_width / 2
        py = (ly - HEIGHT / 2) * self.scale + self.pixel_height / 2
        return (px, py)


class FollowCamera:
    # Glides after a target. It never shows anything outside the arena frame,
    # and if the arena is smaller than the view on an axis it just centers.
    def __init__(self):
        self.x = CENTER_X
        self.y = CENTER_Y

    def clamp_axis(self, value, low, high, view_size):
        if high - low <= view_size:
            return (low + high) / 2
        half = view_size / 2
        return max(low + half, min(high - half, value))

    def clamp(self, x, y, arena, screen):
        frame = arena.frame
        return (self.clamp_axis(x, frame[0], frame[2], screen.view_width),
                self.clamp_axis(y, frame[1], frame[3], screen.view_height))

    def snap(self, x, y, arena, screen):
        self.x, self.y = self.clamp(x, y, arena, screen)

    def update(self, delta_time, target_x, target_y, arena, screen):
        goal_x, goal_y = self.clamp(target_x, target_y, arena, screen)
        blend = 1.0 - math.exp(-FOLLOW_RATE * delta_time)
        self.x += (goal_x - self.x) * blend
        self.y += (goal_y - self.y) * blend
        self.x, self.y = self.clamp(self.x, self.y, arena, screen)


# ------------------------------------------------------------------ backdrop

class ArenaBackdrop:
    # The glowing grid floor, brutalist frame, and moving lights.
    # Shared by the menus and the game.
    def __init__(self, arena=None):
        if arena is None:
            arena = default_arena()
        self.arena = arena
        self.clock = 0.0
        self.effects = []
        self.flashes = []
        self.demo_discs = []

        # Bigger arenas get more moving lights (only the visible ones are drawn).
        area = (arena.max_x - arena.min_x) * (arena.max_y - arena.min_y)
        streak_count = int(12 * area / (880 * 560))
        streak_count = max(12, min(60, streak_count))
        self.streaks = []
        for i in range(streak_count):
            self.streaks.append(DataStreak(arena))

        light_count = max(4, int(arena.perimeter / 1200))
        self.perimeter_lights = []
        for i in range(light_count):
            self.perimeter_lights.append(PerimeterLight(arena, i * arena.perimeter / light_count, 280))

    def add_demo_discs(self):
        for color in [PLAYER_COLOR, ENEMY_COLOR]:
            disc = Disc(DemoOwner(color))
            point = self.arena.random_point(100, CENTER_X, CENTER_Y, 0)
            disc.x = point[0]
            disc.y = point[1]
            angle = random.uniform(0, math.tau)
            disc.state = FLYING
            disc.vx = math.cos(angle) * 280
            disc.vy = math.sin(angle) * 280
            self.demo_discs.append(disc)

    def update(self, delta_time):
        self.clock += delta_time
        self.arena.update(delta_time)
        for streak in self.streaks:
            streak.update(delta_time)
        for light in self.perimeter_lights:
            light.update(delta_time)
        for disc in self.demo_discs:
            disc.update(delta_time, self.effects, 0.0, self.arena)

        # Wall flashes are drawn on top of the frame, so they live in their own list.
        for effect in list(self.effects):
            if isinstance(effect, WallFlash):
                self.effects.remove(effect)
                self.flashes.append(effect)

        for effect in self.effects:
            effect.update(delta_time)
        for flash in self.flashes:
            flash.update(delta_time)
        self.effects = [e for e in self.effects if not e.is_done()]
        self.flashes = [f for f in self.flashes if not f.is_done()]

    def draw_floor(self):
        cx = self.arena.cx
        cy = self.arena.cy

        # faint sheen in the middle of the glass floor
        glow_on()
        sheen = (30, 90, 140)
        arcade.draw_circle_filled(cx, cy, 420, with_alpha(sheen, 5))
        arcade.draw_circle_filled(cx, cy, 300, with_alpha(sheen, 6))
        arcade.draw_circle_filled(cx, cy, 170, with_alpha(sheen, 7))
        glow_off()

        arcade.draw_lines(self.arena.minor_lines, (60, 150, 200, 22), 1)
        arcade.draw_lines(self.arena.major_lines, (90, 190, 240, 60), 1)

        # center emblem
        ring = (110, 210, 255)
        arcade.draw_circle_outline(cx, cy, 70, with_alpha(ring, 70), 2)
        arcade.draw_circle_outline(cx, cy, 74, with_alpha(ring, 25), 6)
        for i in range(4):
            start = 45 + i * 90 - 20 + self.clock * 8
            arcade.draw_arc_outline(cx, cy, 220, 220,
                                    with_alpha(ring, 70), start, start + 40, 2)

    def draw_streaks(self, view=None):
        # call between glow_on and glow_off
        for streak in self.streaks:
            if streak.is_visible(view):
                streak.draw()

    def draw_effects(self):
        # call between glow_on and glow_off
        for disc in self.demo_discs:
            draw_light_pool(disc.x, disc.y, 130, disc.owner.color, 1.0 + disc.flash * 1.5)
        for effect in self.effects:
            effect.draw()
        for disc in self.demo_discs:
            disc.draw_trail()

    def draw_demo_discs(self):
        for disc in self.demo_discs:
            disc.draw()

    def draw_obstacles(self, view=None):
        for obstacle in self.arena.obstacles:
            if obstacle.is_visible(view):
                obstacle.draw()

    def draw_frame(self):
        # Solid frame everywhere outside the arena. It extends far past the
        # logical screen so a stretched window just sees more frame.
        self.arena.slab.draw()

        # bevel and panel seams
        arcade.draw_polygon_outline(self.arena.outer_points, (38, 46, 64, 255), 2)
        frame = self.arena.frame
        bounds = self.arena.bounds
        frame_left = int(frame[0])
        frame_bottom = int(frame[1])
        frame_right = int(frame[2])
        frame_top = int(frame[3])
        seams = []
        for x in range(frame_left, frame_right + 1, 125):
            seams.append((x, frame_top - 12))
            seams.append((x, frame_top))
            seams.append((x, frame_bottom))
            seams.append((x, frame_bottom + 12))
        for y in range(frame_bottom, frame_top + 1, 85):
            seams.append((frame_left, y))
            seams.append((bounds[0] - 14, y))
            seams.append((bounds[2] + 14, y))
            seams.append((frame_right, y))
        arcade.draw_lines(seams, (28, 34, 48, 255), 2)

    def draw_conduit(self):
        arena = self.arena
        glow_on()
        arcade.draw_polygon_outline(arena.points, with_alpha(CONDUIT_COLOR, 18), 22)
        arcade.draw_polygon_outline(arena.points, with_alpha(CONDUIT_COLOR, 45), 10)
        if len(arena.points) <= 12:
            # fill the notch at each sharp corner
            for point in arena.points:
                arcade.draw_circle_filled(point[0], point[1], 5, with_alpha(CONDUIT_COLOR, 25))
        for light in self.perimeter_lights:
            light.draw()
        for flash in self.flashes:
            flash.draw()
        glow_off()

        arcade.draw_polygon_outline(arena.points, with_alpha(CONDUIT_COLOR, 200), 2)

        # heavy white brackets
        for center in arena.bracket_distances:
            previous = None
            s = -arena.bracket_length
            while s <= arena.bracket_length:
                point = arena.point_at(center + s, 4)
                if previous is not None:
                    arcade.draw_line(previous[0], previous[1], point[0], point[1], WHITE_HOT, 5)
                previous = point
                s += 6


# ------------------------------------------------------------------ menu widgets

class Button:
    def __init__(self, label, x, y, width, height, callback):
        self.label = label
        self.x = x
        self.y = y
        self.width = width
        self.height = height
        self.callback = callback
        self.text = make_text(label, x, y, TEXT_DIM, 18, bold=True)

    def contains(self, lx, ly):
        return (abs(lx - self.x) <= self.width / 2 and
                abs(ly - self.y) <= self.height / 2)

    def draw(self, selected, clock):
        left = self.x - self.width / 2
        right = self.x + self.width / 2
        bottom = self.y - self.height / 2
        top = self.y + self.height / 2

        arcade.draw_lrbt_rectangle_filled(left, right, bottom, top, (6, 9, 16, 235))
        if selected:
            glow_on()
            arcade.draw_lrbt_rectangle_filled(left, right, bottom, top,
                                              with_alpha(PLAYER_COLOR, 20))
            arcade.draw_lrbt_rectangle_outline(left, right, bottom, top,
                                               with_alpha(PLAYER_COLOR, 45), 12)
            arcade.draw_lrbt_rectangle_outline(left, right, bottom, top,
                                               with_alpha(PLAYER_COLOR, 90), 5)
            glow_off()
            arcade.draw_lrbt_rectangle_outline(left, right, bottom, top, CONDUIT_COLOR, 2)
            nudge = math.sin(clock * 6) * 3
            arcade.draw_triangle_filled(left - 22 + nudge, self.y + 8,
                                        left - 22 + nudge, self.y - 8,
                                        left - 10 + nudge, self.y, PLAYER_COLOR)
            arcade.draw_triangle_filled(right + 22 - nudge, self.y + 8,
                                        right + 22 - nudge, self.y - 8,
                                        right + 10 - nudge, self.y, PLAYER_COLOR)
            self.text.color = WHITE_HOT
        else:
            arcade.draw_lrbt_rectangle_outline(left, right, bottom, top, (50, 90, 120, 255), 2)
            self.text.color = TEXT_DIM
        self.text.draw()


class MenuList:
    def __init__(self, entries, center_x, top_y, spacing=62, width=380, height=48):
        self.buttons = []
        for i in range(len(entries)):
            label = entries[i][0]
            callback = entries[i][1]
            self.buttons.append(Button(label, center_x, top_y - i * spacing,
                                       width, height, callback))
        self.selected = 0

    def move(self, step):
        self.selected = (self.selected + step) % len(self.buttons)

    def activate(self):
        self.buttons[self.selected].callback()

    def mouse_moved(self, lx, ly):
        for i in range(len(self.buttons)):
            if self.buttons[i].contains(lx, ly):
                self.selected = i

    def mouse_pressed(self, lx, ly):
        for i in range(len(self.buttons)):
            if self.buttons[i].contains(lx, ly):
                self.selected = i
                self.activate()
                return True
        return False

    def key_pressed(self, key):
        if key == arcade.key.UP or key == arcade.key.W:
            self.move(-1)
        elif key == arcade.key.DOWN or key == arcade.key.S:
            self.move(1)
        elif key == arcade.key.ENTER or key == arcade.key.NUM_ENTER or key == arcade.key.SPACE:
            self.activate()

    def draw(self, clock):
        for i in range(len(self.buttons)):
            self.buttons[i].draw(i == self.selected, clock)


def draw_level_icon(cx, cy, level, unlocked, max_width, max_height, max_scale):
    # Tiny map of a level: arena outline, obstacles, and where everyone starts.
    bounds = level_bounds(level)
    mid_x = (bounds[0] + bounds[2]) / 2
    mid_y = (bounds[1] + bounds[3]) / 2
    width = bounds[2] - bounds[0]
    height = bounds[3] - bounds[1]
    scale = min(max_scale, max_width / width, max_height / height)

    line_color = CONDUIT_COLOR
    fill_color = (40, 70, 95)
    if not unlocked:
        line_color = (60, 85, 105)
        fill_color = (30, 45, 60)

    points = []
    for p in arena_points(level["arena"], bounds, level_radius(level)):
        points.append((cx + (p[0] - mid_x) * scale, cy + (p[1] - mid_y) * scale))
    arcade.draw_polygon_outline(points, line_color, 2)

    for spec in level["obstacles"]:
        ox = cx + (spec[1] - mid_x) * scale
        oy = cy + (spec[2] - mid_y) * scale
        if spec[0] == "rect":
            w = max(1.5, spec[3] * scale)
            h = max(1.5, spec[4] * scale)
            arcade.draw_lbwh_rectangle_filled(ox - w / 2, oy - h / 2, w, h, fill_color)
        else:
            arcade.draw_circle_filled(ox, oy, max(1.5, spec[3] * scale), fill_color)

    if unlocked:
        start = level["player_start"]
        arcade.draw_circle_filled(cx + (start[0] - mid_x) * scale,
                                  cy + (start[1] - mid_y) * scale, 3, PLAYER_COLOR)
        for i in range(len(level["enemy_starts"])):
            e = level["enemy_starts"][i]
            arcade.draw_circle_filled(cx + (e[0] - mid_x) * scale,
                                      cy + (e[1] - mid_y) * scale, 3,
                                      ENEMY_COLORS[i % len(ENEMY_COLORS)])


# ------------------------------------------------------------------ views

class BaseView(arcade.View):
    # Handles scaling, F11, FPS counter, and converting mouse positions.
    def __init__(self):
        super().__init__()
        self.screen = Screen()
        self.fps = 60.0
        self.clock = 0.0
        self.fps_text = make_text("", WIDTH - 24, 22, (90, 170, 200), 11, anchor_x="right")

    def on_show_view(self):
        self.screen.update_size(self.window.width, self.window.height)
        self.view_shown()

    def view_shown(self):
        pass

    def on_resize(self, width, height):
        self.screen.update_size(width, height)

    def on_update(self, delta_time):
        self.clock += delta_time
        if delta_time > 0:
            self.fps = self.fps * 0.9 + (1.0 / delta_time) * 0.1
        self.update_view(delta_time)

    def update_view(self, delta_time):
        pass

    def on_key_press(self, key, modifiers):
        if key == arcade.key.F11:
            toggle_fullscreen(self.window)
            return
        self.key_pressed(key, modifiers)

    def key_pressed(self, key, modifiers):
        pass

    def on_mouse_motion(self, x, y, dx, dy):
        lx, ly = self.screen.to_logical(x, y)
        self.mouse_moved(lx, ly)

    def on_mouse_press(self, x, y, button, modifiers):
        lx, ly = self.screen.to_logical(x, y)
        self.mouse_pressed(lx, ly, button)

    def on_mouse_drag(self, x, y, dx, dy, buttons, modifiers):
        lx, ly = self.screen.to_logical(x, y)
        self.mouse_moved(lx, ly)
        self.mouse_dragged(lx, ly)

    def on_mouse_release(self, x, y, button, modifiers):
        self.mouse_released()

    def mouse_moved(self, lx, ly):
        pass

    def mouse_pressed(self, lx, ly, button):
        pass

    def mouse_dragged(self, lx, ly):
        pass

    def mouse_released(self):
        pass

    def draw_fps(self):
        if self.window.save.get("show_fps"):
            self.fps_text.text = "FPS " + str(int(self.fps))
            self.fps_text.draw()

    def draw_backdrop(self, backdrop):
        backdrop.draw_floor()
        glow_on()
        backdrop.draw_streaks()
        backdrop.draw_effects()
        glow_off()
        backdrop.draw_frame()
        backdrop.draw_conduit()
        backdrop.draw_obstacles()
        backdrop.draw_demo_discs()


class MenuView(BaseView):
    def __init__(self):
        super().__init__()
        self.backdrop = ArenaBackdrop()
        self.backdrop.add_demo_discs()

        self.title = make_text("ROME 3999", CENTER_X, 500, WHITE_HOT, 64, bold=True)
        self.title_halo = make_text("ROME 3999", CENTER_X, 500,
                                    with_alpha(PLAYER_COLOR, 55), 64, bold=True)
        self.subtitle = make_text("GLADIATORS OF THE DISTANT FUTURE", CENTER_X, 446,
                                  TEXT_DIM, 14)
        self.menu = None
        self.build_menu()

    def build_menu(self):
        entries = []
        if self.window.save.get("has_played"):
            entries.append(("CONTINUE", self.continue_game))
        entries.append(("PLAY", self.open_mode_select))
        entries.append(("OPTIONS", self.open_options))
        entries.append(("EXIT GAME", self.exit_game))
        self.menu = MenuList(entries, CENTER_X, 370)

    def view_shown(self):
        self.build_menu()

    def continue_game(self):
        save = self.window.save
        level = max(0, min(save.get("unlocked") - 1, save.get("current_level")))
        self.window.show_view(GameView(level))

    def open_mode_select(self):
        self.window.show_view(ModeSelectView(self))

    def open_options(self):
        self.window.show_view(OptionsView(self))

    def exit_game(self):
        arcade.exit()

    def update_view(self, delta_time):
        self.backdrop.update(delta_time)

    def key_pressed(self, key, modifiers):
        self.menu.key_pressed(key)

    def mouse_moved(self, lx, ly):
        self.menu.mouse_moved(lx, ly)

    def mouse_pressed(self, lx, ly, button):
        if button == arcade.MOUSE_BUTTON_LEFT:
            self.menu.mouse_pressed(lx, ly)

    def on_draw(self):
        self.clear()
        self.screen.use()
        self.draw_backdrop(self.backdrop)

        # soft halo: the same text nudged around the main title
        for ox, oy in [(-4, 0), (4, 0), (0, -4), (0, 4), (-3, -3), (3, 3), (-3, 3), (3, -3)]:
            self.title_halo.x = CENTER_X + ox
            self.title_halo.y = 500 + oy
            self.title_halo.draw()
        self.title.draw()
        self.subtitle.draw()
        self.menu.draw(self.clock)
        self.draw_fps()


class LevelSelectView(BaseView):
    COLUMNS = 4
    CARD_WIDTH = 190
    CARD_HEIGHT = 200
    CARD_GAP_X = 24
    CARD_GAP_Y = 20
    FIRST_ROW_Y = 430

    def __init__(self, previous_view):
        super().__init__()
        self.previous_view = previous_view
        self.backdrop = ArenaBackdrop()

        self.title = make_text("GLADIATOR MODE", CENTER_X, 588, WHITE_HOT, 30, bold=True)
        self.subtitle = make_text("CHOOSE YOUR ARENA", CENTER_X, 556, TEXT_DIM, 12)
        self.hint = make_text("ARROWS + ENTER, OR USE THE MOUSE        ESC BACK",
                              CENTER_X, 22, (90, 170, 200), 11)
        self.back_button = Button("< BACK", 125, 30, 150, 40, self.go_back)
        self.prev_button = Button("< PREV", 760, 30, 120, 40, self.prev_page)
        self.next_button = Button("NEXT >", 900, 30, 120, 40, self.next_page)

        count = len(LEVELS)
        self.pages = (count + LEVELS_PER_PAGE - 1) // LEVELS_PER_PAGE
        total = self.COLUMNS * self.CARD_WIDTH + (self.COLUMNS - 1) * self.CARD_GAP_X
        first_x = CENTER_X - total / 2 + self.CARD_WIDTH / 2
        self.card_centers = []
        self.number_texts = []
        self.name_texts = []
        self.info_texts = []
        for i in range(count):
            slot = i % LEVELS_PER_PAGE
            column = slot % self.COLUMNS
            row = slot // self.COLUMNS
            cx = first_x + column * (self.CARD_WIDTH + self.CARD_GAP_X)
            cy = self.FIRST_ROW_Y - row * (self.CARD_HEIGHT + self.CARD_GAP_Y)
            self.card_centers.append((cx, cy))
            level = LEVELS[i]
            self.number_texts.append(make_text(level_label(i), cx, cy + 68, WHITE_HOT, 30, bold=True))
            self.name_texts.append(make_text(level["name"], cx, cy + 36, WHITE_HOT, 12, bold=True))
            info = "1V" + str(level["enemies"]) + "   " + str(level["kills"]) + " KILLS"
            self.info_texts.append(make_text(info, cx, cy - 52, TEXT_DIM, 11))

        save = self.window.save
        self.selected = max(0, min(save.get("unlocked") - 1, save.get("current_level")))
        self.page = self.selected // LEVELS_PER_PAGE
        self.back_selected = False
        self.prev_selected = False
        self.next_selected = False

    def go_back(self):
        self.window.show_view(self.previous_view)

    def select(self, index):
        self.selected = index
        self.page = index // LEVELS_PER_PAGE

    def set_page(self, page):
        page = max(0, min(self.pages - 1, page))
        slot = self.selected % LEVELS_PER_PAGE
        self.page = page
        self.selected = min(len(LEVELS) - 1, page * LEVELS_PER_PAGE + slot)

    def prev_page(self):
        self.set_page(self.page - 1)

    def next_page(self):
        self.set_page(self.page + 1)

    def is_unlocked(self, index):
        return index < self.window.save.get("unlocked")

    def start_level(self, index):
        if self.is_unlocked(index):
            self.window.show_view(GameView(index))

    def update_view(self, delta_time):
        self.backdrop.update(delta_time)

    def key_pressed(self, key, modifiers):
        count = len(LEVELS)
        if key == arcade.key.ESCAPE:
            self.go_back()
        elif key == arcade.key.LEFT or key == arcade.key.A:
            self.select((self.selected - 1) % count)
        elif key == arcade.key.RIGHT or key == arcade.key.D:
            self.select((self.selected + 1) % count)
        elif key == arcade.key.UP or key == arcade.key.W:
            self.select((self.selected - self.COLUMNS) % count)
        elif key == arcade.key.DOWN or key == arcade.key.S:
            self.select((self.selected + self.COLUMNS) % count)
        elif key == arcade.key.PAGEUP:
            self.prev_page()
        elif key == arcade.key.PAGEDOWN:
            self.next_page()
        elif key == arcade.key.ENTER or key == arcade.key.NUM_ENTER or key == arcade.key.SPACE:
            self.start_level(self.selected)

    def card_at(self, lx, ly):
        for slot in range(LEVELS_PER_PAGE):
            index = self.page * LEVELS_PER_PAGE + slot
            if index >= len(LEVELS):
                break
            cx = self.card_centers[index][0]
            cy = self.card_centers[index][1]
            if abs(lx - cx) <= self.CARD_WIDTH / 2 and abs(ly - cy) <= self.CARD_HEIGHT / 2:
                return index
        return -1

    def mouse_moved(self, lx, ly):
        index = self.card_at(lx, ly)
        if index >= 0:
            self.selected = index
        self.back_selected = self.back_button.contains(lx, ly)
        self.prev_selected = self.page > 0 and self.prev_button.contains(lx, ly)
        self.next_selected = self.page < self.pages - 1 and self.next_button.contains(lx, ly)

    def mouse_pressed(self, lx, ly, button):
        if button != arcade.MOUSE_BUTTON_LEFT:
            return
        if self.back_button.contains(lx, ly):
            self.go_back()
            return
        if self.page > 0 and self.prev_button.contains(lx, ly):
            self.prev_page()
            return
        if self.page < self.pages - 1 and self.next_button.contains(lx, ly):
            self.next_page()
            return
        index = self.card_at(lx, ly)
        if index >= 0:
            self.selected = index
            self.start_level(index)

    def draw_card(self, index):
        cx = self.card_centers[index][0]
        cy = self.card_centers[index][1]
        left = cx - self.CARD_WIDTH / 2
        right = cx + self.CARD_WIDTH / 2
        bottom = cy - self.CARD_HEIGHT / 2
        top = cy + self.CARD_HEIGHT / 2
        unlocked = self.is_unlocked(index)
        selected = (index == self.selected)
        level = LEVELS[index]

        arcade.draw_lrbt_rectangle_filled(left, right, bottom, top, (6, 9, 16, 240))
        if selected:
            glow_on()
            arcade.draw_lrbt_rectangle_filled(left, right, bottom, top,
                                              with_alpha(PLAYER_COLOR, 16))
            arcade.draw_lrbt_rectangle_outline(left, right, bottom, top,
                                               with_alpha(PLAYER_COLOR, 45), 14)
            arcade.draw_lrbt_rectangle_outline(left, right, bottom, top,
                                               with_alpha(PLAYER_COLOR, 90), 6)
            glow_off()
            arcade.draw_lrbt_rectangle_outline(left, right, bottom, top, CONDUIT_COLOR, 2)
        else:
            arcade.draw_lrbt_rectangle_outline(left, right, bottom, top, (50, 90, 120, 255), 2)

        # corner ticks
        tick = (90, 190, 240, 255)
        arcade.draw_line(left + 10, top - 10, left + 30, top - 10, tick, 2)
        arcade.draw_line(left + 10, top - 10, left + 10, top - 30, tick, 2)
        arcade.draw_line(right - 10, bottom + 10, right - 30, bottom + 10, tick, 2)
        arcade.draw_line(right - 10, bottom + 10, right - 10, bottom + 30, tick, 2)

        draw_level_icon(cx, cy - 8, level, unlocked, 140, 64, ICON_MAX_SCALE)

        if unlocked:
            number_color = WHITE_HOT
            if not selected:
                number_color = mix(PLAYER_COLOR, WHITE_HOT, 0.25)
            self.number_texts[index].color = number_color
            self.name_texts[index].color = WHITE_HOT
            self.info_texts[index].color = TEXT_DIM
            self.info_texts[index].text = ("1V" + str(level["enemies"]) + "   " +
                                           str(level["kills"]) + " KILLS")

            # difficulty pips
            for p in range(PIP_COUNT):
                px = cx - 59.5 + p * 17
                py = bottom + 22
                arcade.draw_lrbt_rectangle_outline(px - 5, px + 5, py - 5, py + 5,
                                                   ENEMY_COLOR, 2)
                if p < level["difficulty"]:
                    glow_on()
                    arcade.draw_lrbt_rectangle_filled(px - 5, px + 5, py - 5, py + 5,
                                                      with_alpha(ENEMY_COLOR, 200))
                    glow_off()
        else:
            self.number_texts[index].color = (50, 70, 90)
            self.name_texts[index].color = (70, 95, 115)
            self.info_texts[index].color = (70, 95, 115)
            self.info_texts[index].text = "LOCKED"

        self.number_texts[index].draw()
        self.name_texts[index].draw()
        self.info_texts[index].draw()

    def on_draw(self):
        self.clear()
        self.screen.use()
        self.draw_backdrop(self.backdrop)

        self.title.draw()
        self.subtitle.text = "CHOOSE YOUR ARENA     PAGE " + str(self.page + 1) + " / " + str(self.pages)
        self.subtitle.draw()
        for slot in range(LEVELS_PER_PAGE):
            index = self.page * LEVELS_PER_PAGE + slot
            if index >= len(LEVELS):
                break
            self.draw_card(index)
        self.back_button.draw(self.back_selected, self.clock)
        if self.page > 0:
            self.prev_button.draw(self.prev_selected, self.clock)
        if self.page < self.pages - 1:
            self.next_button.draw(self.next_selected, self.clock)
        self.hint.draw()
        self.draw_fps()


MODES = [
    {"id": "gladiator", "name": "GLADIATOR MODE", "blurb": "PROVE YOURSELF",
     "ready": True, "status": str(len(LEVELS)) + " ARENAS"},
    {"id": "endless", "name": "ENDLESS", "blurb": "OUTLAST THE GRID",
     "ready": True, "status": "SURVIVE"},
    {"id": "campaign", "name": "CAMPAIGN", "blurb": "REWRITE THE LEGACY",
     "ready": True, "status": "1 MISSION"},
    {"id": "custom", "name": "CUSTOM", "blurb": "BUILD YOUR OWN BATTLES",
     "ready": False, "status": "COMING SOON"},
]


class ModeSelectView(BaseView):
    CARD_WIDTH = 200
    CARD_HEIGHT = 300
    CARD_SPACING = 215
    CARD_Y = 340

    def __init__(self, previous_view):
        super().__init__()
        self.previous_view = previous_view
        self.backdrop = ArenaBackdrop()

        self.title = make_text("SELECT MODE", CENTER_X, 588, WHITE_HOT, 30, bold=True)
        self.hint = make_text("LEFT / RIGHT + ENTER, OR USE THE MOUSE        ESC BACK",
                              CENTER_X, 22, (90, 170, 200), 11)
        self.back_button = Button("< BACK", 125, 30, 150, 40, self.go_back)

        self.card_xs = []
        self.name_texts = []
        self.blurb_texts = []
        self.status_texts = []
        for i in range(len(MODES)):
            cx = CENTER_X + (i - (len(MODES) - 1) / 2) * self.CARD_SPACING
            self.card_xs.append(cx)
            mode = MODES[i]
            self.name_texts.append(make_text(mode["name"], cx, self.CARD_Y - 30, WHITE_HOT, 15, bold=True))
            self.blurb_texts.append(make_text(mode["blurb"], cx, self.CARD_Y - 62, TEXT_DIM, 11))
            self.status_texts.append(make_text(mode["status"], cx, self.CARD_Y - 112, TEXT_DIM, 12, bold=True))

        self.selected = 0
        self.back_selected = False

    def go_back(self):
        self.window.show_view(self.previous_view)

    def open_mode(self, index):
        mode = MODES[index]
        if mode["id"] == "gladiator":
            self.window.show_view(LevelSelectView(self))
        elif mode["id"] == "endless":
            self.window.show_view(EndlessSetupView(self))
        elif mode["id"] == "campaign":
            self.window.show_view(GameView(0, None, 0))
        else:
            self.window.show_view(PlaceholderView(self, mode["name"], mode["blurb"]))

    def update_view(self, delta_time):
        self.backdrop.update(delta_time)

    def key_pressed(self, key, modifiers):
        count = len(MODES)
        if key == arcade.key.ESCAPE:
            self.go_back()
        elif key == arcade.key.LEFT or key == arcade.key.A or key == arcade.key.UP or key == arcade.key.W:
            self.selected = (self.selected - 1) % count
        elif key == arcade.key.RIGHT or key == arcade.key.D or key == arcade.key.DOWN or key == arcade.key.S:
            self.selected = (self.selected + 1) % count
        elif key == arcade.key.ENTER or key == arcade.key.NUM_ENTER or key == arcade.key.SPACE:
            self.open_mode(self.selected)

    def card_at(self, lx, ly):
        for i in range(len(self.card_xs)):
            if (abs(lx - self.card_xs[i]) <= self.CARD_WIDTH / 2 and
                    abs(ly - self.CARD_Y) <= self.CARD_HEIGHT / 2):
                return i
        return -1

    def mouse_moved(self, lx, ly):
        index = self.card_at(lx, ly)
        if index >= 0:
            self.selected = index
        self.back_selected = self.back_button.contains(lx, ly)

    def mouse_pressed(self, lx, ly, button):
        if button != arcade.MOUSE_BUTTON_LEFT:
            return
        if self.back_button.contains(lx, ly):
            self.go_back()
            return
        index = self.card_at(lx, ly)
        if index >= 0:
            self.selected = index
            self.open_mode(index)

    def draw_icon(self, mode_id, cx, cy, color):
        if mode_id == "gladiator":
            # a disc: rim, inner ring, spinning arcs
            arcade.draw_circle_outline(cx, cy, 38, color, 4)
            arcade.draw_circle_outline(cx, cy, 20, with_alpha(color, 200), 2)
            for i in range(3):
                start = self.clock * 120 + i * 120
                arcade.draw_arc_outline(cx, cy, 58, 58, with_alpha(color, 230),
                                        start, start + 60, 2)
        elif mode_id == "endless":
            # an infinity loop with a light running around it
            previous = None
            for i in range(41):
                t = i * math.tau / 40
                d = 1.0 + math.sin(t) * math.sin(t)
                point = (cx + 46 * math.cos(t) / d, cy + 46 * math.sin(t) * math.cos(t) / d)
                if previous is not None:
                    arcade.draw_line(previous[0], previous[1], point[0], point[1], color, 3)
                previous = point
            t = self.clock * 2.5
            d = 1.0 + math.sin(t) * math.sin(t)
            arcade.draw_circle_filled(cx + 46 * math.cos(t) / d,
                                      cy + 46 * math.sin(t) * math.cos(t) / d, 5, WHITE_HOT)
        elif mode_id == "campaign":
            # a route with three stops
            nodes = [(cx - 40, cy - 22), (cx, cy + 14), (cx + 40, cy - 8)]
            arcade.draw_line(nodes[0][0], nodes[0][1], nodes[1][0], nodes[1][1], color, 2)
            arcade.draw_line(nodes[1][0], nodes[1][1], nodes[2][0], nodes[2][1], color, 2)
            for node in nodes:
                arcade.draw_circle_filled(node[0], node[1], 9, (6, 9, 16, 255))
                arcade.draw_circle_outline(node[0], node[1], 9, color, 3)
        else:
            # a block grid with one block missing
            for gx in range(2):
                for gy in range(2):
                    if gx == 1 and gy == 1:
                        continue
                    left = cx - 34 + gx * 36
                    bottom = cy - 34 + gy * 36
                    arcade.draw_lrbt_rectangle_outline(left, left + 32, bottom, bottom + 32, color, 3)
            arcade.draw_line(cx + 14, cy + 20, cx + 34, cy + 20, color, 3)
            arcade.draw_line(cx + 24, cy + 10, cx + 24, cy + 30, color, 3)

    def draw_card(self, index):
        cx = self.card_xs[index]
        cy = self.CARD_Y
        left = cx - self.CARD_WIDTH / 2
        right = cx + self.CARD_WIDTH / 2
        bottom = cy - self.CARD_HEIGHT / 2
        top = cy + self.CARD_HEIGHT / 2
        mode = MODES[index]
        ready = mode["ready"]
        selected = (index == self.selected)

        arcade.draw_lrbt_rectangle_filled(left, right, bottom, top, (6, 9, 16, 240))
        if selected:
            glow_on()
            arcade.draw_lrbt_rectangle_filled(left, right, bottom, top,
                                              with_alpha(PLAYER_COLOR, 16))
            arcade.draw_lrbt_rectangle_outline(left, right, bottom, top,
                                               with_alpha(PLAYER_COLOR, 45), 14)
            arcade.draw_lrbt_rectangle_outline(left, right, bottom, top,
                                               with_alpha(PLAYER_COLOR, 90), 6)
            glow_off()
            arcade.draw_lrbt_rectangle_outline(left, right, bottom, top, CONDUIT_COLOR, 2)
        else:
            arcade.draw_lrbt_rectangle_outline(left, right, bottom, top, (50, 90, 120, 255), 2)

        tick = (90, 190, 240, 255)
        arcade.draw_line(left + 10, top - 10, left + 30, top - 10, tick, 2)
        arcade.draw_line(left + 10, top - 10, left + 10, top - 30, tick, 2)
        arcade.draw_line(right - 10, bottom + 10, right - 30, bottom + 10, tick, 2)
        arcade.draw_line(right - 10, bottom + 10, right - 10, bottom + 30, tick, 2)

        if ready:
            icon_color = mix(PLAYER_COLOR, WHITE_HOT, 0.25)
            self.name_texts[index].color = WHITE_HOT
            self.status_texts[index].color = ENEMY_COLOR
        else:
            icon_color = (70, 100, 125)
            self.name_texts[index].color = (130, 160, 180)
            self.status_texts[index].color = (110, 140, 160)
        self.draw_icon(mode["id"], cx, cy + 62, icon_color)
        self.name_texts[index].draw()
        self.blurb_texts[index].draw()
        self.status_texts[index].draw()

    def on_draw(self):
        self.clear()
        self.screen.use()
        self.draw_backdrop(self.backdrop)

        self.title.draw()
        for i in range(len(MODES)):
            self.draw_card(i)
        self.back_button.draw(self.back_selected, self.clock)
        self.hint.draw()
        self.draw_fps()


class EndlessSetupView(BaseView):
    # Pick the arena, how many enemies, and how many lives, then start a run.
    PANEL_HALF = 330
    VALUE_X = CENTER_X + 140

    def __init__(self, previous_view):
        super().__init__()
        self.previous_view = previous_view
        self.backdrop = ArenaBackdrop()

        save = self.window.save
        self.level_index = save.get("endless_level")
        self.enemies = save.get("endless_enemies")
        self.lives = save.get("endless_lives")

        self.rows = [
            {"kind": "choice", "key": "arena", "label": "ARENA"},
            {"kind": "choice", "key": "enemies", "label": "ENEMIES"},
            {"kind": "choice", "key": "lives", "label": "LIVES"},
            {"kind": "button", "key": "start", "label": "START RUN"},
            {"kind": "button", "key": "back", "label": "BACK"},
        ]
        self.selected = 3   # START RUN, so ENTER goes straight into a run

        self.title = make_text("ENDLESS MODE", CENTER_X, 582, WHITE_HOT, 30, bold=True)
        self.subtitle = make_text("SURVIVE AS LONG AS YOU CAN", CENTER_X, 548, TEXT_DIM, 12)
        self.hint = make_text("UP / DOWN SELECT     LEFT / RIGHT CHANGE     ENTER START     ESC BACK",
                              CENTER_X, 22, (90, 170, 200), 11)
        self.best_label = make_text("BEST FOR THIS SETUP", CENTER_X, 210, TEXT_DIM, 12)
        self.best_value = make_text("---", CENTER_X, 182, WHITE_HOT, 20, bold=True)

        self.label_texts = []
        self.value_texts = []
        for i in range(len(self.rows)):
            y = self.row_y(i)
            if self.rows[i]["kind"] == "button":
                self.label_texts.append(make_text(self.rows[i]["label"], CENTER_X, y,
                                                  TEXT_DIM, 16, bold=True))
                self.value_texts.append(None)
            else:
                self.label_texts.append(make_text(self.rows[i]["label"],
                                                  CENTER_X - self.PANEL_HALF + 24, y,
                                                  TEXT_DIM, 16, anchor_x="left", bold=True))
                self.value_texts.append(make_text("", self.VALUE_X, y, WHITE_HOT, 14, bold=True))

    def row_y(self, index):
        return 480 - index * 56

    def go_back(self):
        self.window.show_view(self.previous_view)

    def value_text(self, key):
        if key == "arena":
            return level_label(self.level_index) + "  " + LEVELS[self.level_index]["name"]
        if key == "enemies":
            return str(self.enemies)
        return str(self.lives)

    def adjust(self, key, step):
        save = self.window.save
        if key == "arena":
            self.level_index = (self.level_index + step) % len(LEVELS)
            save.set("endless_level", self.level_index)
        elif key == "enemies":
            self.enemies = max(1, min(ENDLESS_MAX_ENEMIES, self.enemies + step))
            save.set("endless_enemies", self.enemies)
        elif key == "lives":
            self.lives = max(1, min(ENDLESS_MAX_LIVES, self.lives + step))
            save.set("endless_lives", self.lives)

    def start_run(self):
        setup = {"enemies": self.enemies, "lives": self.lives}
        self.window.show_view(GameView(self.level_index, setup))

    def update_view(self, delta_time):
        self.backdrop.update(delta_time)

    def key_pressed(self, key, modifiers):
        row = self.rows[self.selected]
        if key == arcade.key.ESCAPE:
            self.go_back()
        elif key == arcade.key.UP or key == arcade.key.W:
            self.selected = (self.selected - 1) % len(self.rows)
        elif key == arcade.key.DOWN or key == arcade.key.S:
            self.selected = (self.selected + 1) % len(self.rows)
        elif key == arcade.key.LEFT or key == arcade.key.A:
            if row["kind"] == "choice":
                self.adjust(row["key"], -1)
        elif key == arcade.key.RIGHT or key == arcade.key.D:
            if row["kind"] == "choice":
                self.adjust(row["key"], 1)
        elif key == arcade.key.ENTER or key == arcade.key.NUM_ENTER or key == arcade.key.SPACE:
            if row["key"] == "back":
                self.go_back()
            else:
                self.start_run()

    def row_at(self, lx, ly):
        if abs(lx - CENTER_X) > self.PANEL_HALF:
            return -1
        for i in range(len(self.rows)):
            if abs(ly - self.row_y(i)) <= 24:
                return i
        return -1

    def mouse_moved(self, lx, ly):
        index = self.row_at(lx, ly)
        if index >= 0:
            self.selected = index

    def mouse_pressed(self, lx, ly, button):
        if button != arcade.MOUSE_BUTTON_LEFT:
            return
        index = self.row_at(lx, ly)
        if index < 0:
            return
        self.selected = index
        row = self.rows[index]
        if row["kind"] == "choice":
            # left of the value is "less", right of it is "more"
            if lx > CENTER_X:
                if lx < self.VALUE_X:
                    self.adjust(row["key"], -1)
                else:
                    self.adjust(row["key"], 1)
        elif row["key"] == "start":
            self.start_run()
        elif row["key"] == "back":
            self.go_back()

    def draw_row(self, index):
        row = self.rows[index]
        y = self.row_y(index)
        selected = (index == self.selected)
        left = CENTER_X - self.PANEL_HALF
        right = CENTER_X + self.PANEL_HALF

        if selected:
            glow_on()
            arcade.draw_lrbt_rectangle_filled(left, right, y - 22, y + 22,
                                              with_alpha(PLAYER_COLOR, 16))
            arcade.draw_lrbt_rectangle_outline(left, right, y - 22, y + 22,
                                               with_alpha(PLAYER_COLOR, 60), 8)
            glow_off()
            arcade.draw_lrbt_rectangle_outline(left, right, y - 22, y + 22, CONDUIT_COLOR, 2)
            self.label_texts[index].color = WHITE_HOT
        else:
            arcade.draw_lrbt_rectangle_outline(left, right, y - 22, y + 22, (40, 70, 95, 255), 1)
            self.label_texts[index].color = TEXT_DIM
        self.label_texts[index].draw()

        if row["kind"] == "choice":
            arrow_color = TEXT_DIM
            if selected:
                arrow_color = PLAYER_COLOR
            vx = self.VALUE_X
            arcade.draw_triangle_filled(vx - 128, y, vx - 116, y + 8, vx - 116, y - 8, arrow_color)
            arcade.draw_triangle_filled(vx + 128, y, vx + 116, y + 8, vx + 116, y - 8, arrow_color)
            self.value_texts[index].text = self.value_text(row["key"])
            self.value_texts[index].draw()

    def on_draw(self):
        self.clear()
        self.screen.use()
        self.draw_backdrop(self.backdrop)

        self.title.draw()
        self.subtitle.draw()
        for i in range(len(self.rows)):
            self.draw_row(i)

        key = endless_key(self.level_index, self.enemies, self.lives)
        record = self.window.save.endless_record(key)
        if record["time"] > 0 or record["kills"] > 0:
            self.best_value.text = (format_time(record["time"]) + " SURVIVED     " +
                                    str(record["kills"]) + " KILLS")
        else:
            self.best_value.text = "---"
        self.best_label.draw()
        self.best_value.draw()

        draw_level_icon(CENTER_X, 112, LEVELS[self.level_index], True, 260, 80, 0.2)

        self.hint.draw()
        self.draw_fps()


class PlaceholderView(BaseView):
    # Stand-in screen for modes that are not built yet.
    def __init__(self, previous_view, name, blurb):
        super().__init__()
        self.previous_view = previous_view
        self.backdrop = ArenaBackdrop()
        self.title = make_text(name, CENTER_X, 420, WHITE_HOT, 40, bold=True)
        self.soon = make_text("COMING SOON", CENTER_X, 350, PLAYER_COLOR, 22, bold=True)
        self.blurb = make_text(blurb, CENTER_X, 310, TEXT_DIM, 13)
        self.hint = make_text("ESC OR ENTER TO GO BACK", CENTER_X, 22, (90, 170, 200), 11)
        self.back_button = Button("< BACK", 125, 30, 150, 40, self.go_back)
        self.back_selected = False

    def go_back(self):
        self.window.show_view(self.previous_view)

    def update_view(self, delta_time):
        self.backdrop.update(delta_time)

    def key_pressed(self, key, modifiers):
        if key == arcade.key.ESCAPE or key == arcade.key.ENTER or key == arcade.key.NUM_ENTER:
            self.go_back()

    def mouse_moved(self, lx, ly):
        self.back_selected = self.back_button.contains(lx, ly)

    def mouse_pressed(self, lx, ly, button):
        if button == arcade.MOUSE_BUTTON_LEFT and self.back_button.contains(lx, ly):
            self.go_back()

    def on_draw(self):
        self.clear()
        self.screen.use()
        self.draw_backdrop(self.backdrop)
        self.title.draw()
        self.soon.draw()
        self.blurb.draw()
        self.back_button.draw(self.back_selected, self.clock)
        self.hint.draw()
        self.draw_fps()


class OptionsView(BaseView):
    TRACK_LEFT = CENTER_X + 10
    TRACK_RIGHT = CENTER_X + 230
    PANEL_HALF = 330

    def __init__(self, previous_view):
        super().__init__()
        self.previous_view = previous_view
        self.backdrop = ArenaBackdrop()

        self.rows = [
            {"kind": "slider", "key": "master_volume", "label": "MASTER VOLUME"},
            {"kind": "slider", "key": "music_volume", "label": "MUSIC VOLUME"},
            {"kind": "slider", "key": "sfx_volume", "label": "EFFECTS VOLUME"},
            {"kind": "toggle", "key": "fullscreen", "label": "FULLSCREEN"},
            {"kind": "toggle", "key": "show_fps", "label": "SHOW FPS"},
            {"kind": "button", "key": "reset", "label": "RESET TO DEFAULTS"},
            {"kind": "button", "key": "back", "label": "BACK"},
        ]
        self.selected = 0
        self.dragging = -1

        self.title = make_text("OPTIONS", CENTER_X, 582, WHITE_HOT, 30, bold=True)
        self.hint = make_text("UP / DOWN SELECT     LEFT / RIGHT ADJUST     ESC BACK",
                              CENTER_X, 22, (90, 170, 200), 11)
        self.label_texts = []
        self.value_texts = []
        for i in range(len(self.rows)):
            y = self.row_y(i)
            if self.rows[i]["kind"] == "button":
                self.label_texts.append(make_text(self.rows[i]["label"], CENTER_X, y,
                                                  TEXT_DIM, 16, bold=True))
            else:
                self.label_texts.append(make_text(self.rows[i]["label"],
                                                  CENTER_X - self.PANEL_HALF + 24, y,
                                                  TEXT_DIM, 16, anchor_x="left", bold=True))
            self.value_texts.append(make_text("", CENTER_X + self.PANEL_HALF - 24, y,
                                              WHITE_HOT, 14, anchor_x="right"))

    def row_y(self, index):
        return 510 - index * 52

    def go_back(self):
        self.window.show_view(self.previous_view)

    def get_value(self, row):
        if row["key"] == "fullscreen":
            return self.window.fullscreen
        return self.window.save.get(row["key"])

    def activate_row(self, index):
        row = self.rows[index]
        if row["kind"] == "toggle":
            if row["key"] == "fullscreen":
                toggle_fullscreen(self.window)
            else:
                self.window.save.set(row["key"], not self.window.save.get(row["key"]))
        elif row["key"] == "reset":
            self.window.save.reset_settings()
            self.window.set_fullscreen(False)
        elif row["key"] == "back":
            self.go_back()

    def adjust_slider(self, index, amount):
        row = self.rows[index]
        value = max(0, min(100, self.window.save.get(row["key"]) + amount))
        self.window.save.set(row["key"], value)

    def update_view(self, delta_time):
        self.backdrop.update(delta_time)

    def key_pressed(self, key, modifiers):
        row = self.rows[self.selected]
        if key == arcade.key.ESCAPE:
            self.go_back()
        elif key == arcade.key.UP or key == arcade.key.W:
            self.selected = (self.selected - 1) % len(self.rows)
        elif key == arcade.key.DOWN or key == arcade.key.S:
            self.selected = (self.selected + 1) % len(self.rows)
        elif key == arcade.key.LEFT or key == arcade.key.A:
            if row["kind"] == "slider":
                self.adjust_slider(self.selected, -5)
            elif row["kind"] == "toggle":
                self.activate_row(self.selected)
        elif key == arcade.key.RIGHT or key == arcade.key.D:
            if row["kind"] == "slider":
                self.adjust_slider(self.selected, 5)
            elif row["kind"] == "toggle":
                self.activate_row(self.selected)
        elif key == arcade.key.ENTER or key == arcade.key.NUM_ENTER or key == arcade.key.SPACE:
            if row["kind"] != "slider":
                self.activate_row(self.selected)

    def row_at(self, lx, ly):
        if abs(lx - CENTER_X) > self.PANEL_HALF:
            return -1
        for i in range(len(self.rows)):
            if abs(ly - self.row_y(i)) <= 24:
                return i
        return -1

    def set_slider_from_x(self, index, lx):
        t = (lx - self.TRACK_LEFT) / (self.TRACK_RIGHT - self.TRACK_LEFT)
        value = int(round(max(0.0, min(1.0, t)) * 100))
        self.window.save.data[self.rows[index]["key"]] = value

    def mouse_moved(self, lx, ly):
        index = self.row_at(lx, ly)
        if index >= 0 and self.dragging < 0:
            self.selected = index

    def mouse_pressed(self, lx, ly, button):
        if button != arcade.MOUSE_BUTTON_LEFT:
            return
        index = self.row_at(lx, ly)
        if index < 0:
            return
        self.selected = index
        row = self.rows[index]
        if row["kind"] == "slider":
            if self.TRACK_LEFT - 14 <= lx <= self.TRACK_RIGHT + 14:
                self.dragging = index
                self.set_slider_from_x(index, lx)
        else:
            self.activate_row(index)

    def mouse_dragged(self, lx, ly):
        if self.dragging >= 0:
            self.set_slider_from_x(self.dragging, lx)

    def mouse_released(self):
        if self.dragging >= 0:
            self.window.save.save()
        self.dragging = -1

    def draw_row(self, index):
        row = self.rows[index]
        y = self.row_y(index)
        selected = (index == self.selected)
        left = CENTER_X - self.PANEL_HALF
        right = CENTER_X + self.PANEL_HALF

        if selected:
            glow_on()
            arcade.draw_lrbt_rectangle_filled(left, right, y - 22, y + 22,
                                              with_alpha(PLAYER_COLOR, 16))
            arcade.draw_lrbt_rectangle_outline(left, right, y - 22, y + 22,
                                               with_alpha(PLAYER_COLOR, 60), 8)
            glow_off()
            arcade.draw_lrbt_rectangle_outline(left, right, y - 22, y + 22, CONDUIT_COLOR, 2)
            self.label_texts[index].color = WHITE_HOT
        else:
            arcade.draw_lrbt_rectangle_outline(left, right, y - 22, y + 22, (40, 70, 95, 255), 1)
            self.label_texts[index].color = TEXT_DIM
        self.label_texts[index].draw()

        if row["kind"] == "slider":
            value = self.get_value(row)
            fill_x = self.TRACK_LEFT + (self.TRACK_RIGHT - self.TRACK_LEFT) * value / 100
            arcade.draw_line(self.TRACK_LEFT, y, self.TRACK_RIGHT, y, (50, 90, 120, 255), 4)
            glow_on()
            arcade.draw_line(self.TRACK_LEFT, y, fill_x, y, with_alpha(PLAYER_COLOR, 70), 12)
            glow_off()
            arcade.draw_line(self.TRACK_LEFT, y, fill_x, y, PLAYER_COLOR, 4)
            arcade.draw_circle_filled(fill_x, y, 8, (6, 9, 16, 255))
            arcade.draw_circle_outline(fill_x, y, 8, WHITE_HOT, 2)
            self.value_texts[index].text = str(value)
            self.value_texts[index].draw()
        elif row["kind"] == "toggle":
            on = self.get_value(row)
            pill_left = right - 24 - 80
            pill_right = right - 24
            arcade.draw_lrbt_rectangle_filled(pill_left, pill_right, y - 13, y + 13, (6, 9, 16, 255))
            if on:
                glow_on()
                arcade.draw_lrbt_rectangle_filled(pill_left, pill_right, y - 13, y + 13,
                                                  with_alpha(PLAYER_COLOR, 60))
                glow_off()
                arcade.draw_lrbt_rectangle_outline(pill_left, pill_right, y - 13, y + 13,
                                                   PLAYER_COLOR, 2)
                self.value_texts[index].text = "ON"
                self.value_texts[index].color = WHITE_HOT
            else:
                arcade.draw_lrbt_rectangle_outline(pill_left, pill_right, y - 13, y + 13,
                                                   (60, 90, 115, 255), 2)
                self.value_texts[index].text = "OFF"
                self.value_texts[index].color = (110, 140, 160)
            self.value_texts[index].x = (pill_left + pill_right) / 2
            self.value_texts[index].anchor_x = "center"
            self.value_texts[index].draw()

    def on_draw(self):
        self.clear()
        self.screen.use()
        self.draw_backdrop(self.backdrop)

        self.title.draw()
        for i in range(len(self.rows)):
            self.draw_row(i)
        self.hint.draw()
        self.draw_fps()


class GameView(BaseView):
    # endless is None for a normal Gladiator level, or a dict like
    # {"enemies": 3, "lives": 5} for an endless run on that arena.
    # campaign is None, or an index into CAMPAIGN_LEVELS.
    #
    # phase only matters in the campaign:
    #   corridor    walk to the exit gate at the end of the hallway
    #   fading_out  screen goes black
    #   fading_in   the circular arena fades in
    #   speech      the announcer talks, nobody can move
    #   reveal      obstacles trace their outlines, then flash solid
    #   fight       normal play
    def __init__(self, level_index, endless=None, campaign=None):
        super().__init__()
        self.level_index = level_index
        self.endless = endless
        self.campaign = campaign
        self.is_endless = endless is not None
        self.is_campaign = campaign is not None

        if self.is_campaign:
            self.level = dict(CAMPAIGN_LEVELS[campaign])
            corridor = self.level["corridor"]
            self.arena = Arena("rect", [], corridor["bounds"])
            start = corridor["player_start"]
            self.phase = "corridor"
        else:
            self.level = dict(LEVELS[level_index])
            self.arena = make_arena(self.level)
            start = self.level["player_start"]
            self.phase = "fight"
        self.backdrop = ArenaBackdrop(self.arena)

        self.lives_total = LIVES
        self.endless_key = ""
        self.best_time = 0.0
        self.best_kills = 0
        self.new_best_time = False
        self.new_best_kills = False
        self.run_time = 0.0

        save = self.window.save
        if self.is_endless:
            self.lives_total = endless["lives"]
            self.endless_key = endless_key(level_index, endless["enemies"], endless["lives"])
            record = save.endless_record(self.endless_key)
            self.best_time = record["time"]
            self.best_kills = record["kills"]
            self.level["enemies"] = endless["enemies"]
            self.level["enemy_starts"] = self.build_endless_spawns(endless["enemies"])
            self.level["kills"] = 0
            self.level["speed"] = max(self.level["speed"], 100)
        elif not self.is_campaign:
            save.data["has_played"] = True
            save.data["current_level"] = level_index
            save.save()
        self.base_level = dict(self.level)

        self.keys_down = set()
        self.mouse_x = WIDTH / 2   # mouse position on the screen layout (not the world)
        self.mouse_y = HEIGHT / 2

        self.player = Fighter(start[0], start[1], PLAYER_COLOR, "player")
        self.enemies = []
        self.brains = []
        self.fighters = [self.player]
        if not self.is_campaign:
            self.spawn_enemies()

        self.camera = FollowCamera()
        self.camera_ready = False

        self.kills = 0
        self.deaths = 0
        self.mode = "playing"   # playing, paused, won, lost
        self.finished = False   # a result is pending, game is frozen
        self.result_timer = 0.0
        self.result = ""
        self.overlay = None
        self.overlay_title = None
        self.overlay_sub = None
        self.overlay_note = None

        # campaign cutscene state
        self.fade = 0.0           # 0 is clear, 1 is fully black
        self.speech_index = 0
        self.speech_time = 0.0
        self.reveal_time = 0.0

        font_hint = (90, 170, 200)
        if self.is_endless:
            title = "ENDLESS   " + level_label(level_index) + " " + self.level["name"]
        elif self.is_campaign:
            title = "CAMPAIGN   " + level_label(campaign) + " " + self.level["name"]
        else:
            title = "LEVEL " + level_label(level_index) + "   " + self.level["name"]
        self.level_text = make_text(title, CENTER_X, HEIGHT - 40, CONDUIT_COLOR, 15, bold=True)
        self.kills_label = make_text("KILLS", 40, HEIGHT - 24, font_hint, 11, anchor_x="left")
        self.lives_label = make_text("LIVES", WIDTH - 40, HEIGHT - 24, font_hint, 11, anchor_x="right")
        self.kills_value = make_text("0", 40, HEIGHT - 50, WHITE_HOT, 20, anchor_x="left", bold=True)
        self.best_kills_text = make_text("", 40, HEIGHT - 76, TEXT_DIM, 11, anchor_x="left")
        self.time_value = make_text("0:00", CENTER_X, HEIGHT - 68, WHITE_HOT, 20, bold=True)
        self.best_time_text = make_text("", CENTER_X, HEIGHT - 92, TEXT_DIM, 11)
        self.hint = make_text("WASD MOVE      CLICK THROW      SPACE RECALL      ESC PAUSE",
                              CENTER_X, 22, font_hint, 11)
        self.announce_label = make_text("ANNOUNCER", 140, HEIGHT - 74, PLAYER_COLOR, 10,
                                        anchor_x="left", bold=True)
        self.announce_text = make_text("", 140, HEIGHT - 106, WHITE_HOT, 15, anchor_x="left")

    def view_shown(self):
        self.keys_down = set()
        if not self.camera_ready:
            self.camera.snap(self.player.x, self.player.y, self.arena, self.screen)
            self.camera_ready = True

    # ------------------------------------------------------------ setup helpers

    def spawn_enemies(self):
        self.enemies = []
        self.brains = []
        for i in range(self.level["enemies"]):
            spot = self.level["enemy_starts"][i]
            enemy = Fighter(spot[0], spot[1], ENEMY_COLORS[i % len(ENEMY_COLORS)], "enemy")
            enemy.facing = math.pi
            self.enemies.append(enemy)
            self.brains.append(EnemyBrain(enemy, self.level, self.arena, min(i * 0.8, 3.0)))
        self.fighters = [self.player] + self.enemies

    def controls_locked(self):
        return self.is_campaign and self.phase in CUTSCENE_PHASES

    # ------------------------------------------------------------ endless helpers

    def build_endless_spawns(self, count):
        # Uses the level's own enemy spots first, then finds more random ones.
        base = list(self.level["enemy_starts"])
        spawns = base[:count]
        player = self.level["player_start"]
        attempts = 0
        while len(spawns) < count and attempts < 200:
            attempts += 1
            point = self.arena.random_point(PLAYER_RADIUS + 20, player[0], player[1], 300)
            if point is None:
                continue
            too_close = False
            for spot in spawns:
                if math.hypot(point[0] - spot[0], point[1] - spot[1]) < 90:
                    too_close = True
            if not too_close:
                spawns.append(point)
        while len(spawns) < count:
            spawns.append(base[len(spawns) % len(base)])
        return spawns

    def apply_ramp(self):
        # Enemies get faster, throw sooner, and aim better as the kills pile up.
        ramp = min(1.0, self.kills / ENDLESS_RAMP_KILLS)
        self.level["speed"] = self.base_level["speed"] * (1.0 + 0.4 * ramp)
        self.level["interval"] = self.base_level["interval"] * (1.0 - 0.4 * ramp)
        self.level["error"] = self.base_level["error"] * (1.0 - 0.5 * ramp)

    def record_endless_run(self):
        # Saves the time and kills if either beats the old record.
        # Returns (new_best_time, new_best_kills).
        if not self.is_endless:
            return (False, False)
        save = self.window.save
        old = save.endless_record(self.endless_key)
        new_time = self.run_time > old["time"]
        new_kills = self.kills > old["kills"]
        if new_time or new_kills:
            save.data["endless_records"][self.endless_key] = {
                "time": round(max(old["time"], self.run_time), 2),
                "kills": max(old["kills"], self.kills),
            }
            save.save()
        return (new_time, new_kills)

    # ------------------------------------------------------------ campaign cutscene

    def check_corridor_exit(self):
        gate_x = self.arena.bounds[2] - CORRIDOR_EXIT_MARGIN
        if self.player.alive and self.player.x >= gate_x:
            self.phase = "fading_out"

    def enter_arena(self):
        # Swap the corridor for the circular arena. The screen is black right now.
        self.arena = Arena(self.level["arena"], [], level_bounds(self.level),
                           level_radius(self.level))
        self.backdrop = ArenaBackdrop(self.arena)
        start = self.level["player_start"]
        self.player.start_x = start[0]
        self.player.start_y = start[1]
        self.player.respawn()
        self.player.facing = 0.0
        self.spawn_enemies()
        self.camera.snap(self.player.x, self.player.y, self.arena, self.screen)
        self.phase = "fading_in"

    def start_speech(self):
        self.phase = "speech"
        self.speech_index = 0
        self.speech_time = -SPEECH_LEAD
        self.announce_text.text = ""

    def update_speech(self, delta_time):
        lines = self.level["speech"]
        line = lines[self.speech_index]
        self.speech_time += delta_time

        chars = int(self.speech_time * SPEECH_CHARS_PER_SECOND)
        chars = max(0, min(len(line), chars))
        self.announce_text.text = line[:chars]

        line_time = len(line) / SPEECH_CHARS_PER_SECOND
        if self.speech_time >= line_time + SPEECH_HOLD:
            self.speech_index += 1
            self.speech_time = 0.0
            if self.speech_index >= len(lines):
                self.announce_text.text = ""
                self.start_reveal()

    def start_reveal(self):
        self.phase = "reveal"
        self.reveal_time = 0.0
        for spec in self.level["reveal"]:
            self.backdrop.effects.append(ObstacleTrace(spec, REVEAL_TIME))

    def finish_reveal(self):
        # The outlines become real obstacles with a bright flash.
        self.arena.add_obstacles(self.level["reveal"])
        for obstacle in self.arena.obstacles:
            obstacle.flash = 1.0
            obstacle.flash_color = WHITE_HOT
            self.backdrop.effects.append(Pulse(obstacle.x, obstacle.y, WHITE_HOT, 70, 0.5))
        self.phase = "fight"

    def update_cutscene(self, delta_time):
        # Everyone stands still. Only the camera, effects and fade move.
        effects = self.backdrop.effects
        self.player.facing = self.player_aim_angle()
        self.player.update_trail(delta_time, False)
        for fighter in self.fighters:
            fighter.disc.update(delta_time, effects, fighter.facing, self.arena)

        if self.phase == "fading_out":
            self.fade = min(1.0, self.fade + delta_time / FADE_OUT_TIME)
            if self.fade >= 1.0:
                self.enter_arena()
        elif self.phase == "fading_in":
            self.fade = max(0.0, self.fade - delta_time / FADE_IN_TIME)
            if self.fade <= 0.0:
                self.start_speech()
        elif self.phase == "speech":
            self.update_speech(delta_time)
        elif self.phase == "reveal":
            self.reveal_time += delta_time
            if self.reveal_time >= REVEAL_TIME:
                self.finish_reveal()

    # ------------------------------------------------------------ overlays

    def open_overlay(self, mode):
        self.mode = mode
        note = ""
        if mode == "paused":
            entries = [("RESUME", self.resume), ("RESTART", self.restart),
                       ("OPTIONS", self.open_options), ("MAIN MENU", self.main_menu)]
            title = "PAUSED"
            title_color = WHITE_HOT
            sub = ""
        elif mode == "won":
            entries = []
            title = "LEVEL COMPLETE"
            if self.is_campaign:
                title = "MISSION COMPLETE"
            elif self.level_index < len(LEVELS) - 1:
                entries.append(("NEXT LEVEL", self.next_level))
            entries.append(("REPLAY", self.restart))
            entries.append(("MAIN MENU", self.main_menu))
            title_color = PLAYER_COLOR
            sub = "DEREZZED " + str(self.kills) + "     LIVES LOST " + str(self.deaths)
            if not self.is_campaign and self.level_index == len(LEVELS) - 1:
                sub = "ALL LEVELS CLEARED     " + sub
        elif self.is_endless:
            entries = [("RETRY", self.restart), ("CHANGE SETUP", self.endless_setup),
                       ("MAIN MENU", self.main_menu)]
            title = "RUN OVER"
            title_color = ENEMY_COLOR
            sub = "SURVIVED " + format_time(self.run_time) + "     KILLS " + str(self.kills)
            if self.new_best_time and self.new_best_kills:
                sub = "NEW BEST TIME AND KILLS     " + sub
            elif self.new_best_time:
                sub = "NEW BEST TIME     " + sub
            elif self.new_best_kills:
                sub = "NEW MOST KILLS     " + sub
            best = self.window.save.endless_record(self.endless_key)
            note = ("BEST TIME " + format_time(best["time"]) +
                    "     MOST KILLS " + str(best["kills"]))
        else:
            entries = [("RETRY", self.restart), ("MAIN MENU", self.main_menu)]
            title = "DEREZZED"
            title_color = ENEMY_COLOR
            sub = "OUT OF LIVES"
        self.overlay = MenuList(entries, CENTER_X, 330)
        self.overlay_title = make_text(title, CENTER_X, 470, title_color, 44, bold=True)
        self.overlay_sub = make_text(sub, CENTER_X, 425, TEXT_DIM, 14)
        self.overlay_note = make_text(note, CENTER_X, 396, TEXT_DIM, 12)

    def resume(self):
        self.mode = "playing"
        self.keys_down = set()

    def restart(self):
        self.record_endless_run()
        self.window.show_view(GameView(self.level_index, self.endless, self.campaign))

    def next_level(self):
        self.window.show_view(GameView(self.level_index + 1))

    def open_options(self):
        self.window.show_view(OptionsView(self))

    def endless_setup(self):
        self.record_endless_run()
        self.window.show_view(EndlessSetupView(ModeSelectView(MenuView())))

    def main_menu(self):
        self.record_endless_run()
        self.window.show_view(MenuView())

    def finish(self, result):
        self.finished = True
        self.result = result
        self.result_timer = 1.1
        if self.is_endless:
            self.new_best_time, self.new_best_kills = self.record_endless_run()
            return
        if self.is_campaign:
            return
        if result == "won":
            save = self.window.save
            save.data["unlocked"] = max(save.get("unlocked"),
                                        min(self.level_index + 2, len(LEVELS)))
            save.data["current_level"] = min(self.level_index + 1, len(LEVELS) - 1)
            save.save()

    # ------------------------------------------------------------ input

    def key_pressed(self, key, modifiers):
        if self.mode == "playing":
            self.keys_down.add(key)
            if key == arcade.key.ESCAPE and not self.finished:
                self.keys_down = set()
                self.open_overlay("paused")
            elif key == arcade.key.SPACE and not self.controls_locked():
                self.player.disc.recall()
        else:
            if key == arcade.key.ESCAPE and self.mode == "paused":
                self.resume()
            else:
                self.overlay.key_pressed(key)

    def on_key_release(self, key, modifiers):
        if key in self.keys_down:
            self.keys_down.remove(key)

    def mouse_moved(self, lx, ly):
        self.mouse_x = lx
        self.mouse_y = ly
        if self.mode != "playing":
            self.overlay.mouse_moved(lx, ly)

    def mouse_pressed(self, lx, ly, button):
        if button != arcade.MOUSE_BUTTON_LEFT:
            return
        if self.mode != "playing":
            self.overlay.mouse_pressed(lx, ly)
        elif not self.finished and not self.controls_locked():
            if self.player.alive and self.player.disc.state == HELD:
                self.player.disc.throw(self.player_aim_angle())

    def mouse_dragged(self, lx, ly):
        self.mouse_x = lx
        self.mouse_y = ly

    def mouse_world(self):
        # The mouse in world coordinates. The camera moves, so this is worked
        # out fresh every time from the screen position.
        return (self.mouse_x - CENTER_X + self.camera.x,
                self.mouse_y - CENTER_Y + self.camera.y)

    def player_aim_angle(self):
        world_x, world_y = self.mouse_world()
        return math.atan2(world_y - self.player.y, world_x - self.player.x)

    # ------------------------------------------------------------ update

    def update_view(self, delta_time):
        if self.mode == "paused":
            return

        # Cap big frame gaps so fast discs can't skip through thin walls.
        delta_time = min(delta_time, 1 / 30)

        self.backdrop.update(delta_time)
        self.update_camera(delta_time)

        if self.finished:
            self.result_timer -= delta_time
            if self.result_timer <= 0 and self.mode == "playing":
                self.open_overlay(self.result)
            return

        if self.mode != "playing":
            return

        if self.controls_locked():
            self.update_cutscene(delta_time)
            return

        effects = self.backdrop.effects

        if self.is_endless:
            self.run_time += delta_time

        self.player.facing = self.player_aim_angle()
        self.update_player_movement(delta_time)
        for brain in self.brains:
            brain.update(delta_time, self.player)

        self.player.disc.update(delta_time, effects, self.player_aim_angle(), self.arena)
        for brain in self.brains:
            brain.fighter.disc.update(delta_time, effects, brain.aim, self.arena)

        self.check_disc_hits()
        self.update_respawns(delta_time)

        if self.phase == "corridor":
            self.check_corridor_exit()

    def update_camera(self, delta_time):
        if self.is_campaign and self.phase in ("speech", "reveal"):
            # Look at the middle of the arena while the show happens.
            self.camera.update(delta_time, self.arena.cx, self.arena.cy,
                               self.arena, self.screen)
            return
        # Follow the player, leaning a little toward the mouse.
        look_x = (self.mouse_x - CENTER_X) * LOOK_AHEAD
        look_y = (self.mouse_y - CENTER_Y) * LOOK_AHEAD
        self.camera.update(delta_time, self.player.x + look_x, self.player.y + look_y,
                           self.arena, self.screen)

    def update_player_movement(self, delta_time):
        moved = False
        if self.player.alive:
            dx = 0
            dy = 0
            if arcade.key.W in self.keys_down:
                dy += 1
            if arcade.key.S in self.keys_down:
                dy -= 1
            if arcade.key.A in self.keys_down:
                dx -= 1
            if arcade.key.D in self.keys_down:
                dx += 1
            if dx != 0 or dy != 0:
                length = math.hypot(dx, dy)
                self.player.x += dx / length * PLAYER_SPEED * delta_time
                self.player.y += dy / length * PLAYER_SPEED * delta_time
                self.player.x, self.player.y = self.arena.constrain(
                    self.player.x, self.player.y, PLAYER_RADIUS)
                moved = True
        self.player.update_trail(delta_time, moved)

    def check_disc_hits(self):
        for fighter in self.fighters:
            disc = fighter.disc
            if disc.state == HELD:
                continue
            for target in self.fighters:
                if not target.alive:
                    continue
                if target is fighter:
                    if not FRIENDLY_FIRE:
                        continue
                elif target.team == fighter.team:
                    continue
                dist = math.hypot(target.x - disc.x, target.y - disc.y)
                if dist < PLAYER_RADIUS + DISC_RADIUS:
                    target.kill(self.backdrop.effects)
                    if target is self.player:
                        self.deaths += 1
                    else:
                        self.kills += 1
                        if self.is_endless:
                            self.apply_ramp()
                    self.check_result()

    def check_result(self):
        if self.finished:
            return
        if self.is_endless:
            if self.deaths >= self.lives_total:
                self.finish("lost")
            return
        if self.kills >= self.level["kills"]:
            self.finish("won")
        elif self.deaths >= self.lives_total:
            self.finish("lost")

    def update_respawns(self, delta_time):
        for fighter in self.fighters:
            if not fighter.alive:
                fighter.respawn_timer -= delta_time
                if fighter.respawn_timer <= 0:
                    fighter.respawn()

    # ------------------------------------------------------------ draw

    def on_draw(self):
        self.clear()

        # The world, seen through the following camera.
        self.screen.use_world(self.camera.x, self.camera.y)
        view = self.screen.view_rect(self.camera.x, self.camera.y, 80)
        b = self.backdrop

        b.draw_floor()

        glow_on()
        b.draw_streaks(view)
        self.draw_light_pools()
        b.draw_effects()
        for fighter in self.fighters:
            fighter.draw_trail()
            fighter.disc.draw_trail()
        glow_off()

        b.draw_frame()
        b.draw_conduit()
        b.draw_obstacles(view)

        if self.is_campaign and self.phase == "corridor":
            self.draw_exit_gate()

        for fighter in self.fighters:
            fighter.draw()
        for fighter in self.fighters:
            fighter.disc.draw()

        self.draw_aim_line()

        # The HUD and overlays stay fixed on the screen.
        self.screen.use()
        self.draw_hud()
        self.draw_announcer()

        if self.fade > 0:
            arcade.draw_lrbt_rectangle_filled(-4000, WIDTH + 4000, -4000, HEIGHT + 4000,
                                              (0, 0, 0, int(255 * self.fade)))

        if self.mode != "playing":
            self.draw_overlay()
        self.draw_fps()

    def draw_light_pools(self):
        for fighter in self.fighters:
            if fighter.alive:
                draw_light_pool(fighter.x, fighter.y, 90, fighter.color, 1.0)
            disc = fighter.disc
            if disc.state != HELD:
                draw_light_pool(disc.x, disc.y, 130, fighter.color,
                                1.0 + disc.flash * 1.5)

    def draw_exit_gate(self):
        # A glowing line across the end of the corridor with chevrons pointing at it.
        bounds = self.arena.bounds
        gate_x = bounds[2] - CORRIDOR_EXIT_MARGIN
        mid_y = (bounds[1] + bounds[3]) / 2
        pulse = 0.6 + 0.4 * math.sin(self.clock * 4)

        glow_on()
        arcade.draw_line(gate_x, bounds[1], gate_x, bounds[3],
                         with_alpha(PLAYER_COLOR, 40 * pulse), 18)
        arcade.draw_line(gate_x, bounds[1], gate_x, bounds[3],
                         with_alpha(PLAYER_COLOR, 120 * pulse), 7)
        for i in range(3):
            chevron_x = gate_x - 44 - i * 30
            wave = 0.5 + 0.5 * math.sin(self.clock * 6 - i * 1.1)
            color = with_alpha(PLAYER_COLOR, 60 + 170 * wave)
            arcade.draw_line(chevron_x - 10, mid_y + 26, chevron_x + 8, mid_y, color, 4)
            arcade.draw_line(chevron_x - 10, mid_y - 26, chevron_x + 8, mid_y, color, 4)
        glow_off()
        arcade.draw_line(gate_x, bounds[1], gate_x, bounds[3], WHITE_HOT, 2)

    def draw_aim_line(self):
        if self.mode != "playing" or self.finished or self.controls_locked():
            return
        if not self.player.alive or self.player.disc.state != HELD:
            return
        angle = self.player_aim_angle()
        px = self.player.x
        py = self.player.y
        arcade.draw_line(px + math.cos(angle) * 50, py + math.sin(angle) * 50,
                         px + math.cos(angle) * 110, py + math.sin(angle) * 110,
                         with_alpha(PLAYER_COLOR, 80), 2)

    def draw_pips(self, x, y, total, filled, direction):
        for i in range(total):
            px = x + direction * i * 20
            arcade.draw_circle_outline(px, y, 6, PLAYER_COLOR, 2)
            if i < filled:
                glow_on()
                arcade.draw_circle_filled(px, y, 9, with_alpha(PLAYER_COLOR, 60))
                glow_off()
                arcade.draw_circle_filled(px, y, 3.5, WHITE_HOT)

    def draw_hud(self):
        self.level_text.draw()
        self.kills_label.draw()
        self.lives_label.draw()
        if self.is_endless:
            self.kills_value.text = str(self.kills)
            self.best_kills_text.text = "BEST " + str(max(self.best_kills, self.kills))
            self.time_value.text = format_time(self.run_time)
            self.best_time_text.text = "BEST " + format_time(max(self.best_time, self.run_time))
            self.kills_value.draw()
            self.best_kills_text.draw()
            self.time_value.draw()
            self.best_time_text.draw()
        else:
            self.draw_pips(46, HEIGHT - 46, self.level["kills"], self.kills, 1)
        self.draw_pips(WIDTH - 46, HEIGHT - 46, self.lives_total,
                       self.lives_total - self.deaths, -1)
        self.hint.draw()

    def draw_announcer(self):
        # The text box at the top of the screen during the campaign intro.
        if not self.is_campaign or self.phase != "speech":
            return
        left = 120
        right = WIDTH - 120
        bottom = HEIGHT - 132
        top = HEIGHT - 58

        arcade.draw_lrbt_rectangle_filled(left, right, bottom, top, (6, 9, 16, 240))
        glow_on()
        arcade.draw_lrbt_rectangle_filled(left, right, bottom, top, with_alpha(PLAYER_COLOR, 14))
        arcade.draw_lrbt_rectangle_outline(left, right, bottom, top,
                                           with_alpha(PLAYER_COLOR, 45), 12)
        arcade.draw_lrbt_rectangle_outline(left, right, bottom, top,
                                           with_alpha(PLAYER_COLOR, 90), 5)
        glow_off()
        arcade.draw_lrbt_rectangle_outline(left, right, bottom, top, CONDUIT_COLOR, 2)

        tick = (90, 190, 240, 255)
        arcade.draw_line(left + 8, top - 8, left + 24, top - 8, tick, 2)
        arcade.draw_line(left + 8, top - 8, left + 8, top - 24, tick, 2)
        arcade.draw_line(right - 8, bottom + 8, right - 24, bottom + 8, tick, 2)
        arcade.draw_line(right - 8, bottom + 8, right - 8, bottom + 24, tick, 2)

        self.announce_label.draw()
        self.announce_text.draw()

    def draw_overlay(self):
        arcade.draw_lrbt_rectangle_filled(-4000, WIDTH + 4000, -4000, HEIGHT + 4000,
                                          (0, 0, 0, 165))
        self.overlay_title.draw()
        self.overlay_sub.draw()
        self.overlay_note.draw()
        self.overlay.draw(self.clock)


# ------------------------------------------------------------------ main

def main():
    window = arcade.Window(WIDTH, HEIGHT, TITLE, resizable=True)
    window.set_minimum_size(640, 440)
    window.save = SaveData()
    if window.save.get("fullscreen"):
        window.set_fullscreen(True)
    window.show_view(MenuView())
    arcade.run()


if __name__ == "__main__":
    main()