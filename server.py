"""局域网 5 人抢食混战贪吃蛇 —— 服务器权威实现。

启动方式：
    python server.py
    uvicorn server:app --host 0.0.0.0 --port 3000

玩法：最多 5 人同屏，限时 2 分钟抢食物，时间到了比分数。
撞墙/撞自己/撞别人都会死，2 秒后在空闲出生点复活，分数保留，尸体原地掉落 3 个食物。
"""

from __future__ import annotations

import asyncio
import json
import os
import random
import socket
from pathlib import Path
from typing import Optional

import uvicorn
from fastapi import FastAPI, WebSocket
from fastapi.responses import FileResponse
from starlette.websockets import WebSocketDisconnect

BASE_DIR = Path(__file__).resolve().parent

# 云平台（Render 等）会通过 PORT 环境变量指定端口
PORT = int(os.environ.get("PORT", "3000"))
ON_CLOUD = "PORT" in os.environ

COLS = 32
ROWS = 32
START_LENGTH = 3
FOOD_SCORE = 10
MAX_PLAYERS = 5
RESPAWN_SECONDS = 2.0
CORPSE_FOOD = 3
BASE_FOODS = 5          # 场上常驻食物数
MAX_FOODS = 22          # 食物总数上限（含尸体掉落的），否则打久了整张图会铺满食物
ROOM_ID = "LAN-01"

# ---- 特殊食物 ----
EFFECT_SECONDS = 5.0
FOOD_KINDS = ("normal", "ghost", "slow", "shield")

# ---- 技能 ----
BLINK_CELLS = 5
SKILL_SHIELD_SECONDS = 3.0
SKILL_SLOW_SECONDS = 5.0
SKILL_COOLDOWN = 25.0
SKILLS = ("blink", "shield", "slow")
SKILL_INFO = {
    "blink": "闪现 · 向前瞬移 5 格",
    "shield": "无敌 · 3 秒内不会死",
    "slow": "减速 · 其他玩家 5 秒内移速减半",
}

# ---- 难度预设：房主在大厅切换，同时改变速度、特殊食物频率与单局时长 ----
DIFFICULTIES = {
    "easy":   {"label": "简单", "tick": 0.150, "special": 0.08, "round": 150.0},
    "normal": {"label": "普通", "tick": 0.120, "special": 0.15, "round": 120.0},
    "hard":   {"label": "困难", "tick": 0.095, "special": 0.25, "round": 90.0},
}
DEFAULT_DIFFICULTY = "normal"
TICK_SECONDS = DIFFICULTIES[DEFAULT_DIFFICULTY]["tick"]   # 兼容旧引用
ROUND_SECONDS = DIFFICULTIES[DEFAULT_DIFFICULTY]["round"]

SKIN_COUNT = 5
COLORS = ["#22e6ff", "#ff3df0", "#ffb020", "#7dffb0", "#a855f7"]

DIRS = {"up": (0, -1), "down": (0, 1), "left": (-1, 0), "right": (1, 0)}
OPPOSITE = {"up": "down", "down": "up", "left": "right", "right": "left"}

# 5 个出生点分散在棋盘上，任意两个都不同行、不同列，
# 所以不会出现「两个人生出来就正对着彼此、不动就必撞」的情况
SPAWNS = [
    ((6, 8), "right"),
    ((25, 24), "left"),
    ((16, 6), "down"),
    ((8, 25), "up"),
    ((24, 12), "left"),
]


def spawn_body(index: int):
    """按出生点序号生成 (body, direction)。"""
    (hx, hy), d = SPAWNS[index % len(SPAWNS)]
    dx, dy = DIRS[d]
    return [(hx - dx * i, hy - dy * i) for i in range(START_LENGTH)], d


class Snake:
    __slots__ = ("id", "name", "color", "skin", "body", "direction", "next_dir",
                 "alive", "score", "respawn_in", "ghost", "shield", "slow", "skill_cd")

    def __init__(self, pid, name, color, skin, body, direction):
        self.id = pid
        self.name = name
        self.color = color
        self.skin = skin
        self.body = [tuple(c) for c in body]
        self.direction = direction
        self.next_dir = direction
        self.alive = True
        self.score = 0
        self.respawn_in = 0.0
        self.ghost = 0.0        # 隐身：别人只看到残影
        self.shield = 0.0       # 无敌：致死的移动会被取消
        self.slow = 0.0         # 被减速：隔一个 tick 才动一次
        self.skill_cd = 0.0

    def target(self):
        dx, dy = DIRS[self.direction]
        hx, hy = self.body[0]
        return (hx + dx, hy + dy)

    def set_direction(self, d: str) -> bool:
        """非法或 180 度掉头一律忽略。"""
        if d not in DIRS:
            return False
        if d == self.direction or d == OPPOSITE[self.direction]:
            return False
        self.next_dir = d
        return True

    def clear_effects(self) -> None:
        self.ghost = self.shield = self.slow = 0.0

    def to_json(self) -> dict:
        return {
            "id": self.id,
            "name": self.name,
            "body": [[x, y] for x, y in self.body],
            "direction": self.direction,
            "alive": self.alive,
            "score": self.score,
            "color": self.color,
            "skin": self.skin,
            "respawnIn": round(self.respawn_in, 2),
            "ghost": round(self.ghost, 2),
            "shield": round(self.shield, 2),
            "slow": round(self.slow, 2),
            "skillCd": round(self.skill_cd, 2),
        }


class Player:
    def __init__(self, pid, name, color, skin, ws):
        self.id = pid
        self.name = name
        self.color = color
        self.skin = skin
        self.ws = ws
        self.ready = False
        self.skill = "blink"


class Room:
    def __init__(self) -> None:
        self.id = ROOM_ID
        self.players: dict[str, Player] = {}
        self.snakes: dict[str, Snake] = {}
        self.foods: list[dict] = []
        self.status = "lobby"            # lobby | playing | paused | over
        self.difficulty = DEFAULT_DIFFICULTY
        self.tick_seconds = TICK_SECONDS
        self.tick = 0
        self.time_left = ROUND_SECONDS
        self.winner_id: Optional[str] = None
        self.over_reason: Optional[str] = None
        self.ranking: list[dict] = []
        self.host_id: Optional[str] = None
        self.lock = asyncio.Lock()
        self.task: Optional[asyncio.Task] = None
        self._next_pid = 1

    # ------------------------------------------------------------------ 消息构造

    def room_msg(self) -> dict:
        return {
            "type": "room",
            "players": [
                {
                    "id": p.id, "name": p.name, "color": p.color,
                    "isHost": p.id == self.host_id, "ready": p.ready,
                    "skin": p.skin, "skill": p.skill,
                }
                for p in self.players.values()
            ],
            "status": self.status,
            "hostId": self.host_id,
            "maxPlayers": MAX_PLAYERS,
            "difficulty": self.difficulty,
        }

    def state_msg(self) -> dict:
        return {
            "type": "state",
            "tick": self.tick,
            "timeLeft": round(self.time_left, 2),
            "foods": [dict(f) for f in self.foods],
            "snakes": [s.to_json() for s in self.snakes.values()],
            "status": self.status,
        }

    def over_msg(self) -> dict:
        return {
            "type": "over",
            "winnerId": self.winner_id,
            "reason": self.over_reason,
            "ranking": self.ranking,
        }

    # ------------------------------------------------------------------ 地图

    def diff(self) -> dict:
        return DIFFICULTIES.get(self.difficulty, DIFFICULTIES[DEFAULT_DIFFICULTY])

    def occupied(self) -> set:
        cells = {(f["x"], f["y"]) for f in self.foods}
        for s in self.snakes.values():
            if s.alive:
                cells.update(s.body)
        return cells

    def free_cells(self):
        occ = self.occupied()
        return [(x, y) for y in range(ROWS) for x in range(COLS) if (x, y) not in occ]

    def roll_kind(self) -> str:
        """按难度概率决定新食物是不是特殊食物；三种特殊类型等概率。"""
        if random.random() < self.diff()["special"]:
            return random.choice(("ghost", "slow", "shield"))
        return "normal"

    def add_food(self, cell, kind: str = "normal") -> None:
        self.foods.append({"x": cell[0], "y": cell[1], "kind": kind})

    def top_up_food(self) -> None:
        """把食物补到常驻数量。被吃掉的食物只补回 BASE_FOODS，不会无限增长。"""
        while len(self.foods) < BASE_FOODS:
            free = self.free_cells()
            if not free:
                return
            self.add_food(random.choice(free), self.roll_kind())

    def pick_spawn(self):
        occ = self.occupied()
        cands = [(body, d) for body, d in (spawn_body(i) for i in range(len(SPAWNS)))
                 if all(c not in occ for c in body)]
        return random.choice(cands) if cands else None

    # ------------------------------------------------------------------ 连接管理

    async def ensure_task(self) -> None:
        if self.task is None or self.task.done():
            self.task = asyncio.create_task(self.run())

    def _free_skin(self) -> int:
        used = {p.skin for p in self.players.values()}
        return next((i for i in range(SKIN_COUNT) if i not in used), 0)

    async def join(self, ws: WebSocket, name: str):
        """返回 (player, error)。"""
        async with self.lock:
            # 页面刷新后旧连接可能还没被判定断开，同名玩家直接顶替以保证能重新加入
            for old in list(self.players.values()):
                if old.name == name:
                    self.players.pop(old.id, None)
                    self.snakes.pop(old.id, None)
                    break

            if len(self.players) >= MAX_PLAYERS:
                return None, f"房间已满（最多 {MAX_PLAYERS} 人）"

            skin = self._free_skin()
            pid = f"p{self._next_pid}"
            self._next_pid += 1
            if not name:
                name = f"玩家{skin + 1}"
            player = Player(pid, name, COLORS[skin % len(COLORS)], skin, ws)
            self.players[pid] = player

            if self.host_id is None or self.host_id not in self.players:
                self.host_id = pid

        await self.ensure_task()
        # 房间广播交给调用方在 welcome 之后发：客户端要先知道自己的 id/皮肤，
        # 再收到房间列表，否则界面会在「输入名字」那一屏多停一拍
        return player, None

    async def leave(self, pid: str) -> None:
        async with self.lock:
            player = self.players.pop(pid, None)
            if player is None:
                return
            self.snakes.pop(pid, None)

            # 人不够 2 个就没法继续，直接结束本局
            if self.status in ("playing", "paused") and len(self.players) < 2:
                self.finish("disconnect")

            if self.players and (self.host_id is None or self.host_id not in self.players):
                self.host_id = next(iter(self.players))

            if not self.players:
                # 房间空了就彻底回到干净的大厅状态
                self.status = "lobby"
                self.snakes.clear()
                self.foods.clear()
                self.tick = 0
                self.time_left = self.diff()["round"]
                self.winner_id = None
                self.over_reason = None
                self.ranking = []
                self.host_id = None

        await self.broadcast_room()

    async def broadcast(self, msg: dict) -> None:
        """只应在不持有 lock 时调用。"""
        data = json.dumps(msg)
        for player in list(self.players.values()):
            try:
                await player.ws.send_text(data)
            except Exception:
                asyncio.create_task(self.leave(player.id))

    async def broadcast_room(self) -> None:
        await self.broadcast(self.room_msg())

    async def send(self, pid: str, msg: dict) -> None:
        player = self.players.get(pid)
        if player is None:
            return
        try:
            await player.ws.send_text(json.dumps(msg))
        except Exception:
            asyncio.create_task(self.leave(pid))

    # ------------------------------------------------------------------ 游戏流程

    def reset_round(self) -> None:
        self.tick = 0
        self.tick_seconds = self.diff()["tick"]
        self.time_left = self.diff()["round"]
        self.winner_id = None
        self.over_reason = None
        self.ranking = []
        self.foods = []
        self.snakes = {}
        for i, player in enumerate(self.players.values()):
            body, direction = spawn_body(i)
            self.snakes[player.id] = Snake(
                player.id, player.name, player.color, player.skin, body, direction)
            player.ready = False
        self.top_up_food()

    async def set_ready(self, pid: str, ready: bool) -> None:
        async with self.lock:
            player = self.players.get(pid)
            if player is None:
                return
        # 任何状态下都允许准备：本局打到一半才进来的人可以先把下一局准备好，
        # 房主看到全员就绪就能立刻开新一局，不用干等当前这局的计时走完
        player.ready = bool(ready)
        await self.broadcast_room()

    def _apply_skin(self, player: Player) -> None:
        player.color = COLORS[player.skin % len(COLORS)]
        snake = self.snakes.get(player.id)
        if snake is not None:
            snake.skin = player.skin
            snake.color = player.color

    async def set_skin(self, pid: str, skin: int) -> None:
        async with self.lock:
            player = self.players.get(pid)
            if player is None or not isinstance(skin, int) or not (0 <= skin < SKIN_COUNT):
                return
            if skin == player.skin:
                return
            # 皮肤在场上保持唯一；选了别人正在用的就跟对方互换，
            # 这样 5 人满员（皮肤全被占）时也始终能改自己的形象
            other = next((p for p in self.players.values() if p.skin == skin), None)
            if other is not None:
                other.skin = player.skin
                self._apply_skin(other)
            player.skin = skin
            self._apply_skin(player)
        await self.broadcast_room()

    async def emote(self, pid: str, emote) -> None:
        async with self.lock:
            if pid not in self.players:
                return
        text = str(emote)[:8]
        await self.broadcast({"type": "emote", "playerId": pid, "emote": text})

    async def start(self, pid: str) -> Optional[str]:
        async with self.lock:
            if pid != self.host_id:
                return "只有主机可以开始游戏"
            if len(self.players) >= 2:
                not_ready = [p.name for p in self.players.values() if not p.ready]
                if not_ready:
                    return "还有玩家未准备：" + "、".join(not_ready)
            # 只有房主一个人时也允许开始 —— 方便自己开局测试特殊食物、技能和难度
            self.reset_round()
            self.status = "playing"
            state = self.state_msg()
        await self.broadcast(state)
        await self.broadcast_room()
        return None

    async def toggle_pause(self, pid: str) -> None:
        async with self.lock:
            if pid != self.host_id:      # 限时局里让任何人暂停会变成干扰手段
                return
            if self.status == "playing":
                self.status = "paused"
            elif self.status == "paused":
                self.status = "playing"
            else:
                return
            state = self.state_msg()
        await self.broadcast(state)

    async def set_skill(self, pid: str, skill) -> None:
        async with self.lock:
            player = self.players.get(pid)
            if player is None or skill not in SKILLS:
                return
            player.skill = skill
        await self.broadcast_room()

    async def set_difficulty(self, pid: str, value) -> None:
        async with self.lock:
            if pid != self.host_id or value not in DIFFICULTIES:
                return
            if self.status not in ("lobby", "over"):
                return
            self.difficulty = value
            self.tick_seconds = DIFFICULTIES[value]["tick"]
        await self.broadcast_room()

    def do_blink(self, snake: Snake) -> bool:
        """向前瞬移若干格，撞到墙/别的蛇/食物就停在可达的最远格；整条蛇一起平移。"""
        dx, dy = DIRS[snake.direction]
        hx, hy = snake.body[0]

        blocked = set()
        for o in self.snakes.values():
            if o.alive and o.id != snake.id:
                blocked.update(o.body)        # 自己的身体不算，因为整条蛇会一起挪走
        for f in self.foods:
            blocked.add((f["x"], f["y"]))

        best = None
        for step in range(1, BLINK_CELLS + 1):
            nx, ny = hx + dx * step, hy + dy * step
            if not (0 <= nx < COLS and 0 <= ny < ROWS):
                break
            if (nx, ny) in blocked:
                break
            best = (nx, ny)
        if best is None:
            return False

        mx, my = best[0] - hx, best[1] - hy
        snake.body = [(x + mx, y + my) for x, y in snake.body]
        return True

    async def use_skill(self, pid: str) -> None:
        async with self.lock:
            if self.status != "playing":
                return
            snake = self.snakes.get(pid)
            player = self.players.get(pid)
            if snake is None or player is None or not snake.alive or snake.skill_cd > 0:
                return

            skill = player.skill
            if skill == "blink":
                if not self.do_blink(snake):
                    return                     # 前方完全被挡住，不消耗冷却
            elif skill == "shield":
                snake.shield = max(snake.shield, SKILL_SHIELD_SECONDS)
            elif skill == "slow":
                for o in self.snakes.values():
                    if o.alive and o.id != pid:
                        o.slow = max(o.slow, SKILL_SLOW_SECONDS)
            else:
                return

            snake.skill_cd = SKILL_COOLDOWN
            state = self.state_msg()
        await self.broadcast(state)

    def handle_input(self, pid: str, d) -> None:
        if self.status != "playing":
            return
        snake = self.snakes.get(pid)
        if snake is None or not snake.alive:
            return
        snake.set_direction(d)

    # ------------------------------------------------------------------ 单步

    def kill_snake(self, snake: Snake) -> None:
        """死亡：身体变成食物，进入复活倒计时，分数保留。"""
        body = list(snake.body)
        # 先把自己从场上摘掉，否则下面算占用时会被自己挡住，一个食物都掉不出来
        snake.alive = False
        snake.body = []
        snake.respawn_in = RESPAWN_SECONDS
        snake.clear_effects()

        if body:
            stride = max(1, len(body) // CORPSE_FOOD)
            occupied = self.occupied()
            for cell in body[::stride][:CORPSE_FOOD]:
                if len(self.foods) >= MAX_FOODS:
                    break
                if cell not in occupied:
                    self.add_food(cell, "normal")   # 尸体只掉普通食物
                    occupied.add(cell)

    def respawn(self, snake: Snake) -> bool:
        pick = self.pick_spawn()
        if pick is None:
            return False
        body, direction = pick
        snake.body = [tuple(c) for c in body]
        snake.direction = direction
        snake.next_dir = direction
        snake.alive = True
        snake.respawn_in = 0.0
        snake.clear_effects()
        return True

    def finish(self, reason: str) -> None:
        self.status = "over"
        self.over_reason = reason
        ranked = sorted(self.snakes.values(), key=lambda s: (-s.score, s.name))
        self.ranking = [{"id": s.id, "name": s.name, "score": s.score,
                         "color": s.color, "skin": s.skin} for s in ranked]
        if ranked and (len(ranked) == 1 or ranked[0].score > ranked[1].score):
            self.winner_id = ranked[0].id
        else:
            self.winner_id = None          # 平分或空场 -> 平局
        for p in self.players.values():
            p.ready = False

    def apply_food_effect(self, snake: Snake, kind: str) -> None:
        if kind == "ghost":
            snake.ghost = max(snake.ghost, EFFECT_SECONDS)
        elif kind == "shield":
            snake.shield = max(snake.shield, EFFECT_SECONDS)
        elif kind == "slow":
            # 「慢速」作用在其他玩家身上
            for o in self.snakes.values():
                if o.alive and o.id != snake.id:
                    o.slow = max(o.slow, EFFECT_SECONDS)

    def step(self) -> list[dict]:
        """推进一步，返回需要广播的击杀事件。tick 由自己递增，调用方不需要管。"""
        events: list[dict] = []
        self.tick += 1
        dt = self.tick_seconds
        self.time_left = max(0.0, self.time_left - dt)

        for s in self.snakes.values():
            s.ghost = max(0.0, s.ghost - dt)
            s.shield = max(0.0, s.shield - dt)
            s.slow = max(0.0, s.slow - dt)
            s.skill_cd = max(0.0, s.skill_cd - dt)
            if not s.alive and s.respawn_in > 0:
                s.respawn_in = max(0.0, s.respawn_in - dt)
                if s.respawn_in <= 1e-6:      # 浮点累减不会精确落到 0
                    self.respawn(s)

        alive = [s for s in self.snakes.values() if s.alive]
        if alive:
            for s in alive:
                s.direction = s.next_dir

            # 被减速的蛇隔一个 tick 才动一次
            movers = [s for s in alive if self.tick % (2 if s.slow > 0 else 1) == 0]
            new_head = {s.id: s.target() for s in movers}
            foods = {(f["x"], f["y"]): f["kind"] for f in self.foods}
            dead: dict[str, tuple[str, Optional[str]]] = {}

            # 头对头只在这次真正移动的蛇之间判定
            for i in range(len(movers)):
                for j in range(i + 1, len(movers)):
                    a, b = movers[i], movers[j]
                    if new_head[a.id] == new_head[b.id] or (
                            new_head[a.id] == b.body[0] and new_head[b.id] == a.body[0]):
                        dead[a.id] = ("head_on", None)
                        dead[b.id] = ("head_on", None)

            grow = {s.id: (s.id not in dead and new_head[s.id] in foods) for s in movers}

            # 移动后占据的格子：移动的蛇去掉让位的尾巴，没动的蛇原地不动
            blocked: dict = {}
            for s in alive:
                segs = (s.body if grow[s.id] else s.body[:-1]) if s in movers else s.body
                for c in segs:
                    blocked[c] = s.id

            cancelled: set[str] = set()
            for s in movers:
                if s.id in dead:
                    continue
                h = new_head[s.id]
                fatal = None
                if not (0 <= h[0] < COLS and 0 <= h[1] < ROWS):
                    fatal = ("wall", None)
                elif h in blocked:
                    owner = blocked[h]
                    fatal = ("self" if owner == s.id else "body", owner)
                if fatal is None:
                    continue
                if s.shield > 0:
                    cancelled.add(s.id)      # 无敌：这次移动直接取消，蛇留在原地
                else:
                    dead[s.id] = fatal

            eaten = set()
            for s in movers:
                if s.id in dead or s.id in cancelled:
                    continue
                s.body.insert(0, new_head[s.id])
                if grow[s.id]:
                    s.score += FOOD_SCORE
                    eaten.add(new_head[s.id])
                    self.apply_food_effect(s, foods[new_head[s.id]])
                else:
                    s.body.pop()

            if eaten:
                self.foods = [f for f in self.foods if (f["x"], f["y"]) not in eaten]
                self.top_up_food()

            for s in alive:
                if s.id in dead:
                    reason, killer = dead[s.id]
                    self.kill_snake(s)
                    events.append({"type": "kill", "killerId": killer,
                                   "victimId": s.id, "reason": reason})

        if self.time_left <= 0:
            self.finish("time")

        return events

    async def run(self) -> None:
        """房间循环：固定 tick 推进并广播。"""
        try:
            while True:
                await asyncio.sleep(self.tick_seconds)
                out: list[dict] = []
                async with self.lock:
                    if not self.players:
                        break
                    if self.status != "playing":
                        continue
                    out.extend(self.step())
                    out.append(self.state_msg())
                    if self.status == "over":
                        out.append(self.over_msg())
                for msg in out:
                    await self.broadcast(msg)
                if self.status == "over":
                    await self.broadcast_room()
        except asyncio.CancelledError:
            raise
        finally:
            self.task = None


app = FastAPI(title="LAN Snake Battle")
ROOM = Room()


@app.get("/")
async def index() -> FileResponse:
    return FileResponse(BASE_DIR / "index.html")


@app.get("/health")
async def health() -> dict:
    return {
        "ok": True,
        "status": ROOM.status,
        "players": len(ROOM.players),
        "timeLeft": round(ROOM.time_left, 1),
        "foods": len(ROOM.foods),
    }


@app.websocket("/ws")
async def ws_endpoint(ws: WebSocket) -> None:
    await ws.accept()
    pid: Optional[str] = None
    try:
        while True:
            raw = await ws.receive_text()
            try:
                msg = json.loads(raw)
            except json.JSONDecodeError:
                await ws.send_text(json.dumps({"type": "error", "message": "消息不是合法 JSON"}))
                continue
            if not isinstance(msg, dict):
                continue

            kind = msg.get("type")

            if kind == "join":
                if pid is not None:
                    continue
                name = str(msg.get("name") or "").strip()[:16]
                player, err = await ROOM.join(ws, name)
                if err:
                    await ws.send_text(json.dumps({"type": "error", "message": err}))
                    continue
                pid = player.id
                await ws.send_text(json.dumps({
                    "type": "welcome",
                    "id": player.id,
                    "color": player.color,
                    "skin": player.skin,
                    "roomId": ROOM.id,
                    "cols": COLS,
                    "rows": ROWS,
                    "roundSeconds": ROOM.diff()["round"],
                    "maxPlayers": MAX_PLAYERS,
                    "difficulty": ROOM.difficulty,
                    "skills": SKILL_INFO,
                }, ensure_ascii=False))
                await ROOM.broadcast_room()

            elif pid is None:
                await ws.send_text(json.dumps({"type": "error", "message": "请先加入房间"}))

            elif kind == "input":
                ROOM.handle_input(pid, msg.get("dir"))

            elif kind == "ready":
                await ROOM.set_ready(pid, msg.get("ready"))

            elif kind == "skin":
                await ROOM.set_skin(pid, msg.get("skin"))

            elif kind == "emote":
                await ROOM.emote(pid, msg.get("emote"))

            elif kind == "skill":
                await ROOM.use_skill(pid)

            elif kind == "setskill":
                await ROOM.set_skill(pid, msg.get("skill"))

            elif kind == "difficulty":
                await ROOM.set_difficulty(pid, msg.get("value"))

            elif kind == "start" or kind == "restart":
                err = await ROOM.start(pid)
                if err:
                    await ROOM.send(pid, {"type": "error", "message": err})

            elif kind == "pause":
                await ROOM.toggle_pause(pid)

            elif kind == "ping":
                await ws.send_text(json.dumps({"type": "pong", "time": msg.get("time")}))

    except WebSocketDisconnect:
        pass
    except Exception:
        pass
    finally:
        if pid is not None:
            await ROOM.leave(pid)


def local_ips() -> list[str]:
    ips: set[str] = set()
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("8.8.8.8", 80))
        ips.add(s.getsockname()[0])
        s.close()
    except OSError:
        pass
    try:
        for info in socket.getaddrinfo(socket.gethostname(), None, socket.AF_INET):
            ips.add(info[4][0])
    except OSError:
        pass
    return sorted(ip for ip in ips if not ip.startswith("127."))


def print_banner() -> None:
    lines = ["", "=" * 46, "  5 人抢食混战贪吃蛇 —— 服务器已启动", "=" * 46]
    if ON_CLOUD:
        lines += [
            f"  云端模式 · 监听端口 {PORT}",
            "  用平台分配的域名访问，手机浏览器直接打开即可",
        ]
    else:
        lines.append(f"  本机访问：    http://localhost:{PORT}")
        for ip in local_ips():
            lines.append(f"  局域网访问：  http://{ip}:{PORT}")
        lines += [
            "-" * 46,
            "  让其他设备连到上面任意一个「局域网访问」地址（手机连同一个 WiFi 即可）",
        ]
    lines += [
        "-" * 46,
        f"  最多 {MAX_PLAYERS} 人同屏 · 三档难度 · 特殊食物 · 每人一个技能",
        "  按 Ctrl+C 停止服务器",
        "=" * 46,
        "",
    ]
    print("\n".join(lines), flush=True)


if __name__ == "__main__":
    print_banner()
    uvicorn.run(app, host="0.0.0.0", port=PORT, log_level="info")
