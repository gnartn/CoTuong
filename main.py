# main.py (refactored)
from __future__ import annotations

import asyncio
import copy
import json
import random
import sqlite3
import time
import traceback
import uuid
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

from fastapi import FastAPI, WebSocket, WebSocketDisconnect
from fastapi.responses import FileResponse, JSONResponse
from fastapi.staticfiles import StaticFiles

# -----------------------------------------------------------------------------
# App & Static
# -----------------------------------------------------------------------------
app = FastAPI()
app.mount("/static", StaticFiles(directory="static"), name="static")

DB_PATH = "games.db"

# -----------------------------------------------------------------------------
# DB helpers
# -----------------------------------------------------------------------------
def init_db() -> None:
    with sqlite3.connect(DB_PATH) as conn:
        c = conn.cursor()
        c.execute(
            """
            CREATE TABLE IF NOT EXISTS games (
                id TEXT PRIMARY KEY,
                room TEXT,
                player_red TEXT,
                player_black TEXT,
                start_ts INTEGER,
                end_ts INTEGER,
                winner TEXT
            )
            """
        )
        c.execute(
            """
            CREATE TABLE IF NOT EXISTS moves (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                game_id TEXT,
                move_index INTEGER,
                from_x INTEGER, from_y INTEGER,
                to_x INTEGER, to_y INTEGER,
                piece TEXT,
                ts INTEGER
            )
            """
        )
        conn.commit()


def db_execute(sql: str, params: Tuple = ()) -> None:
    try:
        with sqlite3.connect(DB_PATH) as conn:
            conn.execute(sql, params)
            conn.commit()
    except Exception as e:
        print(f"[DB] Error: {e}")


def db_query_all(sql: str, params: Tuple = ()) -> List[Tuple]:
    try:
        with sqlite3.connect(DB_PATH) as conn:
            cur = conn.execute(sql, params)
            return cur.fetchall()
    except Exception as e:
        print(f"[DB] Query error: {e}")
        return []


def create_game_record(room_id: str, player_red: str, player_black: str) -> Optional[str]:
    gid = str(uuid.uuid4())
    ts = int(time.time())
    try:
        db_execute(
            "INSERT INTO games(id, room, player_red, player_black, start_ts) VALUES (?,?,?,?,?)",
            (gid, room_id, player_red, player_black, ts),
        )
        return gid
    except Exception as e:
        print(f"[DB] create_game_record error: {e}")
        return None


def add_move_record(game_id: str, idx: int, fx: int, fy: int, tx: int, ty: int, piece: str) -> None:
    ts = int(time.time())
    db_execute(
        "INSERT INTO moves(game_id, move_index, from_x, from_y, to_x, to_y, piece, ts) "
        "VALUES (?,?,?,?,?,?,?,?)",
        (game_id, idx, fx, fy, tx, ty, piece, ts),
    )


def finish_game_record(game_id: Optional[str], winner: str) -> None:
    if not game_id:
        return
    ts = int(time.time())
    db_execute("UPDATE games SET end_ts=?, winner=? WHERE id=?", (ts, winner, game_id))


# -----------------------------------------------------------------------------
# Game model / in-memory state
# -----------------------------------------------------------------------------
Board = List[List[str]]

RED_SET = {'俥', '傌', '相', '仕', '帥', '炮', '兵'}
BLACK_SET = {'車', '馬', '象', '士', '將', '砲', '卒'}

def get_color(piece: str) -> str:
    if piece in RED_SET:
        return 'red'
    if piece in BLACK_SET:
        return 'black'
    return 'none'


def get_opponent_color(color: str) -> str:
    return 'black' if color == 'red' else 'red'


def init_board() -> dict:
    board = [["" for _ in range(9)] for _ in range(10)]
    board[0] = ['車', '馬', '象', '士', '將', '士', '象', '馬', '車']
    board[2] = ['', '砲', '', '', '', '', '', '砲', '']
    board[3] = ['卒', '', '卒', '', '卒', '', '卒', '', '卒']

    board[9] = ['俥', '傌', '相', '仕', '帥', '仕', '相', '傌', '俥']
    board[7] = ['', '炮', '', '', '', '', '', '炮', '']
    board[6] = ['兵', '', '兵', '', '兵', '', '兵', '', '兵']
    return {"board": board}


def is_in_palace(x: int, y: int, color: str) -> bool:
    if not (3 <= x <= 5):
        return False
    if color == 'red' and (7 <= y <= 9):
        return True
    if color == 'black' and (0 <= y <= 2):
        return True
    return False


def find_king(board: Board, color: str) -> Tuple[int, int]:
    k = '帥' if color == 'red' else '將'
    for y in range(10):
        for x in range(9):
            if board[y][x] == k:
                return x, y
    return -1, -1


def count_blockers(board: Board, fx: int, fy: int, tx: int, ty: int) -> int:
    count = 0
    if fx == tx:
        step = 1 if ty > fy else -1
        for y in range(fy + step, ty, step):
            if board[y][fx] != "":
                count += 1
    elif fy == ty:
        step = 1 if tx > fx else -1
        for x in range(fx + step, tx, step):
            if board[fy][x] != "":
                count += 1
    return count


def _is_legal_chariot(board: Board, fx: int, fy: int, tx: int, ty: int) -> bool:
    return (fx == tx or fy == ty) and count_blockers(board, fx, fy, tx, ty) == 0


def _is_legal_horse(board: Board, fx: int, fy: int, tx: int, ty: int) -> bool:
    dx, dy = abs(tx - fx), abs(ty - fy)
    if not ((dx == 1 and dy == 2) or (dx == 2 and dy == 1)):
        return False
    if dx == 2:  # chặn ngang
        return board[fy][(fx + tx) // 2] == ""
    else:  # chặn dọc
        return board[(fy + ty) // 2][fx] == ""


def _is_legal_elephant(board: Board, fx: int, fy: int, tx: int, ty: int, color: str) -> bool:
    if not (abs(tx - fx) == 2 and abs(ty - fy) == 2):
        return False
    if (color == 'red' and ty < 5) or (color == 'black' and ty > 4):
        return False
    return board[(fy + ty) // 2][(fx + tx) // 2] == ""


def _is_legal_advisor(board: Board, fx: int, fy: int, tx: int, ty: int, color: str) -> bool:
    return abs(tx - fx) == 1 and abs(ty - fy) == 1 and is_in_palace(tx, ty, color)


def _is_legal_general(board: Board, fx: int, fy: int, tx: int, ty: int, color: str) -> bool:
    return (abs(tx - fx) + abs(ty - fy) == 1) and is_in_palace(tx, ty, color)


def _is_legal_cannon(board: Board, fx: int, fy: int, tx: int, ty: int, target_piece: str) -> bool:
    if not (fx == tx or fy == ty):
        return False
    blockers = count_blockers(board, fx, fy, tx, ty)
    if target_piece == "":
        return blockers == 0
    return blockers == 1


def _is_legal_soldier(board: Board, fx: int, fy: int, tx: int, ty: int, color: str) -> bool:
    dx, dy = abs(tx - fx), abs(ty - fy)
    if dx + dy != 1:
        return False
    if color == 'red':
        if ty > fy:  # không đi lùi
            return False
        if fy >= 5 and tx != fx:  # chưa qua sông không đi ngang
            return False
    else:
        if ty < fy:
            return False
        if fy <= 4 and tx != fx:
            return False
    return True


def is_legal_move_for_piece(board: Board, fx: int, fy: int, tx: int, ty: int) -> bool:
    piece = board[fy][fx]
    color = get_color(piece)
    target = board[ty][tx]
    if piece in ['俥', '車']:
        return _is_legal_chariot(board, fx, fy, tx, ty)
    if piece in ['傌', '馬']:
        return _is_legal_horse(board, fx, fy, tx, ty)
    if piece in ['相', '象']:
        return _is_legal_elephant(board, fx, fy, tx, ty, color)
    if piece in ['仕', '士']:
        return _is_legal_advisor(board, fx, fy, tx, ty, color)
    if piece in ['帥', '將']:
        return _is_legal_general(board, fx, fy, tx, ty, color)
    if piece in ['炮', '砲']:
        return _is_legal_cannon(board, fx, fy, tx, ty, target)
    if piece in ['兵', '卒']:
        return _is_legal_soldier(board, fx, fy, tx, ty, color)
    return False


def is_square_attacked(board: Board, x: int, y: int, attacker: str) -> bool:
    for fy in range(10):
        for fx in range(9):
            if get_color(board[fy][fx]) == attacker:
                if is_legal_move_for_piece(board, fx, fy, x, y):
                    return True
    return False


def is_king_in_check(board: Board, color: str) -> bool:
    kx, ky = find_king(board, color)
    return (kx, ky) != (-1, -1) and is_square_attacked(board, kx, ky, get_opponent_color(color))


def is_flying_general(board: Board) -> bool:
    rx, ry = find_king(board, 'red')
    bx, by = find_king(board, 'black')
    if rx == -1 or bx == -1 or rx != bx:
        return False
    return count_blockers(board, rx, ry, bx, by) == 0


def apply_move(state: dict, move: dict) -> None:
    fx, fy = move["from"]["x"], move["from"]["y"]
    tx, ty = move["to"]["x"], move["to"]["y"]
    piece = state["board"][fy][fx]
    state["board"][fy][fx] = ""
    state["board"][ty][tx] = piece


def is_valid_move(board: Board, move: dict, player_color: str) -> Tuple[bool, str]:
    fx, fy = move["from"]["x"], move["from"]["y"]
    tx, ty = move["to"]["x"], move["to"]["y"]
    if not (0 <= fx < 9 and 0 <= fy < 10 and 0 <= tx < 9 and 0 <= ty < 10):
        return False, "Đi ra ngoài bàn cờ"
    piece = board[fy][fx]
    if piece == "":
        return False, "Ô trống, không có quân"
    if get_color(piece) != player_color:
        return False, "Không phải quân của bạn"
    target = board[ty][tx]
    if target != "" and get_color(target) == player_color:
        return False, "Không thể ăn quân mình"
    if not is_legal_move_for_piece(board, fx, fy, tx, ty):
        return False, "Nước đi không hợp lệ"
    return True, ""


# -----------------------------------------------------------------------------
# Room & global state
# -----------------------------------------------------------------------------
@dataclass
class GameRoom:
    room_id: str
    players: Dict[WebSocket, str] = field(default_factory=dict)  # ws -> name
    player_colors: Dict[str, str] = field(default_factory=dict)  # name -> 'red'|'black'
    state: dict = field(default_factory=init_board)
    turn: str = "red"
    game_id: Optional[str] = None
    move_count: int = 0
    clocks: Dict[str, int] = field(default_factory=lambda: {"red": 300, "black": 300})
    timer_task: Optional[asyncio.Task] = None
    rematch_offered_by: Optional[str] = None


# in-memory registries
lobby: Dict[WebSocket, str] = {}           # {ws: name}
rooms: Dict[str, GameRoom] = {}            # {room_id: GameRoom}
player_room_map: Dict[WebSocket, str] = {} # {ws: room_id}
pending_challenges: Dict[str, str] = {}    # target_name -> challenger
pending_challenge_targets: Dict[str, str] = {}  # challenger -> target
lock = asyncio.Lock()


# -----------------------------------------------------------------------------
# Messaging helpers
# -----------------------------------------------------------------------------
def dumps(obj: dict) -> str:
    return json.dumps(obj, ensure_ascii=False)

async def safe_send(ws: WebSocket, payload: dict) -> None:
    try:
        await ws.send_text(dumps(payload))
    except Exception:
        pass

async def broadcast_to_room(room_id: str, message: dict, exclude_ws: Optional[WebSocket] = None) -> None:
    if room_id not in rooms:
        return
    tasks = []
    for ws in list(rooms[room_id].players.keys()):
        if ws is not exclude_ws:
            tasks.append(safe_send(ws, message))
    if tasks:
        await asyncio.gather(*tasks, return_exceptions=True)

async def broadcast_to_lobby(message: dict, exclude_ws: Optional[WebSocket] = None) -> None:
    tasks = []
    for ws in list(lobby.keys()):
        if ws is not exclude_ws:
            tasks.append(safe_send(ws, message))
    if tasks:
        await asyncio.gather(*tasks, return_exceptions=True)

async def send_lobby_update() -> None:
    players = list(lobby.values())
    dead = []
    for ws, name in list(lobby.items()):
        try:
            await ws.send_text(dumps({"type": "lobby_update", "players": players}))
        except Exception as e:
            print(f"[WARN] Không gửi được cho {name}: {e}")
            dead.append(ws)
    for ws in dead:
        lobby.pop(ws, None)
    print(f"[LOBBY] {len(players)} người: {', '.join(players) if players else 'Sảnh trống.'}")

async def send_state(room_id: str) -> None:
    if room_id not in rooms:
        return
    g = rooms[room_id]
    b = g.state["board"]
    payload = {
        "type": "state",
        "turn": g.turn,
        "state": g.state,
        "colors": g.player_colors,
        "clocks": g.clocks,
        "check_state": {"red": is_king_in_check(b, 'red'), "black": is_king_in_check(b, 'black')},
    }
    await broadcast_to_room(room_id, payload)

async def send_game_over(room_id: str, winner_color: str, reason: str) -> None:
    if room_id not in rooms:
        return
    g = rooms[room_id]

    if g.timer_task:
        try:
            g.timer_task.cancel()
        except Exception:
            pass
        g.timer_task = None

    # resolve winner name from color
    winner_name = None
    for name, color in g.player_colors.items():
        if color == winner_color:
            winner_name = name
            break
    if winner_name is None and "Bot" in g.player_colors and g.player_colors["Bot"] == winner_color:
        winner_name = "Bot"
    if winner_name is None:
        winner_name = winner_color.capitalize()

    if g.game_id:
        finish_game_record(g.game_id, winner_name)

    g.game_id = None
    g.rematch_offered_by = None

    await broadcast_to_room(
        room_id,
        {"type": "game_over", "winner_color": winner_color, "winner_name": winner_name, "reason": reason},
    )


# -----------------------------------------------------------------------------
# Timer
# -----------------------------------------------------------------------------
async def timer_loop(room_id: str) -> None:
    print(f"[TIMER] start {room_id}")
    try:
        while True:
            await asyncio.sleep(1)
            async with lock:
                if room_id not in rooms:
                    break
                g = rooms[room_id]
                if g.game_id is None:
                    continue

                turn = g.turn
                # đừng trừ khi tới lượt Bot
                if "Bot" in g.player_colors and g.player_colors.get("Bot") == turn:
                    continue

                g.clocks[turn] -= 1
                await broadcast_to_room(room_id, {"type": "clock_update", "clocks": g.clocks})

                if g.clocks[turn] <= 0:
                    winner = get_opponent_color(turn)
                    await send_game_over(room_id, winner, f"{turn.capitalize()} hết giờ")
                    break
    except asyncio.CancelledError:
        print(f"[TIMER] cancelled {room_id}")
    except Exception as e:
        print(f"[TIMER] error {room_id}: {e}")
        traceback.print_exc()
        async with lock:
            if room_id in rooms:
                rooms[room_id].timer_task = None


# -----------------------------------------------------------------------------
# Bot
# -----------------------------------------------------------------------------
def _apply_move_on_copy(board: Board, move: dict) -> Board:
    b = copy.deepcopy(board)
    fx, fy = move["from"]["x"], move["from"]["y"]
    tx, ty = move["to"]["x"], move["to"]["y"]
    b[ty][tx] = b[fy][fx]
    b[fy][fx] = ""
    return b

async def run_bot_move(room_id: str, bot_color: str) -> None:
    await asyncio.sleep(1.0)
    try:
        async with lock:
            if room_id not in rooms:
                return
            g = rooms[room_id]
            if g.game_id is None or g.turn != bot_color:
                return

            board = g.state["board"]
            all_moves: List[dict] = []

            for y in range(10):
                for x in range(9):
                    if get_color(board[y][x]) != bot_color:
                        continue
                    for ty in range(10):
                        for tx in range(9):
                            move = {"from": {"x": x, "y": y}, "to": {"x": tx, "y": ty}}
                            ok, _ = is_valid_move(board, move, bot_color)
                            if not ok:
                                continue
                            nb = _apply_move_on_copy(board, move)
                            if is_flying_general(nb) or is_king_in_check(nb, bot_color):
                                continue
                            all_moves.append(move)

            if not all_moves:
                await send_game_over(room_id, get_opponent_color(bot_color), "Chiếu bí! Bot không còn nước đi.")
                return

            chosen = random.choice(all_moves)
            fx, fy = chosen["from"]["x"], chosen["from"]["y"]
            tx, ty = chosen["to"]["x"], chosen["to"]["y"]
            piece = board[fy][fx]

            apply_move(g.state, chosen)
            idx = g.move_count + 1
            add_move_record(g.game_id, idx, fx, fy, tx, ty, piece)
            g.move_count = idx

            opp = get_opponent_color(bot_color)
            g.turn = opp

            # check king captured
            red_alive = find_king(g.state["board"], 'red')[0] != -1
            black_alive = find_king(g.state["board"], 'black')[0] != -1
            if not red_alive or not black_alive:
                await send_game_over(room_id, 'red' if red_alive else 'black', "Tướng đã bị ăn")
                return

        await send_state(room_id)
        await broadcast_to_room(room_id, {"type": "system", "text": "BOT CHIẾU TƯỚNG!"}
                                ) if is_king_in_check(rooms[room_id].state["board"], opp) else None

    except Exception as e:
        print(f"[BOT] Error: {e}")
        traceback.print_exc()


# -----------------------------------------------------------------------------
# Cleanup / utilities
# -----------------------------------------------------------------------------
async def cleanup_player(ws: WebSocket) -> None:
    async with lock:
        if ws in lobby:
            name = lobby.pop(ws)
            print(f"[CLEANUP] Lobby '{name}' disconnected/left.")
            await send_lobby_update()
            pending_challenges.pop(name, None)
            pending_challenge_targets.pop(name, None)
            return

        if ws in player_room_map:
            room_id = player_room_map.pop(ws)
            if room_id in rooms:
                g = rooms[room_id]
                name = g.players.pop(ws, None)
                if name:
                    color = g.player_colors.get(name)
                    if color in ("red", "black") and g.game_id:
                        winner = get_opponent_color(color)
                        await send_game_over(room_id, winner, f"{name} ({color}) đã ngắt kết nối")
                    else:
                        await broadcast_to_room(room_id, {"type": "system", "text": f"{name} đã rời phòng."}, exclude_ws=ws)

                if not g.players:
                    print(f"[CLEANUP] Delete empty room {room_id}")
                    if g.timer_task:
                        try:
                            g.timer_task.cancel()
                        except Exception:
                            pass
                    del rooms[room_id]

            pending_challenges.pop(name, None)
            pending_challenge_targets.pop(name, None)


def find_player_in_lobby(player_name: str) -> Optional[WebSocket]:
    for ws, name in lobby.items():
        if name == player_name:
            return ws
    return None


def find_ws_by_name(player_name: str) -> Optional[WebSocket]:
    ws = find_player_in_lobby(player_name)
    if ws:
        return ws
    for room in rooms.values():
        for w, n in room.players.items():
            if n == player_name:
                return w
    return None


def get_opponent_ws(room_id: str, self_ws: WebSocket) -> Optional[WebSocket]:
    if room_id not in rooms:
        return None
    for ws in rooms[room_id].players:
        if ws is not self_ws:
            return ws
    return None


# -----------------------------------------------------------------------------
# HTTP
# -----------------------------------------------------------------------------
init_db()

@app.get("/")
async def index():
    return FileResponse("static/client_web.html")

@app.get("/leaderboard")
async def leaderboard():
    rows = db_query_all(
        "SELECT winner, COUNT(*) FROM games "
        "WHERE winner IS NOT NULL AND winner != 'Bot' "
        "GROUP BY winner ORDER BY COUNT(*) DESC"
    )
    return JSONResponse([{"player": r[0], "wins": r[1]} for r in rows])


# -----------------------------------------------------------------------------
# WebSocket
# -----------------------------------------------------------------------------
@app.websocket("/ws")
async def websocket_endpoint(websocket: WebSocket):
    await websocket.accept()
    player_name: Optional[str] = None

    try:
        while True:
            raw = await websocket.receive_text()
            try:
                msg = json.loads(raw)
            except Exception:
                await safe_send(websocket, {"type": "error", "reason": "invalid_json"})
                continue

            mtype = msg.get("type")

            # ---- JOIN LOBBY ----
            if mtype == "join_lobby":
                player_name = msg.get("player") or ("P" + str(int(time.time()) % 1000))
                async with lock:
                    if find_ws_by_name(player_name):
                        player_name = player_name + str(int(time.time()) % 100)
                    lobby[websocket] = player_name
                print(f"[LOBBY] {player_name} joined.")
                await safe_send(websocket, {"type": "system", "text": f"Chào mừng {player_name} đến sảnh."})
                await send_lobby_update()
                continue

            # ---- CHALLENGE ----
            if mtype == "challenge":
                target = msg.get("target_player")
                if not player_name:
                    continue
                if target == player_name:
                    await safe_send(websocket, {"type": "error", "reason": "Bạn không thể tự thách đấu mình."})
                    continue

                # BOT
                if target == "Bot":
                    async with lock:
                        lobby.pop(websocket, None)
                        room_id = str(uuid.uuid4())
                        player_room_map[websocket] = room_id

                        human = player_name
                        bot = "Bot"
                        gid = create_game_record(room_id, human, bot)
                        room = GameRoom(
                            room_id=room_id,
                            players={websocket: human},
                            player_colors={human: 'red', bot: 'black'},
                            turn="red",
                            state=init_board(),
                            game_id=gid,
                        )
                        rooms[room_id] = room
                        room.timer_task = asyncio.create_task(timer_loop(room_id))

                        await safe_send(websocket, {"type": "game_start", "room_id": room_id, "color": "red", "opponent": bot})
                        print(f"[MATCH START] {room_id} {human}(red) vs {bot}(black)")
                        await send_state(room_id)
                    await send_lobby_update()
                    continue

                # HUMAN
                async with lock:
                    target_ws = find_player_in_lobby(target)
                    if not target_ws:
                        await safe_send(websocket, {"type": "error", "reason": f"Không tìm thấy '{target}' trong sảnh."})
                        continue
                    pending_challenges[target] = player_name
                    pending_challenge_targets[player_name] = target
                    try:
                        await safe_send(target_ws, {"type": "challenge_received", "from_player": player_name})
                    except Exception as e:
                        print(f"[CHALLENGE] send fail {target}: {e}")
                        await safe_send(websocket, {"type": "error", "reason": "Không thể gửi lời mời, đối thủ không phản hồi."})
                        pending_challenges.pop(target, None)
                        pending_challenge_targets.pop(player_name, None)
                        continue
                print(f"[CHALLENGE] {player_name} -> {target}")
                await safe_send(websocket, {"type": "system", "text": f"Đã gửi lời mời đến {target}. Đang chờ..."})
                continue

            # ---- ACCEPT ----
            if mtype == "challenge_accept":
                opponent_name = msg.get("opponent_name")
                if not player_name:
                    continue
                async with lock:
                    challenger_ws = find_ws_by_name(opponent_name) or find_player_in_lobby(opponent_name)
                    if not challenger_ws:
                        await safe_send(websocket, {"type": "error", "reason": f"'{opponent_name}' không còn ở sảnh hoặc phiên đã lỗi."})
                        continue

                    # clear pending
                    for k in [player_name, opponent_name]:
                        pending_challenges.pop(k, None)
                        pending_challenge_targets.pop(k, None)

                    lobby.pop(websocket, None)
                    lobby.pop(challenger_ws, None)

                    room_id = str(uuid.uuid4())
                    player_room_map[websocket] = room_id
                    player_room_map[challenger_ws] = room_id

                    challenger_name = opponent_name
                    acceptor_name = player_name
                    gid = create_game_record(room_id, challenger_name, acceptor_name)

                    room = GameRoom(
                        room_id=room_id,
                        players={websocket: acceptor_name, challenger_ws: challenger_name},
                        player_colors={challenger_name: 'red', acceptor_name: 'black'},
                        turn="red",
                        state=init_board(),
                        game_id=gid,
                    )
                    rooms[room_id] = room
                    room.timer_task = asyncio.create_task(timer_loop(room_id))

                    await safe_send(websocket, {"type": "game_start", "room_id": room_id, "color": "black", "opponent": challenger_name})
                    await safe_send(challenger_ws, {"type": "game_start", "room_id": room_id, "color": "red", "opponent": acceptor_name})
                    print(f"[MATCH START] {room_id} {challenger_name}(red) vs {acceptor_name}(black)")
                    await send_state(room_id)
                await send_lobby_update()
                continue

            # ---- DECLINE ----
            if mtype == "challenge_decline":
                opponent_name = msg.get("opponent_name")
                async with lock:
                    challenger_ws = find_ws_by_name(opponent_name)
                    if challenger_ws:
                        await safe_send(challenger_ws, {"type": "system", "text": f"{player_name} đã từ chối lời mời."})
                    pending_challenges.pop(player_name, None)
                    pending_challenge_targets.pop(opponent_name, None)
                continue

            # ---- CHAT ----
            if mtype == "chat_message":
                text = msg.get("text") or ""
                if not player_name or not text.strip():
                    continue
                room_id = player_room_map.get(websocket)
                if not room_id or room_id not in rooms:
                    continue
                await broadcast_to_room(room_id, {"type": "new_chat_message", "from": player_name, "text": text})
                continue

            # ---- MOVE ----
            if mtype == "move":
                move = msg.get("move", {})
                room_id = player_room_map.get(websocket)
                if not room_id or room_id not in rooms:
                    await safe_send(websocket, {"type": "error", "reason": "Bạn không ở trong phòng."})
                    continue

                is_check_alert = False
                is_self_check_alert = False
                is_flying_general_alert = False
                bot_color_to_move: Optional[str] = None

                async with lock:
                    g = rooms[room_id]
                    player = g.players.get(websocket)
                    if not player:
                        continue

                    player_color = g.player_colors.get(player, "spectator")
                    if player_color != g.turn:
                        await safe_send(websocket, {"type": "error", "reason": "Không phải lượt của bạn"})
                        continue

                    if g.game_id is None:
                        await safe_send(websocket, {"type": "error", "reason": "Game đã kết thúc"})
                        continue

                    ok, why = is_valid_move(g.state["board"], move, player_color)
                    if not ok:
                        await safe_send(websocket, {"type": "error", "reason": why})
                        continue

                    fx, fy = move["from"]["x"], move["from"]["y"]
                    piece = g.state["board"][fy][fx]
                    apply_move(g.state, move)

                    if is_flying_general(g.state["board"]):
                        is_flying_general_alert = True
                    if is_king_in_check(g.state["board"], player_color):
                        is_self_check_alert = True

                    opp = get_opponent_color(player_color)
                    if is_king_in_check(g.state["board"], opp):
                        is_check_alert = True

                    idx = g.move_count + 1
                    add_move_record(g.game_id, idx, fx, fy, move["to"]["x"], move["to"]["y"], piece)
                    g.move_count = idx
                    g.turn = opp

                    red_alive = find_king(g.state["board"], 'red')[0] != -1
                    black_alive = find_king(g.state["board"], 'black')[0] != -1
                    if not red_alive or not black_alive:
                        await send_game_over(room_id, 'red' if red_alive else 'black', "Tướng đã bị ăn")
                        continue

                    # bot after user's move
                    names = list(g.player_colors.keys())
                    opponent_name = names[1] if names and names[0] == player else names[0] if names else None
                    if opponent_name == "Bot" and g.game_id and g.turn == g.player_colors["Bot"]:
                        bot_color_to_move = g.turn

                await send_state(room_id)

                if is_flying_general_alert:
                    await safe_send(websocket, {"type": "system", "text": "⚠️ CẢNH BÁO: Lộ tướng!"})
                if is_self_check_alert:
                    await safe_send(websocket, {"type": "system", "text": "⚠️ CẢNH BÁO: Tướng của bạn đang bị chiếu!"})
                if is_check_alert:
                    await broadcast_to_room(room_id, {"type": "system", "text": "CHIẾU TƯỚNG!"})

                if bot_color_to_move:
                    asyncio.create_task(run_bot_move(room_id, bot_color_to_move))
                continue

            # ---- OFFER REMATCH ----
            if mtype == "offer_rematch":
                room_id = player_room_map.get(websocket)
                if not room_id or room_id not in rooms:
                    continue
                async with lock:
                    g = rooms[room_id]
                    if g.game_id is not None:
                        await safe_send(websocket, {"type": "error", "reason": "Game chưa kết thúc"})
                        continue

                    player = g.players.get(websocket)
                    player_names = list(g.player_colors.keys())
                    is_bot_game = "Bot" in player_names

                    if is_bot_game:
                        p1, p2 = player_names
                        gid = create_game_record(room_id, p1, p2)
                        g.state = init_board()
                        g.turn = "red"
                        g.move_count = 0
                        g.game_id = gid
                        g.clocks = {"red": 300, "black": 300}
                        g.rematch_offered_by = None
                        g.timer_task = asyncio.create_task(timer_loop(room_id))
                        await send_state(room_id)
                        await broadcast_to_room(room_id, {"type": "system", "text": "Bot đã đồng ý. Trận đấu mới bắt đầu!"})
                        continue

                    if g.rematch_offered_by and g.rematch_offered_by != player:
                        p1, p2 = player_names
                        gid = create_game_record(room_id, p1, p2)
                        g.state = init_board()
                        g.turn = "red"
                        g.move_count = 0
                        g.game_id = gid
                        g.clocks = {"red": 300, "black": 300}
                        g.rematch_offered_by = None
                        g.timer_task = asyncio.create_task(timer_loop(room_id))
                        await send_state(room_id)
                        await broadcast_to_room(room_id, {"type": "system", "text": "Cả hai đã đồng ý. Trận đấu mới bắt đầu!"})
                    else:
                        g.rematch_offered_by = player
                        opp_ws = get_opponent_ws(room_id, websocket)
                        if opp_ws:
                            await safe_send(opp_ws, {"type": "rematch_offered", "from": player})
                        await safe_send(websocket, {"type": "system", "text": "Đã gửi lời mời chơi lại."})
                continue

            # ---- LEAVE ----
            if mtype == "leave_game":
                room_id = player_room_map.get(websocket)
                if not room_id or room_id not in rooms:
                    async with lock:
                        if websocket not in lobby and player_name:
                            lobby[websocket] = player_name
                            await send_lobby_update()
                    continue

                await cleanup_player(websocket)
                async with lock:
                    if player_name:
                        lobby[websocket] = player_name
                await safe_send(websocket, {"type": "system", "text": "Đã quay về sảnh."})
                await send_lobby_update()
                continue

            # ---- unknown ----
            await safe_send(websocket, {"type": "error", "reason": "unknown_message_type"})

    except WebSocketDisconnect:
        print(f"[WS] Disconnect: {player_name}")
        await cleanup_player(websocket)
    except Exception as e:
        print(f"[WS] Exception for {player_name}: {e}")
        traceback.print_exc()
        await cleanup_player(websocket)
