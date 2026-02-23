import asyncio
import sys
import os
import subprocess
import threading
import tkinter as tk
from tkinter import filedialog
from tkinter import ttk
from tkinterdnd2 import DND_FILES, TkinterDnD
import socket
import json
import webbrowser
import time
import pystray
import zipfile
import tempfile
import fcntl
import wave
import struct
import math
import io
import websockets
import numpy as np
import sounddevice as sd
from PIL import Image, ImageDraw

# =========================
# CONFIG
# =========================

# =========================
# SINGLE INSTANCE CHECK
# =========================

_lock_file = open("/tmp/localbridge.lock", "w")
try:
    fcntl.flock(_lock_file, fcntl.LOCK_EX | fcntl.LOCK_NB)
except IOError:
    import tkinter as _tk
    _r = _tk.Tk()
    _r.withdraw()
    _tk.messagebox.showinfo("LocalBridge", "LocalBridge is already running.\nCheck the system tray.")
    _r.destroy()
    sys.exit(0)

# Base directory — always next to the exe or script
if getattr(sys, "frozen", False):
    BASE_DIR = os.path.dirname(sys.executable)
else:
    BASE_DIR = os.path.dirname(os.path.abspath(__file__))

CONFIG_FILE = os.path.join(BASE_DIR, "config.json")
DEFAULT_CONFIG = {
    "port": 8765,
    "received_folder": "Received",
    "sound": "beep",
    "notifications": True
}

def load_config():
    if os.path.exists(CONFIG_FILE):
        try:
            with open(CONFIG_FILE, "r") as f:
                data = json.load(f)
                for key, val in DEFAULT_CONFIG.items():
                    if key not in data:
                        data[key] = val
                return data
        except Exception:
            pass
    return DEFAULT_CONFIG.copy()

def save_config(config):
    try:
        with open(CONFIG_FILE, "w") as f:
            json.dump(config, f, indent=2)
    except Exception as e:
        print("Config save error:", e)

config = load_config()

def generate_beep_wav(frequency=1000, duration_ms=200, volume=0.5, sample_rate=44100):
    """Generate a beep as in-memory WAV bytes."""
    num_samples = int(sample_rate * duration_ms / 1000)
    buf = io.BytesIO()
    with wave.open(buf, 'wb') as w:
        w.setnchannels(1)
        w.setsampwidth(2)
        w.setframerate(sample_rate)
        for i in range(num_samples):
            t = i / sample_rate
            fade = min(i, num_samples - i, int(sample_rate * 0.01))
            fade = min(fade / (sample_rate * 0.01), 1.0)
            sample = int(32767 * volume * fade * math.sin(2 * math.pi * frequency * t))
            w.writeframes(struct.pack('<h', sample))
    return buf.getvalue()

def _play_wav_bytes(wav_bytes):
    """Play WAV bytes via sounddevice."""
    try:
        buf = io.BytesIO(wav_bytes)
        with wave.open(buf, 'rb') as w:
            sample_rate = w.getframerate()
            frames = w.readframes(w.getnframes())
        samples = np.frombuffer(frames, dtype=np.int16).astype(np.float32) / 32767.0
        sd.play(samples, samplerate=sample_rate)
        sd.wait()
    except Exception as e:
        print("Sound error:", e)

def play_notification_sound():
    sound = config.get("sound", "beep")
    if sound == "beep":
        def _play():
            wav = generate_beep_wav(frequency=1000, duration_ms=200)
            _play_wav_bytes(wav)
        threading.Thread(target=_play, daemon=True).start()
    elif sound == "beep_double":
        def _play():
            wav = generate_beep_wav(frequency=1000, duration_ms=150)
            _play_wav_bytes(wav)
            time.sleep(0.08)
            _play_wav_bytes(wav)
        threading.Thread(target=_play, daemon=True).start()
    # "none" → do nothing

PORT = config["port"]
_rf = config["received_folder"]
RECEIVED_FOLDER = _rf if os.path.isabs(_rf) else os.path.join(BASE_DIR, _rf)
DISCOVERY_PORT = 8766

# PC-to-PC client state
pc_client_ws = None
pc_client_loop = asyncio.new_event_loop()
pc_client_connected = False
pc_target_ip = ""
pc_target_port = 8765
pc_status_var = None  # set after tk init
pc_send_queue = None  # created inside pc_client_loop

# client_id -> {"ws": websocket, "name": str}
connected_clients = {}
client_id_counter = 0
id_lock = threading.Lock()
clients_lock = threading.Lock()

server_loop = asyncio.new_event_loop()

# =========================
# THEME
# =========================

BG_COLOR = "#1e1e1e"
CARD_COLOR = "#2b2b2b"
ACCENT = "#4cc2ff"
TEXT = "#ffffff"
MUTED = "#aaaaaa"
GREEN = "#3CFF5E"
RED = "#ff4c4c"

connected_state = False
pulse_state = True

status_var = None
status_dot = None
progress_bar = None
peers_frame = None

transfer_cards = []

# =========================
# CLIPBOARD SYNC
# =========================

clipboard_pc_text = ""
clipboard_debounce_id = None
_clipboard_receiving = False  # prevent echo when updating from remote

def broadcast_clipboard(text, source="pc", source_ws=None):
    """Send clipboard text to all connected clients except source."""
    msg = json.dumps({"type": "clipboard", "text": text, "source": source})

    async def _send():
        for info in list(connected_clients.values()):
            if info["ws"] is source_ws:
                continue
            try:
                await info["ws"].send(msg)
            except Exception:
                pass
        if pc_client_ws is not None and pc_client_ws is not source_ws:
            try:
                await pc_client_ws.send(msg)
            except Exception:
                pass

    asyncio.run_coroutine_threadsafe(_send(), server_loop)

def on_clipboard_android_update(text):
    """Called when Android sends clipboard — updates Android box in main thread."""
    def _update():
        try:
            clipboard_android_box.config(state="normal")
            clipboard_android_box.delete("1.0", tk.END)
            clipboard_android_box.insert("1.0", text)
            clipboard_android_box.config(state="disabled")
        except Exception:
            pass
    root.after(0, _update)

def on_clipboard_remote_update(text):
    """Called from PC client (remote PC sent clipboard) — updates Android box."""
    on_clipboard_android_update(text)

# =========================
# PEERS UI
# =========================

peer_widgets = {}  # client_id -> {"frame": tk.Frame, "label": tk.Label}

def update_peers_ui():
    """Refresh the connected peers list in the UI."""
    if peers_frame is None:
        return

    def _update():
        for widget in peer_widgets.values():
            try:
                widget["frame"].destroy()
            except Exception:
                pass
        peer_widgets.clear()

        for cid, info in list(connected_clients.items()):
            # Android only in Server tab peers list
            if info.get("device_type") == "pc":
                continue
            frame = tk.Frame(peers_frame, bg=BG_COLOR)
            frame.pack(side="left", padx=4, pady=2)

            label = tk.Label(
                frame,
                text=info["name"],
                fg=TEXT,
                bg=BG_COLOR,
                font=("Segoe UI", 9)
            )
            label.pack()

            peer_widgets[cid] = {"frame": frame, "label": label}

    root.after(0, _update)

async def broadcast_peers():
    """Send updated peer list to all connected clients."""
    peers = [{"id": cid, "name": info["name"]} for cid, info in connected_clients.items()]
    msg = json.dumps({"type": "peers", "devices": peers})
    for info in list(connected_clients.values()):
        try:
            await info["ws"].send(msg)
        except Exception:
            pass

async def broadcast_clipboard_async(text, source="pc", source_ws=None):
    """Send clipboard update to all connected clients except source, and to PC client."""
    msg = json.dumps({"type": "clipboard", "text": text, "source": source})
    for info in list(connected_clients.values()):
        if info["ws"] is source_ws:
            continue
        try:
            await info["ws"].send(msg)
        except Exception:
            pass
    if pc_client_ws is not None and pc_client_ws is not source_ws:
        try:
            await pc_client_ws.send(msg)
        except Exception:
            pass

# =========================
# UDP DISCOVERY
# =========================

def get_local_ip():
    candidates = []
    try:
        # Get all IPs from all interfaces
        hostname = socket.gethostname()
        infos = socket.getaddrinfo(hostname, None)
        for info in infos:
            ip = info[4][0]
            if ":" in ip:  # skip IPv6
                continue
            if ip.startswith("127.") or ip.startswith("169.254"):
                continue
            candidates.append(ip)
    except Exception:
        pass

    # Try connecting to gateway to find best interface
    for gateway in ("192.168.202.1", "192.168.1.1", "192.168.0.1", "10.0.0.1"):
        try:
            s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            s.connect((gateway, 80))
            ip = s.getsockname()[0]
            s.close()
            if not ip.startswith("127.") and not ip.startswith("169.254"):
                return ip
        except Exception:
            continue

    # Return first non-virtual candidate
    for ip in candidates:
        if not ip.startswith("192.168.56.") and not ip.startswith("10.0.75."):
            return ip

    return candidates[0] if candidates else "127.0.0.1"

def udp_discovery_server():
    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    try:
        sock.bind(("0.0.0.0", DISCOVERY_PORT))
        print(f"UDP discovery listening on port {DISCOVERY_PORT}")
        while True:
            try:
                data, addr = sock.recvfrom(1024)
                if data == b"LOCALBRIDGE_DISCOVER":
                    pass
                else:
                    try:
                        parsed = json.loads(data.decode())
                        if parsed.get("type") not in ("discover", "LOCALBRIDGE_DISCOVER"):
                            continue
                    except Exception:
                        continue

                # Ignore requests from ourselves
                if addr[0] == local_ip:
                    continue

                hostname = socket.gethostname()
                response = json.dumps({
                    "type": "pc",
                    "hostname": hostname,
                    "ip": local_ip,
                    "port": PORT
                }).encode()
                sock.sendto(response, addr)
            except Exception as e:
                print("UDP discovery error:", e)
    except Exception as e:
        print("UDP discovery bind error:", e)
    finally:
        sock.close()

# =========================
# TRANSFER CARD
# =========================

class ProxyTransferCard:
    """Thread-safe proxy — delegates all UI ops to main thread via root.after."""

    def __init__(self, parent, label, on_abort=None, file_path=None, status="Uploading"):
        self._card = None
        self._aborted = False
        self.on_abort = on_abort

        def _create():
            self._card = TransferCard(parent, label, on_abort=on_abort, file_path=file_path, status=status)
        root.after(0, _create)

    @property
    def aborted(self):
        return self._aborted

    @aborted.setter
    def aborted(self, val):
        self._aborted = val
        if self._card:
            self._card.aborted = val

    def update(self, done, total):
        root.after(0, lambda d=done, t=total: self._card and self._card.update(d, t))

    def finish(self, message="Completed", show_open=False):
        root.after(0, lambda m=message, s=show_open: self._card and self._card.finish(m, s))

    def destroy(self):
        root.after(0, lambda: self._card and self._card.destroy())


class TransferCard:

    def __init__(self, parent, filename, on_abort=None, file_path=None, status="Uploading"):
        self.start_time = time.time()
        self.aborted = False
        self.on_abort = on_abort
        self.file_path = file_path

        self.frame = tk.Frame(parent, bg=CARD_COLOR)
        self.frame.pack(fill="x", pady=6, padx=15)

        top_row = tk.Frame(self.frame, bg=CARD_COLOR)
        top_row.pack(fill="x")

        self.name_label = tk.Label(
            top_row, text=filename, fg=TEXT, bg=CARD_COLOR,
            font=("Segoe UI", 10, "bold")
        )
        self.name_label.pack(side="left", anchor="w")

        self.status_label = tk.Label(
            top_row, text=status, fg=ACCENT, bg=CARD_COLOR,
            font=("Segoe UI", 8, "bold")
        )
        self.status_label.pack(side="left", padx=6)

        self.abort_button = tk.Button(
            top_row, text="Abort", command=self._abort,
            bg=RED, fg="white", relief="flat", font=("Segoe UI", 8), padx=6
        )
        self.abort_button.pack(side="right", padx=4, pady=2)

        self.open_button = tk.Button(
            top_row, text="Open", command=self._open_location,
            bg="#555", fg="white", relief="flat", font=("Segoe UI", 8), padx=6
        )

        self.progress_var = tk.IntVar(value=0)
        self.progress = ttk.Progressbar(
            self.frame, orient="horizontal",
            variable=self.progress_var, maximum=100
        )
        self.progress.pack(fill="x", pady=3)

        self.info_var = tk.StringVar(value="Starting...")
        self.info_label = tk.Label(
            self.frame, textvariable=self.info_var,
            fg=MUTED, bg=CARD_COLOR, font=("Segoe UI", 8)
        )
        self.info_label.pack(anchor="w")

        transfer_cards.append(self)
        # Keep max 50 cards
        if len(transfer_cards) > 50:
            oldest = transfer_cards.pop(0)
            try:
                oldest.frame.destroy()
            except Exception:
                pass

    def _open_location(self):
        if self.file_path and os.path.exists(self.file_path):
            folder = os.path.dirname(self.file_path)
            subprocess.Popen(["open", folder])

    def _abort(self):
        self.aborted = True
        if self.abort_button.winfo_exists():
            self.abort_button.destroy()
        self.info_var.set("Aborted")
        if self.on_abort:
            self.on_abort()

    def update(self, done, total):
        if self.aborted:
            return
        percent = int((done / total) * 100)
        self.progress_var.set(percent)
        elapsed = time.time() - self.start_time
        speed = done / elapsed if elapsed > 0 else 0
        eta = (total - done) / speed if speed > 0 else 0
        self.info_var.set(f"{percent}% | {speed/1024/1024:.2f} MB/s | ETA {int(eta)}s")

    def finish(self, message="Completed", show_open=False):
        self.progress_var.set(100)
        self.info_var.set(message)
        try:
            if self.abort_button.winfo_exists():
                self.abort_button.destroy()
        except Exception:
            pass
        try:
            self.status_label.destroy()
        except Exception:
            pass
        if show_open and self.file_path:
            self.open_button.pack(side="right", padx=4, pady=2)

    def destroy(self):
        try:
            self.frame.destroy()
        except Exception:
            pass

# =========================
# SERVER
# =========================

async def handler(websocket):
    global client_id_counter

    client_ip = websocket.remote_address[0]

    existing_id = next((cid for cid, info in connected_clients.items() if info.get("ip") == client_ip), None)
    if existing_id is not None:
        my_id = existing_id
    else:
        with id_lock:
            client_id_counter += 1
            my_id = client_id_counter

    connected_clients[my_id] = {"ws": websocket, "name": connected_clients.get(my_id, {}).get("name", f"Android {my_id}"), "ip": client_ip, "device_type": "android"}
    update_peers_ui()
    await broadcast_peers()

    print(f"Device connected (id={my_id})")
    update_status("Connected", True)

    current_transfer = None
    receive_total = 0
    receive_expected = 0
    file = None
    file_path = None
    forward_target = None
    is_pc_client = False  # set to True when hello with device_type=pc received

    def make_transfer_card(parent, label, on_abort=None, file_path=None, status="Downloading"):
        """Non-blocking proxy TransferCard — all UI calls via root.after."""
        proxy = ProxyTransferCard(parent, label, on_abort=on_abort, file_path=file_path, status=status)
        root.after(0, lambda p=proxy: transfer_cards.append(p))
        return proxy

    def get_card_parent():
        return pc_scrollable_frame if is_pc_client else scrollable_frame

    try:
        async for message in websocket:

            if isinstance(message, str):
                data = json.loads(message)
                msg_type = data.get("type", "")

                # — Hello —
                if msg_type == "hello":
                    name = data.get("name", f"Android {my_id}")
                    if data.get("device_type") == "pc":
                        is_pc_client = True
                        connected_clients[my_id]["device_type"] = "pc"
                    else:
                        name = f"📱 {name}" if not name.startswith("📱") else name
                    connected_clients[my_id]["name"] = name
                    update_peers_ui()
                    await broadcast_peers()
                    continue

                # — Clipboard —
                if msg_type == "clipboard":
                    text = data.get("text", "")
                    source = data.get("source", "android")
                    if source == "android":
                        on_clipboard_android_update(text)
                    await broadcast_clipboard_async(text, source=source, source_ws=websocket)
                    continue

                if data.get("direction") == "android_to_pc":
                    current_transfer = None
                    receive_total = 0
                    if file and not file.closed:
                        file.close()
                    file = None
                    file_path = None
                    forward_target = None

                    filename = data["filename"]
                    receive_expected = data["filesize"]
                    target_id = data.get("target_id")

                    # Check if forwarding to another Android
                    if target_id is not None and target_id in connected_clients:
                        forward_target = target_id
                        fwd_meta = json.dumps({
                            "direction": "pc_to_android",
                            "filename": filename,
                            "filesize": receive_expected
                        })
                        try:
                            await connected_clients[target_id]["ws"].send(fwd_meta)
                        except Exception:
                            pass
                        current_transfer = make_transfer_card(
                            get_card_parent(),
                            f"{filename} → {connected_clients[target_id]['name']}",
                            status="Forwarding"
                        )
                    else:
                        receive_total = 0
                        os.makedirs(RECEIVED_FOLDER, exist_ok=True)
                        file_path = os.path.join(RECEIVED_FOLDER, filename)
                        file = open(file_path, "wb")
                        captured_path = os.path.abspath(file_path)

                        def make_abort_callback(path_ref):
                            def on_abort():
                                try:
                                    if file and not file.closed:
                                        file.close()
                                except Exception:
                                    pass
                                try:
                                    if path_ref and os.path.exists(path_ref):
                                        os.remove(path_ref)
                                except Exception:
                                    pass
                            return on_abort

                        current_transfer = make_transfer_card(
                            get_card_parent(), filename,
                            on_abort=make_abort_callback(captured_path),
                            file_path=captured_path,
                            status="Downloading"
                        )

            else:
                if current_transfer and current_transfer.aborted:
                    continue

                if forward_target is not None:
                    target_info = connected_clients.get(forward_target)
                    if target_info:
                        try:
                            await target_info["ws"].send(message)
                        except Exception:
                            pass
                    receive_total += len(message)
                    if current_transfer:
                        root.after(0, lambda d=receive_total, t=receive_expected: current_transfer.update(d, t))
                    if receive_total >= receive_expected:
                        if current_transfer:
                            _ct2 = current_transfer
                            root.after(0, lambda ct=_ct2: ct and ct.finish("Forwarded"))
                        current_transfer = None
                        forward_target = None

                elif file:
                    if current_transfer and current_transfer.aborted:
                        try:
                            if not file.closed:
                                file.close()
                        except Exception:
                            pass
                        try:
                            if file_path and os.path.exists(file_path):
                                os.remove(file_path)
                        except Exception:
                            pass
                        current_transfer = None
                        file = None
                        continue

                    file.write(message)
                    receive_total += len(message)
                    root.after(0, lambda d=receive_total, t=receive_expected: current_transfer and current_transfer.update(d, t))

                    if receive_total >= receive_expected:
                        file.close()
                        root.after(0, lambda fn=filename: tray_notify("File received", fn))
                        play_notification_sound()
                        _ct = current_transfer
                        root.after(0, lambda ct=_ct: ct and ct.finish("Downloaded", show_open=True))
                        current_transfer = None
                        file = None
                        try:
                            await websocket.send(json.dumps({
                                "type": "done",
                                "filename": filename
                            }))
                        except Exception:
                            pass

    except Exception as e:
        print(f"Android {my_id} disconnected:", e)

    finally:
        if file and not file.closed:
            file.close()
        connected_clients.pop(my_id, None)
        update_peers_ui()
        await broadcast_peers()
        if not connected_clients:
            update_status("Disconnected", False)

async def start_server():
    async with websockets.serve(
        handler, "0.0.0.0", PORT,
        ping_interval=20, ping_timeout=20, max_size=None
    ):
        print(f"Server started on port {PORT}")
        await asyncio.Future()

def run_server():
    asyncio.set_event_loop(server_loop)
    server_loop.run_until_complete(start_server())

# =========================
# WATCHDOG
# =========================

server_thread = None

def start_server_thread():
    global server_thread
    server_thread = threading.Thread(target=run_server, daemon=True)
    server_thread.start()

def watchdog():
    while True:
        time.sleep(5)
        if server_thread and not server_thread.is_alive():
            print("Watchdog: server thread died, restarting...")
            root.after(0, lambda: update_status("Restarting server...", False))
            start_server_thread()
            time.sleep(2)

# =========================
# PC → ANDROID
# =========================

async def send_file_async(filepath, target_id=None):
    """Send file to all Androids or to specific one if target_id given."""
    android_clients = {k: v for k, v in connected_clients.items() if v.get("device_type") != "pc"}
    if not android_clients:
        return

    if target_id is not None:
        targets = {target_id: android_clients[target_id]} if target_id in android_clients else {}
    else:
        targets = android_clients

    if not targets:
        return

    filesize = os.path.getsize(filepath)
    filename = os.path.basename(filepath)

    metadata = json.dumps({
        "direction": "pc_to_android",
        "filename": filename,
        "filesize": filesize
    })

    for cid, info in list(targets.items()):
        ws = info["ws"]
        client_name = info["name"]
        label = filename if len(targets) == 1 else f"{filename} → {client_name}"
        transfer = ProxyTransferCard(scrollable_frame, label, status="Uploading")

        await ws.send(metadata)
        sent = 0

        with open(filepath, "rb") as f:
            while True:
                if transfer.aborted:
                    try:
                        await ws.send(json.dumps({"type": "aborted", "filename": filename}))
                    except Exception:
                        pass
                    break

                chunk = f.read(16384)
                if not chunk:
                    break

                await ws.send(chunk)
                sent += len(chunk)
                transfer.update(sent, filesize)
                await asyncio.sleep(0)

        if not transfer.aborted:
            transfer.finish("Sent")

def send_file(filepath, target_id=None):
    asyncio.run_coroutine_threadsafe(send_file_async(filepath, target_id), server_loop)

def ask_target_device(android_clients: dict):
    """Show popup to pick one device. Returns client_id or None if cancelled."""
    result = [None]
    win = tk.Toplevel(root)
    win.title("Select Device")
    win.configure(bg=BG_COLOR)
    win.resizable(False, False)
    win.grab_set()
    win.lift()

    tk.Label(win, text="Send to which device?",
             fg=TEXT, bg=BG_COLOR, font=("Segoe UI", 11, "bold")).pack(pady=(14, 8), padx=20)

    for cid, info in android_clients.items():
        def _pick(c=cid):
            result[0] = c
            win.destroy()
        tk.Button(win, text=info["name"], command=_pick,
                  bg=CARD_COLOR, fg=TEXT, relief="flat",
                  font=("Segoe UI", 10), width=24, pady=6).pack(padx=20, pady=3)

    tk.Button(win, text="Send to All", command=lambda: [result.__setitem__(0, "all"), win.destroy()],
              bg=ACCENT, fg="black", relief="flat",
              font=("Segoe UI", 10), width=24, pady=6).pack(padx=20, pady=(6, 4))

    tk.Button(win, text="Cancel", command=win.destroy,
              bg="#444", fg=TEXT, relief="flat",
              font=("Segoe UI", 9), width=24).pack(padx=20, pady=(0, 12))

    root.wait_window(win)
    r = result[0]
    if r == "all":
        return None  # None = send to all
    return r

def zip_and_send_folder(folderpath, target_id=None):
    """Zip folder in background thread then send."""
    def _zip():
        folder_name = os.path.basename(folderpath.rstrip("/\\"))
        with tempfile.NamedTemporaryFile(delete=False, suffix=".zip", prefix=f"{folder_name}_") as tf:
            tmp = tf.name
        try:
            with zipfile.ZipFile(tmp, "w", zipfile.ZIP_DEFLATED) as zf:
                for root_dir, dirs, files in os.walk(folderpath):
                    for file in files:
                        abs_path = os.path.join(root_dir, file)
                        arc_name = os.path.relpath(abs_path, os.path.dirname(folderpath))
                        zf.write(abs_path, arc_name)
            send_file(tmp, target_id=target_id)
        except Exception as e:
            print("Zip error:", e)
        finally:
            try:
                os.remove(tmp)
            except Exception:
                pass
    threading.Thread(target=_zip, daemon=True).start()

# =========================
# PC CLIENT (PC → PC)
# =========================

def pc_client_send(filepath):
    if pc_client_connected and pc_send_queue is not None:
        asyncio.run_coroutine_threadsafe(pc_send_queue.put(filepath), pc_client_loop)

async def pc_connect_async(ip, port):
    global pc_client_ws, pc_client_connected
    uri = f"ws://{ip}:{port}"

    pc_recv_transfer = None
    pc_recv_expected = 0
    pc_recv_total = 0
    pc_recv_file = None
    pc_recv_path = None

    async def _sender(ws):
        """Reads from queue and sends files one by one."""
        while True:
            filepath = await pc_send_queue.get()
            print(f"[PC] Sending: {filepath}")
            if filepath is None:
                break
            try:
                filesize = os.path.getsize(filepath)
                filename = os.path.basename(filepath)
                transfer = ProxyTransferCard(pc_scrollable_frame, f"{filename} → PC", status="Uploading")
                root.after(0, lambda t=transfer: pc_transfer_cards.append(t))
                print(f"[PC] Sending metadata for {filename} size={filesize}")
                await ws.send(json.dumps({
                    "direction": "android_to_pc",
                    "filename": filename,
                    "filesize": filesize
                }))
                print(f"[PC] Metadata sent, starting chunks")
                sent = 0
                with open(filepath, "rb") as f:
                    while True:
                        if transfer.aborted:
                            break
                        chunk = f.read(16384)
                        if not chunk:
                            break
                        await ws.send(chunk)
                        sent += len(chunk)
                        transfer.update(sent, filesize)
                        await asyncio.sleep(0)
                if not transfer.aborted:
                    transfer.finish("Sent")
            except Exception as e:
                import traceback
                print("PC send error:", e)
                traceback.print_exc()

    sender_task = None
    try:
        async with websockets.connect(uri, ping_interval=20, ping_timeout=60) as ws:
            pc_client_ws = ws
            pc_client_connected = True
            root.after(0, lambda: pc_status_var.set(f"Connected to {ip}"))
            root.after(0, lambda: pc_connect_dot.config(fg=GREEN))
            root.after(0, lambda: pc_disconnect_btn.pack(side="left", padx=(0,6)))
            root.after(0, lambda: pc_connect_btn.pack_forget())
            await ws.send(json.dumps({"type": "hello", "name": f"🖥 {socket.gethostname()}", "device_type": "pc"}))

            def _on_task_done(t):
                if t.cancelled():
                    print("[PC] Sender task cancelled")
                elif t.exception():
                    import traceback
                    print("[PC] Sender task exception:")
                    traceback.print_exception(type(t.exception()), t.exception(), t.exception().__traceback__)
                else:
                    print("[PC] Sender task done normally")
            sender_task = asyncio.create_task(_sender(ws))
            sender_task.add_done_callback(_on_task_done)
            print("[PC] Sender task created")

            async for message in ws:
                if isinstance(message, str):
                    try:
                        data = json.loads(message)
                        if data.get("type") == "clipboard":
                            text = data.get("text", "")
                            source = data.get("source", "pc")
                            on_clipboard_remote_update(text)
                            broadcast_clipboard(text, source=source, source_ws=ws)
                        elif data.get("direction") == "pc_to_android":
                            filename = data["filename"]
                            pc_recv_expected = data["filesize"]
                            pc_recv_total = 0
                            os.makedirs(RECEIVED_FOLDER, exist_ok=True)
                            pc_recv_path = os.path.join(RECEIVED_FOLDER, filename)
                            pc_recv_file = open(pc_recv_path, "wb")
                            captured = os.path.abspath(pc_recv_path)
                            pc_recv_transfer = ProxyTransferCard(
                                pc_scrollable_frame, f"← {filename}",
                                file_path=captured, status="Downloading"
                            )
                            root.after(0, lambda t=pc_recv_transfer: pc_transfer_cards.append(t))
                    except Exception:
                        pass
                else:
                    if pc_recv_file and pc_recv_transfer:
                        pc_recv_file.write(message)
                        pc_recv_total += len(message)
                        t = pc_recv_transfer
                        d, total = pc_recv_total, pc_recv_expected
                        root.after(0, lambda d=d, total=total: t.update(d, total))
                        if pc_recv_total >= pc_recv_expected:
                            pc_recv_file.close()
                            pc_recv_file = None
                            captured = os.path.abspath(pc_recv_path)
                            root.after(0, lambda: t.finish("Received", show_open=True))
                            root.after(0, lambda fn=os.path.basename(pc_recv_path): tray_notify("File received from PC", fn))
                            play_notification_sound()
                            pc_recv_transfer = None
    except Exception as e:
        print("PC client error:", e)
    finally:
        if sender_task is not None:
            try:
                sender_task.cancel()
            except Exception:
                pass
        pc_client_ws = None
        pc_client_connected = False
        root.after(0, lambda: pc_status_var.set("Not connected"))
        root.after(0, lambda: pc_connect_dot.config(fg=RED))
        root.after(0, lambda: pc_disconnect_btn.pack_forget())
        root.after(0, lambda: pc_connect_btn.pack(side="left", padx=(0,6)))

pc_should_reconnect = False
pc_reconnect_ip = ""
pc_reconnect_port = 8765

def pc_connect(ip, port):
    global pc_should_reconnect, pc_reconnect_ip, pc_reconnect_port
    if pc_client_connected:
        return  # already connected
    pc_should_reconnect = True
    pc_reconnect_ip = ip
    pc_reconnect_port = port

    async def _reconnect_loop():
        global pc_send_queue
        pc_send_queue = asyncio.Queue()
        while pc_should_reconnect:
            await pc_connect_async(ip, port)
            if pc_should_reconnect:
                root.after(0, lambda: pc_status_var.set("Reconnecting..."))
                await asyncio.sleep(3)

    def _run():
        asyncio.set_event_loop(pc_client_loop)
        pc_client_loop.run_until_complete(_reconnect_loop())

    threading.Thread(target=_run, daemon=True).start()

def pc_disconnect():
    global pc_should_reconnect
    pc_should_reconnect = False
    if pc_client_ws is not None:
        asyncio.run_coroutine_threadsafe(pc_client_ws.close(), pc_client_loop)
def scan_for_pcs(callback=None):
    def _scan():
        found = []
        seen_ips = set()
        try:
            print(f"[SCAN] Starting, local_ip={local_ip}")
            sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            sock.setsockopt(socket.SOL_SOCKET, socket.SO_BROADCAST, 1)
            sock.settimeout(3)
            # Bind to local IP so broadcast goes through correct interface
            sock.bind((local_ip, 0))
            # Send broadcast 3 times to increase reliability
            for _ in range(3):
                sock.sendto(b"LOCALBRIDGE_DISCOVER", ("255.255.255.255", DISCOVERY_PORT))
                time.sleep(0.2)
            print(f"[SCAN] Broadcast sent to 255.255.255.255:{DISCOVERY_PORT} via {local_ip}")
            end = time.time() + 3.0
            while time.time() < end:
                try:
                    data, addr = sock.recvfrom(1024)
                    print(f"[SCAN] Received from {addr}: {data[:80]}")
                    parsed = json.loads(data.decode())
                    ip = parsed.get("ip", "")
                    if ip and ip != local_ip and ip not in seen_ips:
                        seen_ips.add(ip)
                        found.append(parsed)
                        print(f"[SCAN] Added: {ip}")
                    else:
                        print(f"[SCAN] Skipped: {ip} (local={local_ip})")
                except socket.timeout:
                    continue
                except Exception as ex:
                    print(f"[SCAN] Error: {ex}")
                    continue
            sock.close()
        except Exception as e:
            print(f"[SCAN] Fatal error: {e}")
        print(f"[SCAN] Done. Found: {found}")
        if callback:
            root.after(0, lambda: callback(found))
        else:
            root.after(0, lambda: populate_scan_dropdown(found))
    threading.Thread(target=_scan, daemon=True).start()

def populate_scan_dropdown(devices):
    pc_scan_menu.delete(0, "end")
    if not devices:
        pc_scan_menu.add_command(label="No devices found", state="disabled")
    else:
        for d in devices:
            label = f"🖥 {d.get('hostname', d['ip'])} — {d['ip']}:{d['port']}"
            def make_cmd(ip, port):
                def cmd():
                    pc_ip_var.set(ip)
                    pc_port_var.set(str(port))
                return cmd
            pc_scan_menu.add_command(label=label, command=make_cmd(d["ip"], d["port"]))
    try:
        x = pc_scan_btn.winfo_rootx()
        y = pc_scan_btn.winfo_rooty() + pc_scan_btn.winfo_height()
        pc_scan_menu.tk_popup(x, y)
    except Exception:
        pass

# =========================
# GUI HELPERS
# =========================

_last_drop_time = 0
_last_drop_file = ""

def copy_ip():
    root.clipboard_clear()
    root.clipboard_append(local_ip)

def open_received_folder():
    folder = os.path.abspath(RECEIVED_FOLDER)
    os.makedirs(folder, exist_ok=True)
    subprocess.Popen(["open", folder])

def update_status(text, connected=False):
    root.after(0, lambda: _update_status_ui(text, connected))

def _update_status_ui(text, connected):
    global connected_state
    connected_state = connected
    status_var.set(text)
    if not connected:
        progress_bar.configure(mode="indeterminate")
        progress_bar.start(10)
    else:
        progress_bar.stop()
    update_dot()

def update_dot():
    global pulse_state
    if connected_state:
        color = GREEN if pulse_state else BG_COLOR
        status_dot.config(fg=color)
        pulse_state = not pulse_state
        root.after(600, update_dot)
    else:
        status_dot.config(fg=RED)

def open_site():
    webbrowser.open("https://jonasz-o.itch.io/")

def clear_transfers():
    for card in list(transfer_cards):
        try:
            card.destroy()
        except Exception:
            pass
    transfer_cards.clear()
    canvas.yview_moveto(0)
    canvas.configure(scrollregion=(0,0,0,0))

def open_settings():
    win = tk.Toplevel(root)
    win.title("Settings")
    win.configure(bg=BG_COLOR)
    win.resizable(False, False)
    win.grab_set()

    w, h = 420, 320
    root.update_idletasks()
    rx = root.winfo_x() + (root.winfo_width() - w) // 2
    ry = root.winfo_y() + (root.winfo_height() - h) // 2
    win.geometry(f"{w}x{h}+{rx}+{ry}")

    tk.Label(win, text="Settings", font=("Segoe UI", 13, "bold"),
             fg=TEXT, bg=BG_COLOR).pack(pady=(15, 10))

    row1 = tk.Frame(win, bg=BG_COLOR)
    row1.pack(fill="x", padx=20, pady=4)
    tk.Label(row1, text="Port:", fg=TEXT, bg=BG_COLOR,
             font=("Segoe UI", 10), width=16, anchor="w").pack(side="left")
    port_var = tk.StringVar(value=str(config["port"]))
    tk.Entry(row1, textvariable=port_var, bg=CARD_COLOR, fg=TEXT,
             insertbackground=TEXT, relief="flat", width=20).pack(side="left")

    row2 = tk.Frame(win, bg=BG_COLOR)
    row2.pack(fill="x", padx=20, pady=4)
    tk.Label(row2, text="Received folder:", fg=TEXT, bg=BG_COLOR,
             font=("Segoe UI", 10), width=16, anchor="w").pack(side="left")
    folder_var = tk.StringVar(value=config["received_folder"])
    tk.Entry(row2, textvariable=folder_var, bg=CARD_COLOR, fg=TEXT,
             insertbackground=TEXT, relief="flat", width=20).pack(side="left")

    row3 = tk.Frame(win, bg=BG_COLOR)
    row3.pack(fill="x", padx=20, pady=4)
    tk.Label(row3, text="Notification sound:", fg=TEXT, bg=BG_COLOR,
             font=("Segoe UI", 10), width=16, anchor="w").pack(side="left")
    sound_options = ["beep", "beep_double", "none"]
    sound_var = tk.StringVar(value=config.get("sound", "beep"))
    sound_combo = ttk.Combobox(row3, textvariable=sound_var, values=sound_options,
                                state="readonly", width=18)
    sound_combo.pack(side="left")

    row4 = tk.Frame(win, bg=BG_COLOR)
    row4.pack(fill="x", padx=20, pady=4)
    tk.Label(row4, text="Notifications:", fg=TEXT, bg=BG_COLOR,
             font=("Segoe UI", 10), width=16, anchor="w").pack(side="left")
    notifications_var = tk.BooleanVar(value=config.get("notifications", True))
    tk.Checkbutton(row4, variable=notifications_var, bg=BG_COLOR,
                   activebackground=BG_COLOR, selectcolor=CARD_COLOR).pack(side="left")

    def save():
        try:
            config["port"] = int(port_var.get())
        except ValueError:
            pass
        folder_input = folder_var.get().strip() or "Received"
        config["received_folder"] = folder_input
        config["sound"] = sound_var.get()
        config["notifications"] = notifications_var.get()
        save_config(config)
        win.destroy()
        tk.messagebox.showinfo("Settings", "Saved. Port/folder changes require restart.")

    tk.Button(win, text="Save", command=save, bg=ACCENT, fg="black",
              relief="flat", width=12).pack(pady=15)

# =========================
# UI
# =========================

root = TkinterDnD.Tk()
root.title("LocalBridge by Jonasz Osmenda")
root.geometry("720x900")
root.configure(bg=BG_COLOR)

style = ttk.Style()
style.theme_use("clam")
style.configure("TProgressbar", troughcolor=CARD_COLOR, background=ACCENT, thickness=16)
style.configure("TNotebook", background=BG_COLOR, borderwidth=0)
style.configure("TNotebook.Tab", background=CARD_COLOR, foreground=TEXT,
                padding=[16, 6], font=("Segoe UI", 10))
style.map("TNotebook.Tab",
          background=[("selected", ACCENT)],
          foreground=[("selected", "#000000")])

local_ip = get_local_ip()
status_var = tk.StringVar(value="Disconnected")

# Header
header = tk.Frame(root, bg=BG_COLOR)
header.pack(fill="x", padx=20, pady=(10, 0))

tk.Label(header, text="LocalBridge PC ⇄ Android", font=("Segoe UI", 20, "bold"),
         fg=TEXT, bg=BG_COLOR).pack(side="left")

tk.Button(header, text="Visit my site", command=open_site, relief="flat",
          fg=ACCENT, bg=BG_COLOR, cursor="hand2").pack(side="right")

# IP card
card = tk.Frame(root, bg=CARD_COLOR)
card.pack(fill="x", padx=20, pady=8)

tk.Label(card, text=local_ip, font=("Segoe UI", 20, "bold"), fg=TEXT, bg=CARD_COLOR).pack(pady=(10, 0))
tk.Label(card, text=f"Port {PORT}", font=("Segoe UI", 11), fg=MUTED, bg=CARD_COLOR).pack()

buttons_row = tk.Frame(card, bg=CARD_COLOR)
buttons_row.pack(pady=8)

tk.Button(buttons_row, text="Copy IP", command=copy_ip, bg=ACCENT, fg="black", relief="flat").pack(side="left", padx=5)
tk.Button(buttons_row, text="📂 Open Received", command=open_received_folder, bg="#444", fg="white", relief="flat").pack(side="left", padx=5)
tk.Button(buttons_row, text="⚙ Settings", command=open_settings, bg="#444", fg="white", relief="flat").pack(side="left", padx=5)

# Tabs
notebook = ttk.Notebook(root)
notebook.pack(fill="both", expand=True, padx=20, pady=(8, 0))

# ── TAB 1: Server (Android) ──
tab_server = tk.Frame(notebook, bg=BG_COLOR)
notebook.add(tab_server, text="  📱 Server  ")

# Connected devices
peers_section = tk.Frame(tab_server, bg=BG_COLOR)
peers_section.pack(fill="x", pady=(8, 4))

tk.Label(peers_section, text="Connected devices:", font=("Segoe UI", 9),
         fg=MUTED, bg=BG_COLOR).pack(anchor="w")

peers_frame = tk.Frame(peers_section, bg=BG_COLOR)
peers_frame.pack(fill="x")

# Status row
status_frame = tk.Frame(tab_server, bg=BG_COLOR)
status_frame.pack(pady=(4, 0))

status_dot = tk.Label(status_frame, text="●", font=("Segoe UI", 18), fg=RED, bg=BG_COLOR)
status_dot.pack(side="left")

tk.Label(status_frame, textvariable=status_var, fg=TEXT, bg=BG_COLOR).pack(side="left", padx=5)

progress_bar = ttk.Progressbar(tab_server, orient="horizontal", mode="indeterminate")
progress_bar.pack(fill="x", pady=6)

tk.Button(tab_server, text="Clear History", command=clear_transfers,
          bg="#444", fg="white", relief="flat").pack(pady=4)

# Transfer cards scroll area
container = tk.Frame(tab_server, bg=BG_COLOR)
container.pack(fill="both", expand=True)

canvas = tk.Canvas(container, bg=BG_COLOR, highlightthickness=0)
scrollbar = tk.Scrollbar(container, orient="vertical", command=canvas.yview)

scrollable_frame = tk.Frame(canvas, bg=BG_COLOR)
scrollable_frame.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))

canvas_window = canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
canvas.bind("<Configure>", lambda e: canvas.itemconfig(canvas_window, width=e.width))
canvas.configure(yscrollcommand=scrollbar.set)

canvas.pack(side="left", fill="both", expand=True)
scrollbar.pack(side="right", fill="y")
def _on_mousewheel(e):
    active = notebook.index(notebook.select())
    if active == 0:
        canvas.yview_scroll(int(-1*(e.delta/120)), "units")
    else:
        pc_canvas.yview_scroll(int(-1*(e.delta/120)), "units")
root.bind_all("<MouseWheel>", _on_mousewheel)

drop_label_server = tk.Label(tab_server,
    text="Drag & Drop file or folder here → sends to Android(s)",
    bg=CARD_COLOR, fg=TEXT, height=3)
drop_label_server.pack(fill="x", pady=8)

# ── TAB 2: Connect to PC ──
tab_pc = tk.Frame(notebook, bg=BG_COLOR)
notebook.add(tab_pc, text="  🖥 Connect to PC  ")

tk.Label(tab_pc, text="Target PC", font=("Segoe UI", 13, "bold"),
         fg=TEXT, bg=BG_COLOR).pack(anchor="w", pady=(12, 4))

pc_conn_row = tk.Frame(tab_pc, bg=BG_COLOR)
pc_conn_row.pack(fill="x", pady=4)

pc_ip_var = tk.StringVar()
tk.Label(pc_conn_row, text="IP:", fg=MUTED, bg=BG_COLOR,
         font=("Segoe UI", 10)).pack(side="left", padx=(0, 4))
tk.Entry(pc_conn_row, textvariable=pc_ip_var, bg=CARD_COLOR, fg=TEXT,
         insertbackground=TEXT, relief="flat", width=18,
         font=("Segoe UI", 10)).pack(side="left", padx=(0, 6))

pc_port_var = tk.StringVar(value="8765")
tk.Label(pc_conn_row, text="Port:", fg=MUTED, bg=BG_COLOR,
         font=("Segoe UI", 10)).pack(side="left", padx=(0, 4))
tk.Entry(pc_conn_row, textvariable=pc_port_var, bg=CARD_COLOR, fg=TEXT,
         insertbackground=TEXT, relief="flat", width=6,
         font=("Segoe UI", 10)).pack(side="left", padx=(0, 8))

def on_pc_connect():
    ip = pc_ip_var.get().strip()
    try:
        port = int(pc_port_var.get().strip())
    except ValueError:
        port = 8765
    if ip:
        pc_connect(ip, port)

pc_connect_btn = tk.Button(pc_conn_row, text="Connect", command=on_pc_connect,
          bg=ACCENT, fg="black", relief="flat",
          font=("Segoe UI", 9))
pc_connect_btn.pack(side="left", padx=(0, 6))

def on_pc_disconnect():
    pc_disconnect()
    pc_connect_btn.config(text="Connect", command=on_pc_connect, bg=ACCENT, fg="black")

pc_disconnect_btn = tk.Button(pc_conn_row, text="Disconnect", command=on_pc_disconnect,
          bg=RED, fg="white", relief="flat",
          font=("Segoe UI", 9))
pc_disconnect_btn.pack(side="left", padx=(0, 6))
pc_disconnect_btn.pack_forget()  # hidden until connected

pc_scan_menu = tk.Menu(root, tearoff=0, bg=CARD_COLOR, fg=TEXT)

def show_scan_menu():
    pc_scan_btn.config(text="Scanning...", state="disabled")
    def _after_scan(found):
        pc_scan_btn.config(text="Scan", state="normal")
        populate_scan_dropdown(found)
    scan_for_pcs(callback=_after_scan)

pc_scan_btn = tk.Button(pc_conn_row, text="Scan", command=show_scan_menu,
                         bg="#444", fg=TEXT, relief="flat",
                         font=("Segoe UI", 9))
pc_scan_btn.pack(side="left")

# PC status row
pc_status_row = tk.Frame(tab_pc, bg=BG_COLOR)
pc_status_row.pack(fill="x", pady=6)

pc_connect_dot = tk.Label(pc_status_row, text="●", font=("Segoe UI", 18),
                           fg=RED, bg=BG_COLOR)
pc_connect_dot.pack(side="left")

pc_status_var = tk.StringVar(value="Not connected")
tk.Label(pc_status_row, textvariable=pc_status_var,
         fg=MUTED, bg=BG_COLOR, font=("Segoe UI", 10)).pack(side="left", padx=5)

pc_clear_row = tk.Frame(tab_pc, bg=BG_COLOR)
pc_clear_row.pack(fill="x", pady=(0, 4))

pc_transfer_cards = []

def clear_pc_transfers():
    for card in pc_transfer_cards:
        try:
            card.destroy()
        except Exception:
            pass
    pc_transfer_cards.clear()
    pc_canvas.yview_moveto(0)
    pc_canvas.configure(scrollregion=(0,0,0,0))

tk.Button(pc_clear_row, text="Clear History", command=clear_pc_transfers,
          bg="#444", fg="white", relief="flat").pack(side="left")

# PC transfer cards scroll area
pc_container = tk.Frame(tab_pc, bg=BG_COLOR)
pc_container.pack(fill="both", expand=True)

pc_canvas = tk.Canvas(pc_container, bg=BG_COLOR, highlightthickness=0)
pc_scrollbar = tk.Scrollbar(pc_container, orient="vertical", command=pc_canvas.yview)

pc_scrollable_frame = tk.Frame(pc_canvas, bg=BG_COLOR)
pc_scrollable_frame.bind("<Configure>", lambda e: pc_canvas.configure(scrollregion=pc_canvas.bbox("all")))

pc_canvas_window = pc_canvas.create_window((0, 0), window=pc_scrollable_frame, anchor="nw")
pc_canvas.bind("<Configure>", lambda e: pc_canvas.itemconfig(pc_canvas_window, width=e.width))
pc_canvas.configure(yscrollcommand=pc_scrollbar.set)

pc_canvas.pack(side="left", fill="both", expand=True)
pc_scrollbar.pack(side="right", fill="y")

drop_label_pc = tk.Label(tab_pc,
    text="Drag & Drop file or folder here → sends to connected PC",
    bg=CARD_COLOR, fg=TEXT, height=3)
drop_label_pc.pack(fill="x", pady=8)

# ── TAB 3: Clipboard ──
tab_clipboard = tk.Frame(notebook, bg=BG_COLOR)
notebook.add(tab_clipboard, text="  📋 Clipboard  ")

tk.Label(tab_clipboard, text="Shared Clipboard",
         font=("Segoe UI", 13, "bold"), fg=TEXT, bg=BG_COLOR).pack(anchor="w", pady=(12, 2), padx=15)

# ── PC area (editable) ──
pc_clipboard_header = tk.Frame(tab_clipboard, bg=BG_COLOR)
pc_clipboard_header.pack(fill="x", padx=15, pady=(6, 0))
tk.Label(pc_clipboard_header, text="🖥 PC", font=("Segoe UI", 10, "bold"),
         fg=ACCENT, bg=BG_COLOR).pack(side="left")
tk.Button(pc_clipboard_header, text="Clear", font=("Segoe UI", 8),
          bg="#444", fg="white", relief="flat",
          command=lambda: [clipboard_box.delete("1.0", tk.END), _on_clipboard_change()]).pack(side="right")

clipboard_box = tk.Text(
    tab_clipboard, bg=CARD_COLOR, fg=TEXT, insertbackground=TEXT,
    relief="flat", font=("Segoe UI", 11), wrap="word",
    padx=10, pady=10, undo=True, height=8
)
clipboard_box.pack(fill="x", padx=15, pady=(4, 0))

# ── Android area (read-only) ──
android_clipboard_header = tk.Frame(tab_clipboard, bg=BG_COLOR)
android_clipboard_header.pack(fill="x", padx=15, pady=(10, 0))
tk.Label(android_clipboard_header, text="📱 Android", font=("Segoe UI", 10, "bold"),
         fg=GREEN, bg=BG_COLOR).pack(side="left")

clipboard_android_box = tk.Text(
    tab_clipboard, bg=CARD_COLOR, fg=TEXT,
    relief="flat", font=("Segoe UI", 11), wrap="word",
    padx=10, pady=10, height=8, state="disabled"
)
clipboard_android_box.pack(fill="x", padx=15, pady=(4, 8))

def _on_clipboard_change(event=None):
    global clipboard_debounce_id, clipboard_pc_text
    if _clipboard_receiving:
        return
    if clipboard_debounce_id is not None:
        root.after_cancel(clipboard_debounce_id)
    def _send():
        global clipboard_pc_text
        text = clipboard_box.get("1.0", tk.END).rstrip("\n")
        if text == clipboard_pc_text:
            return
        clipboard_pc_text = text
        broadcast_clipboard(text, source="pc")
    clipboard_debounce_id = root.after(400, _send)

clipboard_box.bind("<KeyRelease>", _on_clipboard_change)
def drop(event):
    global _last_drop_time, _last_drop_file
    files = root.tk.splitlist(event.data)
    if not files:
        return
    now = time.time()
    # Debounce — ignore if exact same first file within 1s
    if files[0] == _last_drop_file and now - _last_drop_time < 1.0:
        return
    _last_drop_time = now
    _last_drop_file = files[0]

    active_tab = notebook.index(notebook.select())

    if active_tab == 0:
        # Server tab → send to Androids
        android_clients = {k: v for k, v in connected_clients.items() if v.get("device_type") != "pc"}
        if not android_clients:
            tk.messagebox.showwarning("No devices", "No Android devices connected.")
            return
        if len(android_clients) == 1:
            target_id = next(iter(android_clients))
        else:
            target_id = ask_target_device(android_clients)
            if target_id is None:
                return  # user cancelled
        for filepath in files:
            if os.path.isdir(filepath):
                zip_and_send_folder(filepath, target_id=target_id)
            else:
                send_file(filepath, target_id=target_id)
    else:
        # Connect to PC tab → send to PC
        if pc_client_ws is None:
            tk.messagebox.showwarning("No devices", "Not connected to any PC.")
            return
        for filepath in files:
            if os.path.isdir(filepath):
                def _zip_send(fp):
                    folder_name = os.path.basename(fp.rstrip("/\\"))
                    with tempfile.NamedTemporaryFile(delete=False, suffix=".zip", prefix=f"{folder_name}_") as tf:
                        tmp = tf.name
                    with zipfile.ZipFile(tmp, "w", zipfile.ZIP_DEFLATED) as zf:
                        for rd, dirs, flist in os.walk(fp):
                            for f in flist:
                                ap = os.path.join(rd, f)
                                zf.write(ap, os.path.relpath(ap, os.path.dirname(fp)))
                    pc_client_send(tmp)
                    try:
                        os.remove(tmp)
                    except Exception:
                        pass
                threading.Thread(target=_zip_send, args=(filepath,), daemon=True).start()
            else:
                pc_client_send(filepath)

root.drop_target_register(DND_FILES)
root.dnd_bind("<<Drop>>", drop)

update_status("Disconnected", False)

start_server_thread()
threading.Thread(target=watchdog, daemon=True).start()
threading.Thread(target=udp_discovery_server, daemon=True).start()

# =========================
# SYSTEM TRAY
# =========================

def create_tray_icon():
    img = Image.new("RGB", (64, 64), color=(30, 30, 30))
    draw = ImageDraw.Draw(img)
    draw.ellipse([8, 8, 56, 56], fill=(76, 194, 255))
    draw.text((20, 18), "LB", fill=(0, 0, 0))
    return img

def show_window(icon, item):
    root.after(0, root.deiconify)

def tray_notify(title, message):
    """Show balloon notification from tray icon."""
    if not config.get("notifications", True):
        return
    try:
        tray_icon.notify(message, title)
    except Exception:
        pass

def quit_app(icon, item):
    icon.stop()
    root.after(0, root.destroy)

def on_close():
    root.withdraw()

root.protocol("WM_DELETE_WINDOW", on_close)

def tray_send_file():
    def _pick():
        filepaths = filedialog.askopenfilenames(title="Send File")
        if not filepaths:
            return
        active_tab = notebook.index(notebook.select())
        for filepath in filepaths:
            if active_tab == 1 and pc_client_connected:
                pc_client_send(filepath)
            else:
                android_clients = {k: v for k, v in connected_clients.items() if v.get("device_type") != "pc"}
                if android_clients:
                    send_file(filepath)
                elif pc_client_connected:
                    pc_client_send(filepath)
                else:
                    root.after(0, lambda: tk.messagebox.showwarning("No devices", "No devices connected."))
                    break
    threading.Thread(target=_pick, daemon=True).start()

tray_menu = pystray.Menu(
    pystray.MenuItem("Show", show_window, default=True),
    pystray.MenuItem("Send File", lambda icon, item: tray_send_file()),
    pystray.Menu.SEPARATOR,
    pystray.MenuItem("Quit", quit_app)
)

tray_icon = pystray.Icon(
    "LocalBridge",
    create_tray_icon(),
    "LocalBridge",
    tray_menu
)

threading.Thread(target=tray_icon.run, daemon=True).start()
root.mainloop()