#!/usr/bin/env python3
"""Persistent Unix-socket daemon and CLI client for leanprover-community/repl.

Why this exists:
Agent tool calls execute in separate subshells. Running `lake build <Module>` in
a loop or piping one-shot `echo ... | lake env repl` re-imports `.olean`s and
re-elaborates thousands of lines on every edit. This script keeps a single
`lake env repl` process alive in the background over a Unix domain socket so:
  1. `load-header` loads imports (and optional unchanged prefix lines of a file)
     ONCE into an in-memory REPL environment (`env: 0`).
  2. `check` or `send` typechecks edited declarations/proofs (or slices of a
     file directly from disk) against `--env 0` in ~1 second without JSON
     escaping or re-elaborating the prefix.

Fast loop: always load the unchanged prefix up to the line *before* the first
edited declaration (`load-header --until-line N` or `--before-decl NAME`), then
`check --decl NAME` (or `--start-line/--end-line`) so each check elaborates only
the 20-50 lines being edited instead of everything from the header to EOF.
"""

from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import os
import re
import signal
import socket
import subprocess
import sys
import tempfile
import threading
import time
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_REPL_DIR = "/tmp/lean-repl"
REPL_REPO_URL = "https://github.com/leanprover-community/repl.git"
# A `check` range longer than this almost always means the prefix was not
# loaded with `--until-line`, so the REPL re-elaborates far more than the edit.
LARGE_CHECK_RANGE = 150
# Server-side deadline for requests that do not carry their own `timeout`.
DEFAULT_REQUEST_TIMEOUT = 300.0
LARGE_REPL_RSS_MB = 8192


def default_socket_path(repo_root: Path = ROOT) -> str:
    """Per-worktree socket, so sibling worktrees never share one `lake env`.

    `VERITY_LEAN_REPL_SOCKET` overrides the derived path.
    """
    override = os.environ.get("VERITY_LEAN_REPL_SOCKET")
    if override:
        return override
    digest = hashlib.sha1(str(repo_root.resolve()).encode("utf-8")).hexdigest()[:10]
    return f"/tmp/verity-lean-repl-{digest}.sock"


DEFAULT_SOCKET = default_socket_path()

_DECL_KEYWORDS = (
    "theorem|lemma|def|abbrev|instance|example|structure|inductive|class|opaque|axiom"
)
_DECL_HEAD_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial|nonrec)\s+)*"
    rf"(?:{_DECL_KEYWORDS})\s+([^\s:({{\[]+)"
)
_MUTUAL_DECL_HEAD_RE = re.compile(
    r"^\s+(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial|nonrec)\s+)*"
    rf"(?:{_DECL_KEYWORDS})\s+([^\s:({{\[]+)"
)
_NAMESPACE_RE = re.compile(r"^namespace\s+([^\s]+)")
_SECTION_RE = re.compile(r"^section(?:\s+([^\s]+))?\s*$")
_END_RE = re.compile(r"^end(?:\s+([^\s]+))?\s*$")
_MUTUAL_START_RE = re.compile(r"^mutual\s*$")
# Column-0 lines that still belong to the preceding declaration.
_DECL_CONTINUATION_RE = re.compile(r"^(?:\||termination_by\b|decreasing_by\b|where\b|deriving\b)")
_DECL_PREFIX_RE = re.compile(r"^(?:@\[|set_option\s.*\sin\s*$)")


def _name_matches(raw_found: str, full_found: str, wanted: str, has_ns: bool) -> bool:
    """Match `Ns.foo` against `foo` in `namespace Ns`, respecting explicit qualifiers."""
    if full_found == wanted or full_found.endswith(f".{wanted}"):
        return True
    if not has_ns and wanted.endswith(f".{raw_found}"):
        return True
    return False


def _docstring_start(lines: list[str], end_idx: int) -> int | None:
    """Index of the `/--` opening a docstring that closes on line `end_idx`."""
    if not lines[end_idx].rstrip().endswith("-/"):
        return None
    for idx in range(end_idx, -1, -1):
        if lines[idx].startswith("/--"):
            return idx
        if idx != end_idx and lines[idx].rstrip().endswith("-/"):
            return None
    return None


def _leading_prefix_start(lines: list[str], head: int) -> int:
    start = head
    while start > 0:
        prev = start - 1
        if _DECL_PREFIX_RE.match(lines[prev]):
            start = prev
            continue
        doc = _docstring_start(lines, prev)
        if doc is None:
            break
        start = doc
    return start


def locate_declaration(path: Path, name: str) -> tuple[int, int]:
    """1-based inclusive line range of top-level declaration `name` (or its enclosing `mutual` block).

    The range includes the docstring, attributes, and `set_option ... in`
    prefix lines, and ends at the last non-blank line before the next
    column-0 command. Raises `LookupError` if absent or ambiguous.
    """
    lines = path.read_text(encoding="utf-8").splitlines()
    scopes: list[tuple[str, list[str]]] = []
    mutual_start: int | None = None
    # Each entry is (report_line_idx, block_head_idx, is_mutual)
    matches: list[tuple[int, int, bool]] = []

    for idx, line in enumerate(lines):
        if _MUTUAL_START_RE.match(line):
            mutual_start = idx
            continue
        if mutual_start is not None:
            if _END_RE.match(line):
                mutual_start = None
                continue
            m_inner = _MUTUAL_DECL_HEAD_RE.match(line) or _DECL_HEAD_RE.match(line)
            if m_inner:
                raw_name = m_inner.group(1)
                ns_parts = [p for k, ps in scopes if k == "namespace" for p in ps]
                full_name = ".".join([*ns_parts, raw_name]) if ns_parts else raw_name
                if _name_matches(raw_name, full_name, name, bool(ns_parts)):
                    matches.append((idx, mutual_start, True))
            continue

        if m_ns := _NAMESPACE_RE.match(line):
            scopes.append(("namespace", m_ns.group(1).split(".")))
            continue
        if m_sec := _SECTION_RE.match(line):
            sec_name = m_sec.group(1)
            scopes.append(("section", sec_name.split(".") if sec_name else []))
            continue
        if m_end := _END_RE.match(line):
            end_name = m_end.group(1)
            if not end_name:
                if scopes:
                    scopes.pop()
            else:
                parts = end_name.split(".")
                while scopes and parts:
                    _, top_parts = scopes.pop()
                    if len(top_parts) >= len(parts):
                        break
                    parts = parts[:-len(top_parts)]
            continue

        if match := _DECL_HEAD_RE.match(line):
            raw_name = match.group(1)
            ns_parts = [p for k, ps in scopes if k == "namespace" for p in ps]
            full_name = ".".join([*ns_parts, raw_name]) if ns_parts else raw_name
            if _name_matches(raw_name, full_name, name, bool(ns_parts)):
                matches.append((idx, idx, False))

    if not matches:
        raise LookupError(f"declaration `{name}` not found in {path}")
    if len(matches) > 1:
        found = ", ".join(str(m[0] + 1) for m in matches)
        raise LookupError(f"declaration `{name}` is ambiguous in {path} (lines {found})")

    _, head, is_mutual = matches[0]
    start = _leading_prefix_start(lines, head)
    if is_mutual:
        end = head
        for idx in range(head + 1, len(lines)):
            if _END_RE.match(lines[idx]):
                end = idx
                break
            if lines[idx].strip():
                end = idx
        return start + 1, end + 1

    end = head
    for idx in range(head + 1, len(lines)):
        line = lines[idx]
        if line and not line[0].isspace() and not _DECL_CONTINUATION_RE.match(line):
            break
        if line.strip():
            end = idx
    return start + 1, end + 1


def detect_toolchain_tag(repo_root: Path = ROOT) -> str:
    toolchain_file = repo_root / "lean-toolchain"
    if not toolchain_file.exists():
        return "v4.31.0"
    raw = toolchain_file.read_text(encoding="utf-8").strip()
    version = raw.split(":")[-1].strip()
    if not version.startswith("v"):
        version = f"v{version}"
    return version


def ensure_repl_binary(
    repl_bin: Path | None,
    repl_dir: Path = Path(DEFAULT_REPL_DIR),
    repo_root: Path = ROOT,
) -> Path:
    if repl_bin is not None and repl_bin.exists():
        return repl_bin.resolve()
    candidates = [
        repl_dir / ".lake" / "build" / "bin" / "repl",
        Path("/tmp/repl/.lake/build/bin/repl"),
    ]
    for candidate in candidates:
        if candidate.exists():
            return candidate.resolve()

    tag = detect_toolchain_tag(repo_root)
    if not (repl_dir / "lakefile.lean").exists() and not (repl_dir / "lakefile.toml").exists():
        repl_dir.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(
            ["git", "clone", "--depth", "1", "--branch", tag, REPL_REPO_URL, str(repl_dir)],
            check=True,
        )
    env = os.environ.copy()
    env.setdefault("LEAN_NUM_THREADS", str(os.cpu_count() or 4))
    subprocess.run(
        ["lake", "build", "repl:exe"],
        cwd=str(repl_dir),
        env=env,
        check=True,
    )
    built = repl_dir / ".lake" / "build" / "bin" / "repl"
    if not built.exists():
        raise FileNotFoundError(f"Built repl binary not found at {built}")
    return built.resolve()


def read_repl_response(stdout) -> dict[str, Any]:
    lines: list[str] = []
    while True:
        line = stdout.readline()
        if not line:
            if not lines:
                raise EOFError("REPL process closed stdout unexpectedly")
            break
        if line in ("\n", "\r\n"):
            if lines:
                break
            continue
        lines.append(line)
    raw = "".join(lines).strip()
    return json.loads(raw)


def has_error_messages(resp: dict[str, Any]) -> bool:
    if "error" in resp:
        return True
    for msg in resp.get("messages", []):
        if msg.get("severity") == "error":
            return True
    if "message" in resp and "env" not in resp and "proofState" not in resp:
        return True
    return False


def spawn_repl(repl_cmd: list[str], cwd: Path, env: dict[str, str]) -> subprocess.Popen:
    # Own process group: `lake env` forks the real `repl`, and killing only
    # `lake` would orphan a still-spinning `repl` child.
    return subprocess.Popen(
        repl_cmd,
        cwd=str(cwd),
        env=env,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        text=True,
        bufsize=1,
        start_new_session=True,
    )


def kill_repl(proc: subprocess.Popen, sig: int) -> None:
    if proc.poll() is not None:
        return
    try:
        os.killpg(proc.pid, sig)
    except OSError:
        proc.kill()
    try:
        proc.wait(timeout=3)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except OSError:
            proc.kill()
        proc.wait()


def process_tree_rss_mb(root_pid: int) -> int | None:
    """Resident memory of `root_pid` and its descendants (Linux `/proc` only)."""
    try:
        children: dict[int, list[int]] = {}
        rss_kb: dict[int, int] = {}
        for entry in Path("/proc").iterdir():
            if not entry.name.isdigit():
                continue
            try:
                fields = (entry / "stat").read_text().rsplit(")", 1)[1].split()
                status = (entry / "status").read_text()
            except OSError:
                continue
            pid = int(entry.name)
            children.setdefault(int(fields[1]), []).append(pid)
            for line in status.splitlines():
                if line.startswith("VmRSS:"):
                    rss_kb[pid] = int(line.split()[1])
        total, stack = 0, [root_pid]
        while stack:
            pid = stack.pop()
            total += rss_kb.get(pid, 0)
            stack.extend(children.get(pid, []))
        return total // 1024
    except OSError:
        return None


def exchange_with_repl(proc: subprocess.Popen, payload: dict[str, Any], timeout: float) -> dict[str, Any]:
    """Send one stanza and read its response, raising `TimeoutError` past `timeout`."""
    result: dict[str, Any] = {}

    def worker() -> None:
        try:
            assert proc.stdin is not None and proc.stdout is not None
            proc.stdin.write(json.dumps(payload) + "\n\n")
            proc.stdin.flush()
            result["resp"] = read_repl_response(proc.stdout)
        except Exception as exc:  # surfaced to the caller below
            result["exc"] = exc

    thread = threading.Thread(target=worker, daemon=True)
    thread.start()
    thread.join(timeout)
    if thread.is_alive():
        raise TimeoutError
    if "exc" in result:
        raise result["exc"]
    return result["resp"]


def serve_daemon(socket_path: Path, repl_cmd: list[str], cwd: Path) -> int:
    socket_path.parent.mkdir(parents=True, exist_ok=True)
    lock_path = Path(f"{socket_path}.lock")
    lock_fd = os.open(str(lock_path), os.O_CREAT | os.O_RDWR, 0o600)
    try:
        fcntl.flock(lock_fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError:
        os.close(lock_fd)
        return 0

    if socket_path.exists():
        socket_path.unlink(missing_ok=True)

    env = os.environ.copy()
    env.setdefault("LEAN_NUM_THREADS", str(os.cpu_count() or 4))

    proc = spawn_repl(repl_cmd, cwd, env)

    state: dict[str, Any] = {
        "header_env": None,
        "last_env": None,
        "pid": proc.pid,
        "repl_cmd": repl_cmd,
    }

    server = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    server.bind(str(socket_path))
    os.chmod(socket_path, 0o600)
    server.listen(8)

    def cleanup(*_args: Any) -> None:
        try:
            server.close()
        except OSError:
            pass
        if socket_path.exists():
            try:
                socket_path.unlink()
            except OSError:
                pass
        kill_repl(proc, signal.SIGTERM)
        try:
            fcntl.flock(lock_fd, fcntl.LOCK_UN)
            os.close(lock_fd)
        except OSError:
            pass
        sys.exit(0)

    signal.signal(signal.SIGTERM, cleanup)
    signal.signal(signal.SIGINT, cleanup)

    try:
        while True:
            conn, _ = server.accept()
            with conn:
                data = b""
                while True:
                    chunk = conn.recv(65536)
                    if not chunk:
                        break
                    data += chunk
                if not data:
                    continue
                try:
                    req = json.loads(data.decode("utf-8"))
                except (UnicodeDecodeError, json.JSONDecodeError) as exc:
                    conn.sendall(json.dumps({"error": f"invalid request: {exc}"}).encode("utf-8"))
                    continue
                action = req.get("action", "send")
                if action == "status":
                    resp = {
                        "ok": proc.poll() is None,
                        "daemon_pid": os.getpid(),
                        "repl_pid": proc.pid,
                        "header_env": state["header_env"],
                        "last_env": state["last_env"],
                        "cwd": str(cwd.resolve()),
                        "repl_rss_mb": process_tree_rss_mb(proc.pid),
                    }
                    conn.sendall(json.dumps(resp).encode("utf-8"))
                    continue
                if action == "restart":
                    kill_repl(proc, signal.SIGKILL)
                    proc = spawn_repl(repl_cmd, cwd, env)
                    state.update(header_env=None, last_env=None, pid=proc.pid)
                    conn.sendall(json.dumps({"ok": True, "repl_pid": proc.pid}).encode("utf-8"))
                    continue
                if action == "stop":
                    conn.sendall(json.dumps({"ok": True, "stopped": True}).encode("utf-8"))
                    cleanup()

                payload = req.get("payload")
                if not isinstance(payload, dict):
                    conn.sendall(json.dumps({"error": "missing dict payload"}).encode("utf-8"))
                    continue
                mark_header = bool(req.get("mark_header", False))
                timeout = float(req.get("timeout", DEFAULT_REQUEST_TIMEOUT))
                try:
                    repl_resp = exchange_with_repl(proc, payload, timeout)
                except TimeoutError:
                    # A runaway elaboration (e.g. a looping `simp`) would otherwise
                    # wedge every later request behind it: restart the REPL.
                    kill_repl(proc, signal.SIGKILL)
                    proc = spawn_repl(repl_cmd, cwd, env)
                    state.update(header_env=None, last_env=None, pid=proc.pid)
                    message = (
                        f"REPL request exceeded {timeout:g}s; the REPL was restarted and "
                        "header_env cleared. Re-run `load-header`, and bound exploratory "
                        "tactics with `set_option maxHeartbeats N in`."
                    )
                    conn.sendall(json.dumps({"error": message, "restarted": True}).encode("utf-8"))
                    continue
                except Exception as exc:
                    conn.sendall(json.dumps({"error": f"REPL communication error: {exc}"}).encode("utf-8"))
                    continue
                if "env" in repl_resp and not has_error_messages(repl_resp):
                    state["last_env"] = repl_resp["env"]
                    if mark_header:
                        state["header_env"] = repl_resp["env"]
                conn.sendall(json.dumps(repl_resp).encode("utf-8"))
    finally:
        cleanup()


def request_daemon(socket_path: Path, message: dict[str, Any], timeout: float = 300.0) -> dict[str, Any]:
    if not socket_path.exists():
        raise FileNotFoundError(
            f"REPL daemon socket {socket_path} does not exist. Run `lean_repl_daemon.py start` first."
        )
    if message.get("action", "send") == "send":
        # The daemon enforces the deadline (restarting a wedged REPL); wait a
        # little longer here so its restart notice reaches the caller.
        message = {**message, "timeout": timeout}
        timeout += 30.0
    client = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    client.settimeout(timeout)
    with client:
        client.connect(str(socket_path))
        client.sendall(json.dumps(message).encode("utf-8"))
        client.shutdown(socket.SHUT_WR)
        chunks: list[bytes] = []
        while True:
            chunk = client.recv(65536)
            if not chunk:
                break
            chunks.append(chunk)
    return json.loads(b"".join(chunks).decode("utf-8"))


def extract_file_slice(path: Path, start_line: int, end_line: int | None) -> str:
    lines = path.read_text(encoding="utf-8").splitlines()
    start_idx = max(0, start_line - 1)
    end_idx = len(lines) if end_line is None else min(len(lines), end_line)
    return "\n".join(lines[start_idx:end_idx])


def extract_import_header(path: Path, until_line: int | None) -> str:
    lines = path.read_text(encoding="utf-8").splitlines()
    if until_line is not None:
        return "\n".join(lines[:until_line])
    header_lines: list[str] = []
    block_comment_depth = 0
    for line in lines:
        stripped = line.strip()
        depth_delta = stripped.count("/-") - stripped.count("-/")
        if stripped.startswith("/-") or block_comment_depth > 0:
            block_comment_depth = max(0, block_comment_depth + depth_delta)
            header_lines.append(line)
            continue
        if (
            not stripped
            or stripped.startswith("--")
            or stripped.startswith("import ")
            or stripped.startswith("open ")
            or stripped.startswith("set_option ")
            or stripped.startswith("universe ")
            or stripped.startswith("variable ")
            or stripped.startswith("namespace ")
            or stripped.startswith("noncomputable ")
        ):
            header_lines.append(line)
            continue
        break
    return "\n".join(header_lines)


def cmd_start(args: argparse.Namespace) -> int:
    socket_path = Path(args.socket)
    if socket_path.exists():
        try:
            status = request_daemon(socket_path, {"action": "status"}, timeout=2.0)
            if status.get("ok"):
                wanted_cwd = str(Path(args.cwd).resolve())
                if status.get("cwd") not in (None, wanted_cwd):
                    print(
                        f"REPL daemon on {socket_path} serves {status['cwd']}, not {wanted_cwd}; "
                        "pass a distinct --socket (or set VERITY_LEAN_REPL_SOCKET).",
                        file=sys.stderr,
                    )
                    return 1
                print(json.dumps({"status": "already_running", **status}))
                return 0
        except OSError:
            pass

    repl_bin = ensure_repl_binary(
        Path(args.repl_bin) if args.repl_bin else None,
        Path(args.repl_dir),
        Path(args.cwd),
    )
    repl_cmd = ["lake", "env", str(repl_bin)] if not args.no_lake_env else [str(repl_bin)]

    if args.foreground:
        return serve_daemon(socket_path, repl_cmd, Path(args.cwd))

    log_path = Path(args.log or f"{socket_path}.log")
    with open(log_path, "ab") as log_file:
        subprocess.Popen(
            [
                sys.executable,
                str(Path(__file__).resolve()),
                "start",
                "--foreground",
                "--socket",
                str(socket_path),
                "--repl-bin",
                str(repl_bin),
                "--cwd",
                str(args.cwd),
                *(["--no-lake-env"] if args.no_lake_env else []),
            ],
            stdout=log_file,
            stderr=log_file,
            start_new_session=True,
        )

    deadline = time.time() + 10.0
    while time.time() < deadline:
        if socket_path.exists():
            try:
                status = request_daemon(socket_path, {"action": "status"}, timeout=2.0)
                if status.get("ok"):
                    print(json.dumps({"status": "started", "socket": str(socket_path), **status}))
                    return 0
            except OSError:
                pass
        time.sleep(0.1)

    print(f"Failed to start REPL daemon on {socket_path}; inspect {log_path}", file=sys.stderr)
    return 1


def advise(message: str) -> None:
    print(f"lean_repl_daemon: hint: {message}", file=sys.stderr)


def resolve_header_until_line(args: argparse.Namespace) -> int | None:
    if args.before_decl is not None:
        if args.until_line is not None:
            raise ValueError("pass only one of --until-line / --before-decl")
        start, _ = locate_declaration(Path(args.file), args.before_decl)
        return start - 1
    if args.until_line is None:
        advise(
            "only the import header was loaded; every `check` must then re-elaborate "
            "the file from the header onward. Pass `--until-line <first_edited_decl - 1>` "
            "(or `--before-decl <name>`) so `check` elaborates just the edited declaration."
        )
    return args.until_line


def resolve_check_range(args: argparse.Namespace) -> tuple[int, int | None]:
    if args.decl is not None:
        if args.start_line is not None or args.end_line is not None:
            raise ValueError("pass either --decl or --start-line/--end-line, not both")
        return locate_declaration(Path(args.file), args.decl)
    if args.start_line is None:
        raise ValueError("specify --decl NAME or --start-line M [--end-line K]")
    if args.end_line is None:
        advise("no --end-line given: checking through EOF. Pass the edited declaration's range.")
    elif args.end_line - args.start_line + 1 > LARGE_CHECK_RANGE:
        advise(
            f"checking {args.end_line - args.start_line + 1} lines. Reload the prefix with "
            f"`load-header --until-line {args.start_line - 1}` and check one declaration "
            "at a time (`check --decl <name>`)."
        )
    return args.start_line, args.end_line


def warn_if_repl_memory_large(socket_path: Path) -> None:
    # The REPL never frees environments; each multi-thousand-line prefix adds
    # gigabytes, and a bloated REPL starves every new `lean`/`lake` process.
    try:
        rss = request_daemon(socket_path, {"action": "status"}, timeout=5.0).get("repl_rss_mb")
    except OSError:
        return
    if isinstance(rss, int) and rss > LARGE_REPL_RSS_MB:
        advise(
            f"the REPL holds {rss} MiB of environments; run `lean_repl_daemon.py restart` "
            "before loading another large file's prefix."
        )


def cmd_load_header(args: argparse.Namespace) -> int:
    socket_path = Path(args.socket)
    file_path = Path(args.file)
    cmd_text = extract_import_header(file_path, resolve_header_until_line(args))
    payload: dict[str, Any] = {"cmd": cmd_text}
    if args.env is not None:
        payload["env"] = args.env
    resp = request_daemon(
        socket_path,
        {"action": "send", "payload": payload, "mark_header": True},
        timeout=args.timeout,
    )
    print(json.dumps(resp, indent=2))
    warn_if_repl_memory_large(socket_path)
    return 1 if has_error_messages(resp) else 0


def cmd_check(args: argparse.Namespace) -> int:
    import shutil

    socket_path = Path(args.socket)
    file_path = Path(args.file)
    if args.socket == DEFAULT_SOCKET and not socket_path.exists() and args.decl and shutil.which("turbo-lean"):
        res = subprocess.run(
            ["turbo-lean", "check", str(file_path), "--decl", args.decl],
            cwd=str(ROOT),
        )
        return res.returncode
    start_line, end_line = resolve_check_range(args)
    snippet = extract_file_slice(file_path, start_line, end_line)
    env_id = args.env
    if env_id is None:
        status = request_daemon(socket_path, {"action": "status"}, timeout=5.0)
        env_id = status.get("header_env")
    payload: dict[str, Any] = {"cmd": snippet}
    if env_id is not None:
        payload["env"] = env_id
    resp = request_daemon(
        socket_path,
        {"action": "send", "payload": payload},
        timeout=args.timeout,
    )
    print(json.dumps(resp, indent=2))
    return 1 if has_error_messages(resp) else 0


def cmd_send(args: argparse.Namespace) -> int:
    socket_path = Path(args.socket)
    if args.json:
        payload = json.loads(args.json)
    elif args.tactic is not None:
        if args.proof_state is None:
            raise ValueError("--proof-state is required when --tactic is used")
        payload = {"tactic": args.tactic, "proofState": args.proof_state}
    else:
        if args.cmd is None:
            raise ValueError("Specify --cmd, --tactic, or --json")
        payload = {"cmd": args.cmd}
        if args.env is not None:
            payload["env"] = args.env
    resp = request_daemon(
        socket_path,
        {"action": "send", "payload": payload},
        timeout=args.timeout,
    )
    print(json.dumps(resp, indent=2))
    return 1 if (args.fail_on_error and has_error_messages(resp)) else 0


def cmd_locate(args: argparse.Namespace) -> int:
    start, end = locate_declaration(Path(args.file), args.decl)
    print(json.dumps({"decl": args.decl, "start_line": start, "end_line": end, "until_line": start - 1}))
    return 0


def cmd_status(args: argparse.Namespace) -> int:
    resp = request_daemon(Path(args.socket), {"action": "status"}, timeout=5.0)
    print(json.dumps(resp, indent=2))
    return 0 if resp.get("ok") else 1


def cmd_restart(args: argparse.Namespace) -> int:
    resp = request_daemon(Path(args.socket), {"action": "restart"}, timeout=30.0)
    print(json.dumps(resp, indent=2))
    return 0 if resp.get("ok") else 1


def cmd_stop(args: argparse.Namespace) -> int:
    socket_path = Path(args.socket)
    if not socket_path.exists():
        print(json.dumps({"ok": True, "stopped": False, "reason": "not_running"}))
        return 0
    resp = request_daemon(socket_path, {"action": "stop"}, timeout=5.0)
    print(json.dumps(resp, indent=2))
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="subcommand", required=True)

    p_start = sub.add_parser("start", help="Start the persistent Lean REPL daemon")
    p_start.add_argument("--socket", default=DEFAULT_SOCKET)
    p_start.add_argument("--repl-bin", default=None)
    p_start.add_argument("--repl-dir", default=DEFAULT_REPL_DIR)
    p_start.add_argument("--cwd", default=str(ROOT))
    p_start.add_argument("--log", default=None)
    p_start.add_argument("--foreground", action="store_true")
    p_start.add_argument("--no-lake-env", action="store_true")
    p_start.set_defaults(func=cmd_start)

    p_header = sub.add_parser(
        "load-header",
        help=(
            "Load a file's prefix once into header_env; pass --until-line "
            "<first_edited_decl - 1> (or --before-decl NAME) so checks stay small"
        ),
    )
    p_header.add_argument("--socket", default=DEFAULT_SOCKET)
    p_header.add_argument("--file", required=True)
    p_header.add_argument("--until-line", type=int, default=None)
    p_header.add_argument(
        "--before-decl",
        default=None,
        help="Load everything before this declaration (docstring/attributes included)",
    )
    p_header.add_argument("--env", type=int, default=None)
    p_header.add_argument("--timeout", type=float, default=300.0)
    p_header.set_defaults(func=cmd_load_header)

    p_check = sub.add_parser(
        "check",
        help="Typecheck a declaration (--decl) or line range from a file against header_env",
    )
    p_check.add_argument("--socket", default=DEFAULT_SOCKET)
    p_check.add_argument("--file", required=True)
    p_check.add_argument("--decl", default=None, help="Check exactly this declaration's lines")
    p_check.add_argument("--start-line", type=int, default=None)
    p_check.add_argument("--end-line", type=int, default=None)
    p_check.add_argument("--env", type=int, default=None)
    p_check.add_argument("--timeout", type=float, default=300.0)
    p_check.set_defaults(func=cmd_check)

    p_locate = sub.add_parser(
        "locate",
        help="Print a declaration's line range and the --until-line that precedes it",
    )
    p_locate.add_argument("--file", required=True)
    p_locate.add_argument("--decl", required=True)
    p_locate.set_defaults(func=cmd_locate)

    p_send = sub.add_parser("send", help="Send a raw cmd, tactic, or JSON stanza to REPL")
    p_send.add_argument("--socket", default=DEFAULT_SOCKET)
    p_send.add_argument("--cmd", default=None)
    p_send.add_argument("--env", type=int, default=None)
    p_send.add_argument("--tactic", default=None)
    p_send.add_argument("--proof-state", type=int, default=None)
    p_send.add_argument("--json", default=None)
    p_send.add_argument("--timeout", type=float, default=300.0)
    p_send.add_argument("--fail-on-error", action=argparse.BooleanOptionalAction, default=True)
    p_send.set_defaults(func=cmd_send)

    p_status = sub.add_parser("status", help="Check daemon status and saved env IDs")
    p_status.add_argument("--socket", default=DEFAULT_SOCKET)
    p_status.set_defaults(func=cmd_status)

    p_restart = sub.add_parser(
        "restart",
        help="Restart the REPL process (frees every loaded env; reload the header afterwards)",
    )
    p_restart.add_argument("--socket", default=DEFAULT_SOCKET)
    p_restart.set_defaults(func=cmd_restart)

    p_stop = sub.add_parser("stop", help="Stop the running REPL daemon")
    p_stop.add_argument("--socket", default=DEFAULT_SOCKET)
    p_stop.set_defaults(func=cmd_stop)

    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    try:
        return args.func(args)
    except (LookupError, ValueError) as exc:
        print(f"lean_repl_daemon: error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
