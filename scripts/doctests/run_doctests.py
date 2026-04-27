#!/usr/bin/python3
# /// script
# dependencies = [
#   "tqdm",
#   "polars",
# ]
# ///
import json
import os
import queue
import signal
import argparse
import shutil
import socket
import sqlite3
import subprocess
import sys
import tempfile
import time
import tomllib
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime
from pathlib import Path
from tqdm import tqdm
import polars as pl
import analysis

PRUSTI_SERVER_PORT  = 27010
PRUSTI_SERVER_COUNT = max(1, (os.cpu_count() or 4) * 3 // 4)


def _clean_crate_level(crate_level: str) -> str:
    """Remove #![deny(warnings)] and #![feature(stmt_expr_attributes)] from crate-level attrs."""
    return (crate_level
        .replace("#![deny(warnings)]\n", "")
        .replace("#![feature(stmt_expr_attributes)]\n", "")
    )


def cmd_extract(args):
    src_dir = Path(args.source_dir)
    output_dir = Path(args.output_dir)
    library = args.library

    if not src_dir.is_dir():
        print(f"Error: Source directory {src_dir} does not exist.")
        return

    output_dir.mkdir(parents=True, exist_ok=True)

    cargo_cmd = ["cargo", "rustdoc", "--", "-Zunstable-options", "--output-format=doctest"]
    if hasattr(args, 'channel') and args.channel:
        cargo_cmd = ["cargo", f"+{args.channel}", "rustdoc", "--", "-Zunstable-options", "--output-format=doctest"]
    result = subprocess.run(
        cargo_cmd,
        capture_output=True, text=True, cwd=str(src_dir),
    )
    if result.returncode != 0:
        print(f"Error: cargo rustdoc failed:\n{result.stderr}", file=sys.stderr)
        sys.exit(1)

    data = json.loads(result.stdout)

    seen = set()
    n_written = 0
    for dt in data["doctests"]:
        attrs = dt["doctest_attributes"]
        if (attrs["should_panic"] or attrs["no_run"] or attrs["compile_fail"]
                or attrs["standalone_crate"] or attrs["ignore"] != "None"
                or not attrs["rust"] or dt["doctest_code"] is None
                or ".." in dt["file"]):
            continue

        key = (dt["file"], dt["line"])
        if key in seen:
            continue
        seen.add(key)

        dc = dt["doctest_code"]
        crate_level = _clean_crate_level(dc["crate_level"])
        code = dc["code"]
        wrapper = dc["wrapper"]

        if wrapper is not None:
            full_code = crate_level + wrapper["before"] + code + wrapper["after"]
        else:
            full_code = crate_level + code

        # Build filename
        rel = dt["file"]
        pfx = f"{library}/src/"
        if rel.startswith(pfx):
            rel = rel[len(pfx):]
        rel = rel.rsplit(".", 1)[0] if "." in rel else rel
        path_part = rel.replace("/", "_")

        out_path = output_dir / f"{library}_{path_part}_doctest_{dt['line']}.rs"
        with open(out_path, 'w', encoding='utf-8') as f:
            f.write(full_code)
        n_written += 1

    print(f"Done! Extracted {n_written} snippets to {output_dir}")


def compile_one(rs_file: Path, bin_dir: Path, prusti_rustc: Path, channel: str = "nightly") -> tuple[bool, str]:
    out_bin = bin_dir / rs_file.stem
    result = subprocess.run(
        ["rustc", f"+{channel}", "--edition", "2021", "-Zcrate-attr=feature(stmt_expr_attributes)", str(rs_file), "-o", str(out_bin)],
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        return False, result.stderr
    env = os.environ.copy()
    env.update(PRUSTI_NO_VERIFY_ENV)
    with tempfile.TemporaryDirectory() as tmp:
        pcheck = subprocess.run(
            [str(prusti_rustc), "--edition", "2021", "--crate-type=lib", "--out-dir", tmp, str(rs_file)],
            capture_output=True,
            text=True,
            env=env,
        )
    if pcheck.returncode != 0:
        out_bin.unlink(missing_ok=True)
        return False, pcheck.stderr
    return True, result.stderr


def cmd_compile(args):
    snippets_dir = Path(args.snippets_dir)
    bin_dir = Path(args.bin_dir)
    prusti_rustc = Path(args.prusti_rustc)

    if not snippets_dir.is_dir():
        print(f"Error: Snippets directory {snippets_dir} does not exist.")
        return
    if not prusti_rustc.is_file():
        print(f"Error: prusti-rustc not found at {prusti_rustc}")
        return

    bin_dir.mkdir(parents=True, exist_ok=True)

    rs_files = sorted(snippets_dir.glob("*.rs"))
    ok = fail = 0
    failures = []

    channel = getattr(args, "channel", "nightly")
    with ThreadPoolExecutor() as executor:
        futures = {executor.submit(compile_one, f, bin_dir, prusti_rustc, channel): f for f in rs_files}
        with tqdm(total=len(rs_files), desc="Compiling", unit="file") as pbar:
            for future in as_completed(futures):
                success, stderr = future.result()
                if success:
                    ok += 1
                else:
                    fail += 1
                    failures.append((futures[future], stderr))
                pbar.update(1)

    if getattr(args, "verbose", False):
        for rs_file, stderr in sorted(failures):
            print(f"\n--- {rs_file.name} ---")
            print(stderr.strip())

    print(f"\nDone! {ok} compiled OK, {fail} failed.")


def cmd_run(args):
    bin_dir = Path(args.bin_dir)

    if not bin_dir.is_dir():
        print(f"Error: Binary directory {bin_dir} does not exist.")
        return

    binaries = [p for p in sorted(bin_dir.iterdir()) if p.is_file() and os.access(p, os.X_OK)]
    ok = fail = 0
    failures = []

    for binary in tqdm(binaries, desc="Running", unit="binary"):
        result = subprocess.run([str(binary)], capture_output=True, text=True, timeout=10)
        if result.returncode == 0:
            ok += 1
        else:
            fail += 1
            output = (result.stdout + result.stderr).strip()
            failures.append((binary, result.returncode, output))

    for binary, returncode, output in failures:
        print(f"\n--- {binary.name} (exit {returncode}) ---")
        if output:
            print(output)

    print(f"\nDone! {ok} passed, {fail} failed.")


def cmd_copy_passing(args):
    snippets_dir = Path(args.snippets_dir)
    bin_dir      = Path(args.bin_dir)
    dest_dir     = Path(args.dest_dir)

    if not snippets_dir.is_dir():
        print(f"Error: Snippets directory {snippets_dir} does not exist.")
        return
    if not bin_dir.is_dir():
        print(f"Error: Binary directory {bin_dir} does not exist.")
        return

    dest_dir.mkdir(parents=True, exist_ok=True)

    binaries = [p for p in sorted(bin_dir.iterdir()) if p.is_file() and os.access(p, os.X_OK)]
    copied = skipped = 0

    for binary in tqdm(binaries, desc="Checking", unit="binary"):
        result = subprocess.run([str(binary)], capture_output=True, timeout=10)
        if result.returncode == 0:
            snippet = snippets_dir / (binary.name + ".rs")
            if snippet.exists():
                shutil.copy2(snippet, dest_dir / snippet.name)
                copied += 1
        else:
            skipped += 1

    print(f"\nDone! {copied} snippets copied, {skipped} skipped (failed at runtime).")


def init_db(db_path: Path) -> sqlite3.Connection:
    conn = sqlite3.connect(db_path)
    conn.execute("""
        CREATE TABLE IF NOT EXISTS results (
            id         INTEGER PRIMARY KEY AUTOINCREMENT,
            file_name  TEXT    NOT NULL,
            success    TEXT    NOT NULL,  -- 'success', 'fail', or 'timeout'
            output     TEXT,
            duration_s REAL,
            timestamp  TEXT    DEFAULT CURRENT_TIMESTAMP
        )
    """)
    conn.commit()
    return conn



PRUSTI_ENV = {
    "PRUSTI_QUIET": "true",
    "PRUSTI_FULL_COMPILATION": "true",
    "PRUSTI_CARGO": "",
    "PRUSTI_CHECK_OVERFLOWS": "false",
}

PRUSTI_NO_VERIFY_ENV = {
    **PRUSTI_ENV,
    "PRUSTI_NO_VERIFY": "true",
}


def _run_prusti(rs_file: Path, prusti_rustc: Path, timeout: int, env: dict) -> tuple[str, str, float]:
    """Run prusti-rustc with the given env; return (status, stderr, elapsed_s)."""
    with tempfile.TemporaryDirectory() as tmp:
        proc = subprocess.Popen(
            [str(prusti_rustc), "--edition", "2021", "--crate-type=lib", "--out-dir", tmp, str(rs_file)],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            env=env,
            start_new_session=True,
        )
        t0 = time.monotonic()
        try:
            _, stderr = proc.communicate(timeout=timeout)
            return ("success" if proc.returncode == 0 else "fail"), stderr, time.monotonic() - t0
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGKILL)
            proc.wait()
            return "timeout", "", time.monotonic() - t0


def _wait_for_server(port: int, timeout: float = 60.0):
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        try:
            with socket.create_connection(("localhost", port), timeout=0.5):
                return
        except (ConnectionRefusedError, OSError):
            time.sleep(0.2)
    raise TimeoutError(f"prusti-server did not start within {timeout:.0f}s")


def _wait_for_port_free(port: int, timeout: float = 30.0):
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        try:
            with socket.create_connection(("localhost", port), timeout=0.5):
                time.sleep(0.2)  # still listening, keep waiting
        except (ConnectionRefusedError, OSError):
            return  # port is free
    raise TimeoutError(f"Port {port} not released within {timeout:.0f}s")


def _kill_server(proc: "subprocess.Popen[bytes]"):
    """Kill a server process group (prusti-server + prusti-server-driver)."""
    try:
        os.killpg(proc.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    proc.wait()


def _spawn_server(prusti_server_bin: Path, port: int) -> "subprocess.Popen[bytes]":
    return subprocess.Popen(
        [str(prusti_server_bin), "--port", str(port)],
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        start_new_session=True,
    )


def _restart_server(server_procs: list, idx: int, prusti_rustc: Path):
    """Kill the server process group at index idx and start a fresh one on the same port."""
    port = PRUSTI_SERVER_PORT + idx
    _kill_server(server_procs[idx])
    _wait_for_port_free(port)
    server_procs[idx] = _spawn_server(prusti_rustc.parent / "prusti-server", port)
    _wait_for_server(port)


def prusti_one(rs_file: Path, prusti_rustc: Path, timeout: int,
               server_addresses: list[str], server_procs: list,
               server_queue: "queue.Queue | None") -> tuple[str, str, float]:
    idx = server_queue.get() if server_queue is not None else None
    try:
        env = os.environ.copy()
        env.update(PRUSTI_ENV)
        if idx is not None:
            env["PRUSTI_SERVER_ADDRESS"] = server_addresses[idx]
        status, stderr, duration = _run_prusti(rs_file, prusti_rustc, timeout, env)
        if status == "timeout" and idx is not None:
            _restart_server(server_procs, idx, prusti_rustc)
        return status, stderr, duration
    finally:
        if server_queue is not None:
            server_queue.put(idx)


def cmd_prusti(args):
    prusti_rustc = Path(args.prusti_rustc)

    if not prusti_rustc.is_file():
        print(f"Error: prusti-rustc not found at {prusti_rustc}")
        return

    if args.file:
        rs_file = Path(args.file)
        if not rs_file.is_file():
            print(f"Error: {rs_file} does not exist.")
            return
        rs_files = [rs_file]
    else:
        dest_dir = Path(args.dest_dir)
        if not dest_dir.is_dir():
            print(f"Error: Directory {dest_dir} does not exist.")
            return
        rs_files = sorted(dest_dir.glob("*.rs"))
    if args.db:
        db_path = Path(args.db)
    else:
        timestamp = datetime.now().strftime("%Y-%m-%d_%H%M%S")
        db_path = Path(f"prusti_{timestamp}.db")
    conn = init_db(db_path)
    print(f"Writing results to {db_path}")

    timeout = args.timeout
    ok = fail = timed_out = 0
    failures = []

    prusti_server_bin = prusti_rustc.parent / "prusti-server"
    server_procs = []
    server_addresses = []
    try:
        if args.server:
            if not prusti_server_bin.is_file():
                print(f"Error: prusti-server not found at {prusti_server_bin}", file=sys.stderr)
                sys.exit(1)
            for i in range(PRUSTI_SERVER_COUNT):
                port = PRUSTI_SERVER_PORT + i
                proc = _spawn_server(prusti_server_bin, port)
                server_procs.append(proc)
                server_addresses.append(f"localhost:{port}")
            for port in range(PRUSTI_SERVER_PORT, PRUSTI_SERVER_PORT + PRUSTI_SERVER_COUNT):
                _wait_for_server(port)
            print(f"Started {PRUSTI_SERVER_COUNT} prusti-server instances (ports {PRUSTI_SERVER_PORT}–{PRUSTI_SERVER_PORT + PRUSTI_SERVER_COUNT - 1})")

        server_queue: queue.Queue | None = None
        if server_addresses:
            server_queue = queue.Queue()
            for i in range(len(server_addresses)):
                server_queue.put(i)

        max_workers = PRUSTI_SERVER_COUNT
        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            futures = {
                executor.submit(prusti_one, f, prusti_rustc, timeout, server_addresses, server_procs, server_queue): f
                for f in rs_files
            }
            with tqdm(total=len(rs_files), desc="Prusti", unit="file") as pbar:
                for future in as_completed(futures):
                    rs_file = futures[future]
                    status, stderr, duration_s = future.result()
                    conn.execute(
                        "INSERT INTO results (file_name, success, output, duration_s) VALUES (?, ?, ?, ?)",
                        (rs_file.name, status, stderr, duration_s),
                    )
                    conn.commit()
                    if status == "success":
                        ok += 1
                    elif status == "fail":
                        fail += 1
                        failures.append((rs_file, stderr))
                    else:
                        timed_out += 1
                    pbar.update(1)
    finally:
        for proc in server_procs:
            _kill_server(proc)

    conn.close()
    if getattr(args, "verbose", False):
        for rs_file, stderr in sorted(failures):
            print(f"\n--- {rs_file.name} ---")
            print(stderr.strip())
    print(f"\nDone! {ok} passed, {fail} failed, {timed_out} timed out.")


def _snapshot_name(prusti_dir: Path, branch: "str | None") -> tuple[Path, str]:
    """Compute snapshot (dest, name) from git metadata; also checks for uncommitted changes."""
    def git(*cmd):
        return subprocess.run(["git", "-C", str(prusti_dir)] + list(cmd),
                              capture_output=True, text=True, check=True).stdout.strip()

    diff = subprocess.run(["git", "-C", str(prusti_dir), "diff", "--quiet", "--", "HEAD"])
    if diff.returncode != 0:
        print(f"Error: tracked files modified in {prusti_dir}; aborting.", file=sys.stderr)
        sys.exit(1)

    timestamp = git("log", "-1", "--format=%cd", "--date=format:%Y%m%d-%H%M%S")
    commit_hash = git("rev-parse", "--short=9", "HEAD")
    prefix = f"{branch}-" if branch else ""
    name = f"{prefix}{timestamp}-{commit_hash}"
    return Path(f"./prusti-{name}"), name


def _snapshot_do_build(prusti_dir: Path, dest: Path):
    """Build Prusti and copy artifacts into dest."""
    print("Updating submodules and building…")
    (prusti_dir / "prusti" / "src" / "driver.rs").touch()
    subprocess.run(["git", "-C", str(prusti_dir), "submodule", "update"], check=True)
    subprocess.run(["./x.py", "build"], cwd=str(prusti_dir), check=True)

    (dest / "deps").mkdir(parents=True, exist_ok=True)

    for bin_name in ["prusti-rustc", "cargo-prusti", "prusti-driver",
                     "prusti-server", "prusti-server-driver", "prusti-smt-solver"]:
        shutil.copy2(prusti_dir / "target" / "debug" / bin_name, dest / bin_name)

    for rlib in (prusti_dir / "target" / "verify" / "debug").glob("libprusti_contracts*.rlib"):
        shutil.copy2(rlib, dest / rlib.name)

    for f in (prusti_dir / "target" / "verify" / "debug" / "deps").iterdir():
        shutil.copy2(f, dest / "deps" / f.name)

    viper_link = dest / "viper_tools"
    if viper_link.is_symlink() or viper_link.exists():
        viper_link.unlink()
    viper_link.symlink_to(prusti_dir / "viper_tools")


def cmd_snapshot(args):
    prusti_dir = Path(args.prusti_dir).expanduser()
    if not prusti_dir.is_dir():
        print(f"Error: prusti directory not found at {prusti_dir}", file=sys.stderr)
        sys.exit(1)
    dest, _ = _snapshot_name(prusti_dir, args.branch)
    _snapshot_do_build(prusti_dir, dest)
    print(f"Snapshot created at {dest}/")


def _get_toolchain_channel(prusti_dir: Path) -> str:
    """Read rust-toolchain TOML and return the channel name."""
    toolchain_file = prusti_dir / "rust-toolchain"
    with open(toolchain_file, "rb") as f:
        data = tomllib.load(f)
    return data["toolchain"]["channel"]


def _get_toolchain_sysroot(prusti_dir: Path) -> Path:
    """Read rust-toolchain TOML and return the sysroot for the specified channel."""
    channel = _get_toolchain_channel(prusti_dir)
    result = subprocess.run(
        ["rustc", f"+{channel}", "--print", "sysroot"],
        capture_output=True, text=True, check=True,
    )
    return Path(result.stdout.strip())


def cmd_full(args):
    prusti_dir = Path(args.prusti_dir).expanduser()
    if not prusti_dir.is_dir():
        print(f"Error: prusti directory not found at {prusti_dir}", file=sys.stderr)
        sys.exit(1)

    dest, name = _snapshot_name(prusti_dir, args.branch)
    db = args.db or f"prusti-{name}.db"
    if Path(db).exists():
        print(f"Error: database {db} already exists; aborting.", file=sys.stderr)
        sys.exit(1)

    _snapshot_do_build(prusti_dir, dest)
    print(f"Snapshot created at {dest}/")
    prusti_rustc = dest / "prusti-rustc"

    clean_passing = args.dest_dir is None
    dest_dir = args.dest_dir or "tests/"

    if clean_passing:
        p = Path(dest_dir)
        if p.is_dir():
            for f in p.glob("*.rs"):
                f.unlink()

    args.dest_dir = dest_dir

    for lib in ["alloc", "core"]:
        for d, pattern in [(Path(f"{lib}/snippets/"), "*.rs"), (Path(f"{lib}/bin/"), "*")]:
            if d.is_dir():
                for f in d.glob(pattern):
                    if f.is_file():
                        f.unlink()

    channel = _get_toolchain_channel(prusti_dir)
    sysroot = _get_toolchain_sysroot(prusti_dir)
    lib_base = sysroot / "lib" / "rustlib" / "src" / "rust" / "library"

    for lib in ["alloc", "core"]:
        print(f"=== {lib} ===")
        cmd_extract(argparse.Namespace(library=lib, source_dir=str(lib_base / lib), output_dir=f"{lib}/snippets/", channel=channel))
        cmd_compile(argparse.Namespace(snippets_dir=f"{lib}/snippets/", bin_dir=f"{lib}/bin/", prusti_rustc=str(prusti_rustc), verbose=args.verbose, channel=channel))
        cmd_copy_passing(argparse.Namespace(snippets_dir=f"{lib}/snippets/", bin_dir=f"{lib}/bin/", dest_dir=args.dest_dir))

    for lib in ["alloc", "core"]:
        for f in Path(f"{lib}/bin/").glob("*"):
            if f.is_file():
                f.unlink()

    cmd_prusti(argparse.Namespace(prusti_rustc=str(prusti_rustc), dest_dir=args.dest_dir, file=None, db=db, timeout=args.timeout, server=args.server, verbose=args.verbose))


def cmd_ci(args):
    prusti_dir = Path(args.prusti_dir).expanduser()
    if not prusti_dir.is_dir():
        print(f"Error: prusti directory not found at {prusti_dir}", file=sys.stderr)
        sys.exit(1)

    print("Building Prusti...")
    result = subprocess.run(["./x.py", "build"], cwd=str(prusti_dir))
    if result.returncode != 0:
        print("Error: Prusti build failed.", file=sys.stderr)
        sys.exit(1)

    prusti_rustc = prusti_dir / "target" / "debug" / "prusti-rustc"
    if not prusti_rustc.is_file():
        print(f"Error: prusti-rustc not found at {prusti_rustc}", file=sys.stderr)
        sys.exit(1)

    channel = _get_toolchain_channel(prusti_dir)
    sysroot = _get_toolchain_sysroot(prusti_dir)
    lib_base = sysroot / "lib" / "rustlib" / "src" / "rust" / "library"

    with tempfile.TemporaryDirectory(dir=".") as tmpdir:
        tmp = Path(tmpdir)
        tests_dir = str(tmp / "tests")
        db = str(tmp / "results.db")

        for lib in ["alloc", "core"]:
            snippets = str(tmp / lib / "snippets")
            bins = str(tmp / lib / "bin")
            print(f"=== {lib} ===")
            cmd_extract(argparse.Namespace(library=lib, source_dir=str(lib_base / lib), output_dir=snippets, channel=channel))
            cmd_compile(argparse.Namespace(snippets_dir=snippets, bin_dir=bins, prusti_rustc=str(prusti_rustc), verbose=True, channel=channel))
            cmd_copy_passing(argparse.Namespace(snippets_dir=snippets, bin_dir=bins, dest_dir=tests_dir))

        cmd_prusti(argparse.Namespace(
            prusti_rustc=str(prusti_rustc), dest_dir=tests_dir, file=None,
            db=db, timeout=args.timeout, server=args.server, verbose=False,
        ))
        cmd_analyze(argparse.Namespace(db=db))


def cmd_analyze(args):
    db_path = Path(args.db)
    if not db_path.exists():
        print(f"Error: database {db_path} not found.", file=sys.stderr)
        sys.exit(1)

    df = analysis.transform(analysis.load_dbs([db_path]))

    n_success = len(df.filter(pl.col("success") == "success"))
    n_timeout = len(df.filter(pl.col("success") == "timeout"))
    n_fail = len(df.filter(pl.col("success") == "fail"))

    print("=== Stdlib Doctest Analysis ===\n")
    print(f"Total: {len(df)}  |  Success: {n_success}  |  Fail: {n_fail}  |  Timeout: {n_timeout}\n")

    failures = df.filter(pl.col("success") == "fail")
    counts = (
        failures.group_by("category")
        .agg(pl.len().alias("count"))
        .sort("count", descending=True)
    )

    col_width = 80
    print(f"{'Failure Category':<{col_width}}  Count")
    print("-" * (col_width + 8))
    for row in counts.iter_rows(named=True):
        cat = row["category"]
        display = cat if len(cat) <= col_width else cat[:col_width - 3] + "..."
        print(f"{display:<{col_width}}  {row['count']}")
    print("-" * (col_width + 8))
    print(f"{'Total failures':<{col_width}}  {n_fail}\n")

    print("=== Files by Category ===\n")
    for row in counts.iter_rows(named=True):
        cat = row["category"]
        files = (
            failures.filter(pl.col("category") == cat)
            .select("file_name")
            .sort("file_name")
            .to_series()
            .to_list()
        )
        print(f"--- {cat} ({len(files)} files) ---")
        for f in files:
            print(f)
        print()


def main():
    parser = argparse.ArgumentParser(description="Rust doctest extractor, compiler, and runner.")
    subparsers = parser.add_subparsers(dest="command", required=True)

    # extract subcommand
    p_extract = subparsers.add_parser("extract", help="Extract doctests from Rust source files.")
    p_extract.add_argument("--src-dir", required=True, dest="source_dir", help="Path to the library's Cargo project directory (e.g., toolchain library/core)")
    p_extract.add_argument("--snippets-dir", required=True, dest="output_dir", help="Directory to write extracted .rs snippets into")
    p_extract.add_argument("--library", required=True, dest="library", help="Name of the library, e.g. 'core' or 'alloc'")
    p_extract.set_defaults(func=cmd_extract)

    # compile subcommand
    p_compile = subparsers.add_parser("compile", help="Compile extracted .rs snippets with rustc.")
    p_compile.add_argument("--snippets-dir", required=True, dest="snippets_dir", help="Directory containing extracted .rs snippets")
    p_compile.add_argument("--bin-dir", required=True, dest="bin_dir", help="Directory to write compiled binaries into")
    p_compile.add_argument("--prusti", required=True, dest="prusti_rustc", help="Path to prusti-rustc; runs PRUSTI_NO_VERIFY pre-check and rejects snippets that fail it")
    p_compile.set_defaults(func=cmd_compile)

    # run subcommand
    p_run = subparsers.add_parser("run", help="Run compiled snippet binaries.")
    p_run.add_argument("--bin-dir", required=True, dest="bin_dir", help="Directory containing compiled binaries")
    p_run.set_defaults(func=cmd_run)

    # copy-passing subcommand
    p_copy = subparsers.add_parser("copy-passing", help="Copy snippets that compiled and ran successfully to a new directory.")
    p_copy.add_argument("--snippets-dir", required=True, dest="snippets_dir", help="Directory containing extracted .rs snippets")
    p_copy.add_argument("--bin-dir", required=True, dest="bin_dir", help="Directory containing compiled binaries")
    p_copy.add_argument("--passing-dir", required=True, dest="dest_dir", help="Directory to copy passing snippets into")
    p_copy.set_defaults(func=cmd_copy_passing)

    # prusti subcommand
    p_prusti = subparsers.add_parser("prusti", help="Run prusti-rustc on snippets.")
    p_prusti.add_argument("--prusti", required=True, dest="prusti_rustc", help="Path to the prusti-rustc executable")
    prusti_target = p_prusti.add_mutually_exclusive_group(required=True)
    prusti_target.add_argument("--passing-dir", dest="dest_dir", help="Directory containing .rs snippets to verify")
    prusti_target.add_argument("--file", help="Single .rs file to verify")
    p_prusti.add_argument("--timeout", type=int, default=60, help="Timeout per file in seconds (default: 60)")
    p_prusti.add_argument("--db", help="Path to SQLite database (default: prusti_<timestamp>.db)")
    p_prusti.add_argument("--server", action="store_true", help=f"Use prusti-server ({PRUSTI_SERVER_COUNT} instances, one worker each)")
    p_prusti.add_argument("--verbose", action="store_true", help="Print Prusti output for failed files at the end")
    p_prusti.set_defaults(func=cmd_prusti)

    # compile subcommand (verbose flag)
    # (p_compile defined above — add verbose there too)
    p_compile.add_argument("--verbose", action="store_true", help="Print compiler output for failed files")

    # full subcommand
    p_full = subparsers.add_parser("full", help="Snapshot Prusti, extract, compile, and verify alloc+core doctests.")
    p_full.add_argument("--prusti-dir", default="~/prusti-dev", dest="prusti_dir", help="Path to prusti-dev checkout (default: ~/prusti-dev)")
    p_full.add_argument("--branch", default=None, help="Branch label for snapshot and DB name (e.g. fix_ConstEnc)")
    p_full.add_argument("--passing-dir", default=None, dest="dest_dir", help="Directory to copy passing snippets into (default: tests/, cleaned before use)")
    p_full.add_argument("--timeout", type=int, default=60, help="Timeout per file in seconds (default: 60)")
    p_full.add_argument("--db", help="Path to SQLite database (default: prusti-<name>.db)")
    p_full.add_argument("--noserver", action="store_false", dest="server", help=f"Disable prusti-server (enabled by default, {PRUSTI_SERVER_COUNT} instances)")
    p_full.add_argument("--verbose", action="store_true", help="Print compiler and Prusti output for failed files")
    p_full.set_defaults(func=cmd_full, server=True)

    # snapshot subcommand
    p_snapshot = subparsers.add_parser("snapshot", help="Build Prusti and create a self-contained snapshot directory.")
    p_snapshot.add_argument("--prusti-dir", default="~/prusti-dev", dest="prusti_dir",
                            help="Path to prusti-dev checkout (default: ~/progs/prusti-dev)")
    p_snapshot.add_argument("--branch", default=None, help="Branch label to include in snapshot name (e.g. fix_ConstEnc)")
    p_snapshot.set_defaults(func=cmd_snapshot)

    # ci subcommand
    p_ci = subparsers.add_parser("ci", help="Extract, compile, verify, and analyze stdlib doctests (no Prusti build).")
    p_ci.add_argument("--prusti-dir", default=".", dest="prusti_dir", help="Path to prusti-dev checkout (default: current directory)")
    p_ci.add_argument("--timeout", type=int, default=60, help="Timeout per file in seconds (default: 60)")
    p_ci.add_argument("--noserver", action="store_false", dest="server", help=f"Disable prusti-server (enabled by default, {PRUSTI_SERVER_COUNT} instances)")
    p_ci.set_defaults(func=cmd_ci, server=True)

    # analyze subcommand
    p_analyze = subparsers.add_parser("analyze", help="Analyze a Prusti results database and print categorized summary.")
    p_analyze.add_argument("--db", required=True, help="Path to SQLite results database")
    p_analyze.set_defaults(func=cmd_analyze)

    args = parser.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
