#!/usr/bin/env python3
"""Offline build of the shipped Lean closure with plain `lean` (no lake, no network).

    py build_closure.py --src <reproducibility/lean> --out <build dir> --lean <lean executable>
                        --path "<dir>;<dir>;..." [--jobs 2] [--timeout 3600] [--gate <gate.py>] [--roots M1 M2 ...]

`--path` lists the directories that hold the compiled Mathlib packages (each `<package>/.lake/build/lib/lean`), as `lake env`
would put them in LEAN_PATH.  The modules of `Erdos/Proofs/` reachable from the roots (default: `Erdos.Proofs.P1186LowMain`,
`Erdos.Proofs.P1186M2Main`) are compiled in dependency order, each with
`lean -R <src> -o <out>/<Module>.olean -i <out>/<Module>.ilean -DautoImplicit=false -DrelaxedAutoImplicit=false
 -Dpp.unicode.fun=true -Dwarn.sorry=false <file>`
which are the options `lakefile.toml` sets.  A module is skipped when its `.olean` is newer than its source and than the
`.olean` of every import (so the run can be resumed).  One JSON line per module is appended to `<out>/build_log.jsonl`.
The build stops at the first failure and exits non-zero.  `--gate` runs each compile through a machine-wide slot gate (used on
the shared research machine; not needed elsewhere).

This is a convenience for a machine that already has compiled Mathlib; the canonical route is `lake build Erdos` in
`reproducibility/lean` (README.md).
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import threading
import time
from pathlib import Path

IMPORT = re.compile(r"^import\s+(Erdos\.\S+)\s*$", re.M)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--src", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--lean", required=True)
    ap.add_argument("--path", required=True)
    ap.add_argument("--jobs", type=int, default=1)
    ap.add_argument("--timeout", type=int, default=3600)
    ap.add_argument("--gate", default=None)
    ap.add_argument("--roots", nargs="*", default=["Erdos.Proofs.P1186LowMain", "Erdos.Proofs.P1186M2Main"])
    a = ap.parse_args()
    src, out = Path(a.src).resolve(), Path(a.out).resolve()
    out.mkdir(parents=True, exist_ok=True)

    def file_of(m: str) -> Path:
        return src / (m.replace(".", "/") + ".lean")

    deps: dict[str, list[str]] = {}
    stack = list(a.roots)
    while stack:
        m = stack.pop()
        if m in deps:
            continue
        deps[m] = IMPORT.findall(file_of(m).read_text(encoding="utf-8"))
        stack.extend(deps[m])
    print(f"{len(deps)} modules in the closure of {a.roots}", flush=True)

    def olean(m: str) -> Path:
        return out / (m.replace(".", "/") + ".olean")

    def fresh(m: str) -> bool:
        o = olean(m)
        if not o.exists():
            return False
        t = o.stat().st_mtime
        return t >= file_of(m).stat().st_mtime and all(t >= olean(d).stat().st_mtime for d in deps[m] if olean(d).exists())

    env = dict(os.environ)
    env["LEAN_PATH"] = os.pathsep.join([str(out), a.path])
    log = out / "build_log.jsonl"
    lock = threading.Lock()
    done: set[str] = set()
    running: set[str] = set()
    failed: list[str] = []
    cv = threading.Condition(lock)

    def compile_one(m: str) -> tuple[int, float]:
        o = olean(m)
        o.parent.mkdir(parents=True, exist_ok=True)
        cmd = [a.lean, "-R", str(src), "-o", str(o), "-i", str(o.with_suffix(".ilean")),
               "-DautoImplicit=false", "-DrelaxedAutoImplicit=false", "-Dpp.unicode.fun=true", "-Dwarn.sorry=false",
               str(file_of(m))]
        if a.gate:
            cmd = [sys.executable, a.gate, "--timeout", str(a.timeout), "--"] + cmd
        t0 = time.time()
        p = subprocess.run(cmd, env=env, capture_output=True, text=True, encoding="utf-8", errors="replace")
        dt = time.time() - t0
        if p.returncode != 0:
            (out / (m + ".err.txt")).write_text(p.stdout + "\n" + p.stderr, encoding="utf-8")
            if o.exists():
                o.unlink()
        return p.returncode, dt

    def worker() -> None:
        while True:
            with cv:
                while True:
                    if failed or len(done) == len(deps):
                        return
                    ready = [m for m in sorted(deps) if m not in done and m not in running
                             and all(d in done for d in deps[m])]
                    if ready:
                        m = ready[0]
                        running.add(m)
                        break
                    cv.wait(timeout=5)
            if fresh(m):
                rc, dt, skipped = 0, 0.0, True
            else:
                rc, dt = compile_one(m)
                skipped = False
            with cv:
                running.discard(m)
                if rc == 0:
                    done.add(m)
                else:
                    failed.append(m)
                with log.open("a", encoding="utf-8") as f:
                    f.write(json.dumps({"module": m, "rc": rc, "seconds": round(dt, 1), "skipped": skipped,
                                        "t": time.strftime("%H:%M:%S")}) + "\n")
                print(f"[{len(done)}/{len(deps)}] {m} rc={rc} {dt:.0f}s{' (fresh)' if skipped else ''}", flush=True)
                cv.notify_all()

    threads = [threading.Thread(target=worker) for _ in range(max(1, a.jobs))]
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    if failed:
        print("FAILED:", failed, flush=True)
        return 1
    print("BUILD OK", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
