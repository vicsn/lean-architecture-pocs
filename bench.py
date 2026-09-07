#!/usr/bin/env python3
"""Compile, measure, and test 10x claims. No third-party Python packages.

GNU time (`/usr/bin/time` on Linux, Homebrew `gtime` on macOS) and Lean 4.33.1 are required.
All measured successes require real compiler exit status 0. Limits and failures
are reported, not converted into fictitious ratios. No network calls are made
by this script itself (an elan shim can install the requested toolchain).
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import re
import shutil
import signal
import statistics
import subprocess
import sys
import time
import threading
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from generate import PIN, make_pair, make_fanout, write

ROOT = Path(__file__).resolve().parent
GRIDS = {
    "conversion": [256, 1024, 4096, 16384, 65536],
    "tree": [6, 8, 10, 12, 14, 16, 18, 20],
    "instances": [16, 64, 256, 1024, 4096],
    "opacity": [128],
}
TARGETS = {
    "conversion": ["wall_s"],
    "tree": ["peak_rss_kib", "serialized_parent_bytes"],
    "instances": ["elaboration_heartbeats_raw"],
    "opacity": [],
}


_GNU_TIME: str | None = None


def find_gnu_time() -> str:
    """Return a GNU time binary that accepts `-f '%U %S %M %x'`."""
    names = []
    env = os.environ.get("GNU_TIME")
    if env:
        names.append(env)
    names.extend(["gtime", "/opt/homebrew/bin/gtime", "/usr/local/bin/gtime", "/usr/bin/time"])
    seen: set[str] = set()
    for name in names:
        path = name if Path(name).is_file() else shutil.which(name)
        if not path or path in seen:
            continue
        seen.add(path)
        probe = subprocess.run([path, "-f", "%U %S %M %x", "-o", os.devnull, "true"],
                               capture_output=True, text=True)
        if probe.returncode == 0:
            return path
    raise RuntimeError(
        "GNU time is required (Linux /usr/bin/time or Homebrew gnu-time as gtime). "
        "BSD /usr/bin/time on macOS is not sufficient.")


def gnu_time() -> str:
    global _GNU_TIME
    if _GNU_TIME is None:
        _GNU_TIME = find_gnu_time()
    return _GNU_TIME


def atomic_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temp = path.with_suffix(path.suffix + ".tmp")
    temp.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")
    temp.replace(path)


def artifact_files(d: Path, stem: str) -> list[Path]:
    # Include split modern .olean products; don't mistake the main file for
    # the entire serialized proof. No .lean source or timing logs are counted.
    return sorted(p for p in d.glob(stem + ".*") if p.is_file() and
                  (p.name.startswith(stem + ".olean") or
                   p.name in {stem + ".ilean", stem + ".ir"}))


def artifact_size(d: Path, stem: str) -> int:
    return sum(p.stat().st_size for p in artifact_files(d, stem))


def run_process(cmd: list[str], cwd: Path, log: Path, timeout: float,
                env: dict[str, str] | None = None) -> dict:
    """Measure one command. Killing its process group also stops descendants."""
    log.parent.mkdir(parents=True, exist_ok=True)
    stdout = log.with_suffix(".stdout.txt")
    stderr = log.with_suffix(".stderr.txt")
    timing = log.with_suffix(".time.txt")
    wrapped = [gnu_time(), "-f", "%U %S %M %x", "-o", str(timing), *cmd]
    result: dict = {"command": cmd, "cwd": str(cwd), "stdout": str(stdout),
                    "stderr": str(stderr), "status": "NOT_RUN"}
    with stdout.open("wb") as out, stderr.open("wb") as err:
        begin = time.perf_counter_ns()
        proc = subprocess.Popen(wrapped, cwd=cwd, env=env, stdout=out, stderr=err,
                                start_new_session=True)
        expired = threading.Event()
        def kill_group() -> None:
            expired.set()
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        watchdog = threading.Timer(timeout, kill_group)
        watchdog.daemon = True
        watchdog.start()
        try:
            proc.wait()  # Blocking wait: no timeout-polling quantization of timings.
        finally:
            watchdog.cancel()
        result["wall_s"] = (time.perf_counter_ns() - begin) / 1e9
        result["exit_code"] = proc.returncode
        result["status"] = "TIMEOUT" if expired.is_set() else "OK" if proc.returncode == 0 else "FAILED"
    if timing.exists():
        # GNU time may prepend a diagnostic for an unsuccessful command.
        for line in reversed(timing.read_text(errors="replace").splitlines()):
            if re.fullmatch(r"[0-9.]+ [0-9.]+ [0-9]+ [0-9]+", line.strip()):
                u, s, rss, _ = line.split()
                result.update(user_cpu_s=float(u), system_cpu_s=float(s),
                              cpu_s=float(u) + float(s), peak_rss_kib=int(rss))
                break
    return result


def require_ok(result: dict, stage: str) -> None:
    if result["status"] != "OK":
        raise RuntimeError(f"{stage}: {result['status']}; see {result['stderr']} "
                           f"and {result['stdout']}")


def median_measurements(runs: list[dict]) -> dict:
    if not runs or any(r["status"] != "OK" for r in runs):
        raise ValueError("medians require a nonempty set of successful runs")
    keys = ["wall_s", "cpu_s", "peak_rss_kib", "serialized_parent_bytes"]
    return {key: statistics.median(r[key] for r in runs)
            for key in keys if all(key in r for r in runs)}


def ratio(bad: float | int | None, good: float | int | None) -> float | None:
    return bad / good if bad is not None and good is not None and good > 0 else None


class Runner:
    def __init__(self, args: argparse.Namespace, lean: str):
        self.args = args
        self.lean = lean
        # Small thread count and the same resource limits for both variants.
        self.flags = ["-j", "1", "-s", str(args.stack_kib), "-M", str(args.memory_mib),
                      "-D", "Elab.async=false"]

    def compile(self, d: Path, module: str, label: str) -> dict:
        for p in artifact_files(d, module):
            p.unlink()
        env = os.environ.copy()
        env["LEAN_PATH"] = str(d) + (os.pathsep + env["LEAN_PATH"] if env.get("LEAN_PATH") else "")
        cmd = [self.lean, *self.flags, "-o", module + ".olean", module + ".lean"]
        res = run_process(cmd, d, d / "logs" / label, self.args.timeout, env)
        if res["status"] == "OK":
            if not (d / (module + ".olean")).is_file():
                res["status"] = "MISSING_OUTPUT"
            else:
                res["serialized_parent_bytes"] = artifact_size(d, module)
        return res

    def pair(self, case: str, size: int) -> dict:
        d = self.args.work / case / str(size)
        metadata = make_pair(d, case, size, self.args.parent_repetitions)
        record: dict = {"case": case, "size": size, "metadata": metadata,
                        "status": "RUNNING", "variants": {}}
        try:
            for variant in ("bad", "good"):
                v = d / variant
                data: dict = {"prebuild": [], "parent_runs": [], "baseline_runs": [],
                              "probe_runs": [], "source_sha256": {}}
                record["variants"][variant] = data
                for module in ("Common", "Child"):
                    res = self.compile(v, module, "prebuild_" + module)
                    data["prebuild"].append(res)
                    require_ok(res, f"{case}/{variant}/{module}")
                for path in sorted(v.glob("*.lean")):
                    data["source_sha256"][path.name] = hashlib.sha256(path.read_bytes()).hexdigest()
                # Warm the OS page cache. This is NOT a cold-cache benchmark.
                for module in ("Baseline", "Parent"):
                    res = self.compile(v, module, "warmup_" + module)
                    data["warmup_" + module] = res
                    require_ok(res, f"warmup {case}/{variant}/{module}")
            # Alternate the order to reduce systematic first/second-run bias.
            for k in range(self.args.repeats):
                for variant in (("bad", "good") if k % 2 == 0 else ("good", "bad")):
                    v = d / variant
                    data = record["variants"][variant]
                    for module, key in (("Baseline", "baseline_runs"), ("Parent", "parent_runs")):
                        res = self.compile(v, module, f"repeat{k}_{module}")
                        data[key].append(res)
                        require_ok(res, f"measure {case}/{variant}/{module}")
            for variant in ("bad", "good"):
                v = d / variant
                data = record["variants"][variant]
                data["parent_median"] = median_measurements(data["parent_runs"])
                data["baseline_median"] = median_measurements(data["baseline_runs"])
                data["diagnostic_parent_minus_baseline_wall_s"] = (
                    data["parent_median"]["wall_s"] - data["baseline_median"]["wall_s"])
                # Instrumentation is deliberately absent from primary time/RSS runs.
                probe_build = self.compile(v, "Metrics", "prebuild_Metrics")
                data["metrics_prebuild"] = probe_build
                require_ok(probe_build, f"{case}/{variant}/Metrics")
                expected = self.args.parent_repetitions if case == "instances" else 1
                totals = []
                for k in range(self.args.repeats):
                    res = self.compile(v, "Probe", f"repeat{k}_Probe")
                    data["probe_runs"].append(res)
                    require_ok(res, f"{case}/{variant}/Probe")
                    text = Path(res["stdout"]).read_text(errors="replace") + Path(res["stderr"]).read_text(errors="replace")
                    counts = [int(x) for x in re.findall(r"BENCH_HEARTBEATS_RAW=(\d+)", text)]
                    if len(counts) != expected:
                        raise RuntimeError(f"Expected {expected} heartbeat records, got {len(counts)}: {v}")
                    res["elaboration_heartbeats_raw"] = sum(counts)
                    totals.append(sum(counts))
                data["parent_median"]["elaboration_heartbeats_raw"] = statistics.median(totals)
                # Separate logical audit; it is not included in timing or size.
                names = re.findall(r"^theorem (parent\d*)\b", (v / "Parent.lean").read_text(), re.M)
                write(v / "Audit.lean", "import Parent\n\n" +
                      "\n".join(f"#print axioms {name}" for name in names) + "\n")
                audit = self.compile(v, "Audit", "audit")
                data["audit"] = audit
                require_ok(audit, f"{case}/{variant}/Audit")
                text = Path(audit["stdout"]).read_text(errors="replace") + Path(audit["stderr"]).read_text(errors="replace")
                if "sorryAx" in text or "Lean.ofReduceBool" in text:
                    raise RuntimeError("Audit found an admitted or native-decision axiom")
            bad = record["variants"]["bad"]["parent_median"]
            good = record["variants"]["good"]["parent_median"]
            record["bad_over_good"] = {k: ratio(bad.get(k), good.get(k)) for k in sorted(set(bad) | set(good))}
            record["target_metrics"] = TARGETS[case]
            record["threshold"] = self.args.threshold
            record["threshold_met_by_metric"] = {
                k: record["bad_over_good"].get(k) is not None and
                   record["bad_over_good"][k] >= self.args.threshold for k in TARGETS[case]}
            record["all_targets_met"] = bool(TARGETS[case]) and all(record["threshold_met_by_metric"].values())
            metadata["lean_validation"] = "COMPILED_AND_PARENT_AXIOM_AUDITED"
            atomic_json(d / "case.json", metadata)
            record["status"] = "OK"
        except (RuntimeError, OSError, ValueError) as exc:
            metadata["lean_validation"] = "ATTEMPTED_NOT_VALIDATED"
            atomic_json(d / "case.json", metadata)
            record["status"] = "FAILED_OR_CENSORED"
            record["error"] = str(exc)
            record["all_targets_met"] = False
        atomic_json(d / "measurement.json", record)
        return record


def snapshot_oleans(d: Path) -> dict[str, int]:
    result: dict[str, int] = {}
    build = d / ".lake/build/lib/lean"
    for path in build.rglob("*.olean"):
        module = ".".join(path.relative_to(build).with_suffix("").parts)
        result[module] = path.stat().st_mtime_ns
    return result


def measure_fanout(args: argparse.Namespace, lake: str) -> dict:
    root = args.work / "fanout"
    static = make_fanout(root, args.consumers)
    result: dict = {"case": "fanout", "static": static, "variants": {}, "status": "RUNNING"}
    try:
        for variant in ("bad", "good"):
            d = root / variant
            # This is a generated, dependency-free project under --work.
            shutil.rmtree(d / ".lake", ignore_errors=True)
            data: dict = {"rebuilds": []}
            result["variants"][variant] = data
            clean = run_process([lake, "build"], d, d / "logs/clean", args.timeout)
            data["clean_build"] = clean
            require_ok(clean, "fanout clean build")
            # Unchanged builds should not rewrite compilation products.
            before = snapshot_oleans(d)
            noop = run_process([lake, "build"], d, d / "logs/noop", args.timeout)
            data["noop_build"] = noop
            require_ok(noop, "fanout no-op build")
            if snapshot_oleans(d) != before:
                raise RuntimeError("No-op Lake build rewrote .olean files; cannot use mtime accounting")
            changed = d / static["variants"][variant]["changed_file"]
            for k in range(args.repeats):
                before = snapshot_oleans(d)
                # An actual exported theorem-statement edit, not merely touch().
                content = changed.read_text()
                content = re.sub(r"theorem auxiliary : 0 < \d+ := by decide",
                                 f"theorem auxiliary : 0 < {11+k} := by decide", content)
                time.sleep(0.02)
                changed.write_text(content)
                run = run_process([lake, "build"], d, d / f"logs/rebuild{k}", args.timeout)
                require_ok(run, "fanout dirty build")
                after = snapshot_oleans(d)
                if not after:
                    raise RuntimeError("No .olean files found at the expected Lake output path")
                modified = sorted(m for m, ts in after.items() if before.get(m) != ts)
                run["rewritten_olean_modules"] = modified
                run["rewritten_parent_count"] = sum(m.startswith("Bench.Parent") for m in modified)
                # This is an observable artifact-rewrite count. Logs retain actual jobs.
                # Build systems may avoid rewriting unchanged outputs; don't hide that.
                data["rebuilds"].append(run)
            data["median_rewritten_parent_count"] = statistics.median(
                r["rewritten_parent_count"] for r in data["rebuilds"])
            data["median_dirty_wall_s"] = statistics.median(r["wall_s"] for r in data["rebuilds"])
        bad = result["variants"]["bad"]
        good = result["variants"]["good"]
        result["measured_rewritten_parent_ratio"] = ratio(
            bad["median_rewritten_parent_count"], good["median_rewritten_parent_count"])
        result["measured_dirty_wall_ratio"] = ratio(bad["median_dirty_wall_s"], good["median_dirty_wall_s"])
        r = result["measured_rewritten_parent_ratio"]
        result["threshold_met"] = r is not None and r >= args.threshold
        result["status"] = "OK"
    except (RuntimeError, OSError, ValueError) as exc:
        result["status"] = "FAILED_OR_CENSORED"
        result["error"] = str(exc)
    atomic_json(root / "measurement.json", result)
    return result


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--case", choices=["all", "conversion", "tree", "instances", "fanout", "opacity"], default="all")
    p.add_argument("--smoke", action="store_true", help="small compile checks, not 10x certification")
    p.add_argument("--sizes", help="comma-separated sizes, only with a single non-fanout case")
    p.add_argument("--repeats", type=int, default=3)
    p.add_argument("--parent-repetitions", type=int, default=16)
    p.add_argument("--consumers", type=int, default=32)
    p.add_argument("--timeout", type=float, default=180.0, help="seconds per subprocess")
    p.add_argument("--memory-mib", type=int, default=4096)
    p.add_argument("--stack-kib", type=int, default=131072)
    p.add_argument("--threshold", type=float, default=10.0)
    p.add_argument("--lean", default="lean")
    p.add_argument("--lake", default="lake")
    p.add_argument("--allow-version-mismatch", action="store_true")
    p.add_argument("--work", type=Path, default=ROOT / "work")
    p.add_argument("--out", type=Path, default=ROOT / "results.json")
    p.add_argument("--keep-sweeping", action="store_true", help="continue after a successful threshold")
    p.add_argument("--require-targets", action="store_true", help="exit nonzero unless every selected positive case meets 10x")
    args = p.parse_args()
    if args.repeats < 1 or args.parent_repetitions < 1 or args.timeout <= 0:
        p.error("repeat counts and timeout must be positive")
    if args.threshold <= 0 or args.memory_mib < 128 or args.stack_kib < 1024 or args.consumers < 2:
        p.error("invalid threshold, memory, stack, or consumer count")
    if args.sizes and args.case in {"all", "fanout"}:
        p.error("--sizes requires one of conversion, tree, instances, opacity")
    if args.smoke and args.require_targets:
        p.error("smoke checks do not certify 10x claims")
    args.work = args.work.resolve()
    args.out = args.out.resolve()
    report: dict = {
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "toolchain_pin": PIN, "host": platform.platform(),
        "python": sys.version, "cpu_count": os.cpu_count(),
        "method": "numeric pairs: warm-cache, precompiled children, single-threaded Lean, median whole-process wall/RSS; fanout: default Lake scheduler",
        "arguments": {k: str(v) if isinstance(v, Path) else v for k, v in vars(args).items()},
        "status": "STARTING", "measurements": [],
    }
    try:
        report["gnu_time"] = gnu_time()
        lean = shutil.which(args.lean)
        if not lean:
            raise RuntimeError(f"Lean is not installed or not on PATH: {args.lean}. No Lean measurements were performed.")
        # Resolve the elan shim using the suite's pinned toolchain, before timings.
        version = subprocess.run([lean, "--version"], cwd=ROOT, text=True, capture_output=True,
                                 timeout=args.timeout)
        if version.returncode:
            raise RuntimeError("lean --version failed: " + version.stderr)
        report["lean_version"] = version.stdout.strip()
        if not re.search(r"\bversion 4\.33\.1\b", version.stdout, re.I) and not args.allow_version_mismatch:
            raise RuntimeError("Wrong Lean version; use the pin or explicitly allow and report a mismatch")
        runner = Runner(args, lean)
        cases = list(GRIDS) + ["fanout"] if args.case == "all" else [args.case]
        report["status"] = "RUNNING"
        atomic_json(args.out, report)
        for case in cases:
            if case == "fanout":
                lake = shutil.which(args.lake)
                if not lake:
                    raise RuntimeError("Lake is required for the fanout experiment")
                rec = measure_fanout(args, lake)
                report["measurements"].append(rec)
                print(f"fanout: {rec['status']}, measured ratio={rec.get('measured_rewritten_parent_ratio')}", flush=True)
                atomic_json(args.out, report)
                continue
            sizes = ([int(x) for x in args.sizes.split(",")] if args.sizes else
                     [dict(conversion=16, tree=3, instances=4, opacity=8)[case]] if args.smoke else GRIDS[case])
            if any(n < 1 for n in sizes):
                raise ValueError("all sizes must be positive")
            for size in sizes:
                print(f"Running {case}, size={size}", flush=True)
                rec = runner.pair(case, size)
                report["measurements"].append(rec)
                print(f"  {rec['status']}; ratios={rec.get('bad_over_good', {})}", flush=True)
                atomic_json(args.out, report)
                if rec["status"] != "OK":
                    # Do not compound an OOM/stack/time failure with a larger job.
                    break
                if rec["all_targets_met"] and not args.keep_sweeping:
                    break
        selected = set(cases) - {"opacity"}
        satisfied = {r["case"] for r in report["measurements"]
                     if r.get("all_targets_met") or (r["case"] == "fanout" and r.get("threshold_met"))}
        report["selected_positive_cases"] = sorted(selected)
        report["cases_with_measured_threshold"] = sorted(satisfied)
        report["all_selected_targets_met"] = selected <= satisfied
        failures = any(r["status"] != "OK" for r in report["measurements"])
        report["status"] = "COMPLETE_WITH_FAILURES" if failures else "COMPLETE"
        atomic_json(args.out, report)
        if failures or (args.require_targets and not report["all_selected_targets_met"]):
            return 2
        return 0
    except (OSError, RuntimeError, ValueError, subprocess.TimeoutExpired) as exc:
        report["status"] = "UNAVAILABLE_OR_FAILED"
        report["error"] = str(exc)
        atomic_json(args.out, report)
        print(str(exc), file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
