#!/usr/bin/env python3
"""Run the host region/zone Criterion benchmarks and export per-operation means.

Usage: python3 tools/run_region_zone_bench.py [Criterion filter/options]
Workload: PREFILL_REGIONS=32 PREFILL_REGION_PAGES=1024 REGION_PAGES=1024
          ZONE_REGIONS=0; affinity: BENCH_CPU.
Region cases time one target insertion/removal after background setup.
ZONE_REGIONS=0 measures empty-zone creation/removal directly.
Each invocation writes a fresh target/region-zone-bench/runs/<id>/ directory.
"""

import csv
import datetime
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import re
import shlex
import subprocess
import sys
import tempfile


TOOLCHAIN = "1.95.0"
CRITERION_VERSION = "0.8.2"
BENCHMARK = "region_zone_ops"
REPOSITORY = Path(__file__).resolve().parent.parent
TARGET = REPOSITORY / "target" / "region-zone-bench"


def capture(command):
    result = subprocess.run(command, cwd=REPOSITORY, capture_output=True, text=True)
    if result.returncode:
        detail = result.stderr.strip() or result.stdout.strip()
        raise RuntimeError(f"{shlex.join(command)} failed: {detail}")
    return result.stdout.strip()


def workload_environment():
    if "REGIONS" in os.environ:
        raise ValueError(
            "REGIONS is no longer supported; unset it. Region cases now time "
            "one operation on a prefilled set: use PREFILL_REGIONS for the "
            "background region count, PREFILL_REGION_PAGES for background "
            "region size, and REGION_PAGES for target size."
        )
    values = {}
    for name, default, minimum, maximum in (
        ("PREFILL_REGIONS", "32", 1, 4096),
        ("PREFILL_REGION_PAGES", "1024", 1, 32768),
        ("REGION_PAGES", "1024", 1, 32768),
        ("ZONE_REGIONS", "0", 0, 64),
    ):
        value = os.environ.get(name, default)
        if not re.fullmatch(r"0|[1-9][0-9]{0,4}", value) or not minimum <= int(value) <= maximum:
            raise ValueError(f"{name} must be an integer from {minimum} to {maximum}; got {value!r}")
        values[name] = int(value)
    stride = max(values["PREFILL_REGION_PAGES"], values["REGION_PAGES"])
    if values["PREFILL_REGIONS"] * stride + values["REGION_PAGES"] > 65536:
        raise ValueError(
            "PREFILL_REGIONS * max(PREFILL_REGION_PAGES, REGION_PAGES) + "
            "REGION_PAGES must not exceed 65536 pages (256 MiB address range)"
        )
    if values["ZONE_REGIONS"] * values["REGION_PAGES"] > 32768:
        raise ValueError("ZONE_REGIONS * REGION_PAGES must not exceed 32768 (128 MiB)")
    return values


def benchmark_affinity():
    requested = os.environ.get("BENCH_CPU")
    if not hasattr(os, "sched_getaffinity") or not hasattr(os, "sched_setaffinity"):
        if requested is not None:
            raise ValueError("BENCH_CPU requires sched_getaffinity/sched_setaffinity support")
        return {"supported": False, "allowed_cpus": None, "selected_cpu": None}
    allowed = sorted(os.sched_getaffinity(0))
    if not allowed:
        raise ValueError("the current process has no allowed CPUs")
    if requested is None:
        selected = allowed[0]
    else:
        if not re.fullmatch(r"[0-9]+", requested):
            raise ValueError(f"BENCH_CPU must be a nonnegative CPU number; got {requested!r}")
        selected = int(requested)
        if selected not in allowed:
            raise ValueError(f"BENCH_CPU={selected} is outside the allowed CPUs: {allowed}")
    return {"supported": True, "allowed_cpus": allowed, "selected_cpu": selected}


def source_metadata():
    diff = subprocess.run(
        ["git", "diff", "--binary", "HEAD", "--", "."],
        cwd=REPOSITORY, check=True, capture_output=True,
    ).stdout
    paths = ["Cargo.toml", "Cargo.lock", "src", "benches", ".cargo", "tools/run_region_zone_bench.py"]
    files = {}
    for tracking, options in (("tracked", ["--cached"]), ("untracked", ["--others", "--exclude-standard"])):
        names = capture(["git", "ls-files", *options, "-z", "--", *paths]).split("\0")
        for name in filter(None, names):
            path = REPOSITORY / name
            if not path.exists():
                files[name] = {"tracking": tracking, "missing": True}
                continue
            item = {"tracking": tracking, "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
            if path.is_symlink():
                item["symlink_target"] = os.readlink(path)
            files[name] = item
    digest = hashlib.sha256(json.dumps(files, sort_keys=True).encode()).hexdigest()
    return {
        "branch": capture(["git", "rev-parse", "--abbrev-ref", "HEAD"]),
        "revision": capture(["git", "rev-parse", "HEAD"]),
        "status": capture(["git", "status", "--porcelain=v1"]),
        "tracked_diff_sha256": hashlib.sha256(diff).hexdigest(),
        "source_files_sha256": digest,
        "source_files": files,
    }


def stream_process(command, log, environment, cpu=None, cargo_json=False):
    # This runner is single-threaded. Pin only the benchmark child, leaving
    # Cargo and the user's shell on their original CPU masks.
    def pin_child():
        os.sched_setaffinity(0, {cpu})

    executable = None
    process = subprocess.Popen(
        command, cwd=REPOSITORY, env=environment, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, text=True, errors="replace", bufsize=1,
        preexec_fn=pin_child if cpu is not None else None,
    )
    try:
        for line in process.stdout:
            log.write(line)
            log.flush()
            if cargo_json:
                try:
                    message = json.loads(line)
                except json.JSONDecodeError:
                    print(line, end="", flush=True)
                    continue
                if message.get("reason") == "compiler-artifact":
                    target = message.get("target", {})
                    if target.get("name") == BENCHMARK and "bench" in target.get("kind", []):
                        executable = message.get("executable") or executable
                elif message.get("reason") == "compiler-message":
                    rendered = message.get("message", {}).get("rendered")
                    if rendered:
                        print(rendered, end="", flush=True)
            else:
                print(line, end="", flush=True)
        return process.wait(), executable
    except BaseException:
        if process.poll() is None:
            process.terminate()
            try:
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait()
        raise
    finally:
        process.stdout.close()


def operation_counts(workload):
    region_case = (
        f"prefill_{workload['PREFILL_REGIONS']}_regions_"
        f"{workload['PREFILL_REGION_PAGES']}_pages/"
        f"target_{workload['REGION_PAGES']}_pages"
    )
    zone_case = (
        "empty" if workload["ZONE_REGIONS"] == 0
        else f"{workload['ZONE_REGIONS']}_regions_{workload['REGION_PAGES']}_pages"
    )
    return {
        f"region/insert/{region_case}": 1,
        f"region/remove/after_insert/{region_case}": 1,
        f"zone_memory/create/{zone_case}": 1,
        f"zone_memory/remove/{zone_case}": 1,
    }


def normalized_results(criterion_directory, counts):
    """Read only this invocation's estimates, checking their operation counts."""
    results = {}
    for path in sorted(criterion_directory.glob("**/new/estimates.json")):
        benchmark = json.loads((path.parent / "benchmark.json").read_text())
        benchmark_id = benchmark["full_id"]
        if benchmark_id not in counts:
            raise ValueError(f"unexpected benchmark ID: {benchmark_id}")
        divisor = counts[benchmark_id]
        if benchmark.get("throughput") != {"Elements": divisor}:
            raise ValueError(f"{benchmark_id}: expected throughput Elements({divisor}), got {benchmark.get('throughput')!r}")
        if benchmark_id in results:
            raise ValueError(f"duplicate benchmark ID: {benchmark_id}")
        mean = json.loads(path.read_text())["mean"]
        interval = mean["confidence_interval"]
        numbers = [mean["point_estimate"], interval["lower_bound"], interval["upper_bound"], interval["confidence_level"]]
        if not all(isinstance(value, (float, int)) and math.isfinite(value) for value in numbers):
            raise ValueError(f"{benchmark_id}: invalid mean or confidence interval")
        if not (0 <= numbers[1] <= numbers[0] <= numbers[2] and 0 < numbers[3] < 1):
            raise ValueError(f"{benchmark_id}: invalid mean or confidence interval bounds")
        results[benchmark_id] = {
            "benchmark": benchmark_id,
            "operations_per_iteration": divisor,
            "mean_ns_per_iteration": mean["point_estimate"],
            "mean_ns_per_op": mean["point_estimate"] / divisor,
            "confidence_interval_ns_per_op": {
                "confidence_level": interval["confidence_level"],
                "lower_bound": interval["lower_bound"] / divisor,
                "upper_bound": interval["upper_bound"] / divisor,
            },
            "estimates_file": str(path),
        }
    return [results[name] for name in counts if name in results]


def write_reports(directory, status, results):
    summary = {"status": status, "benchmarks": results}
    (directory / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    with (directory / "results.csv").open("w", newline="") as output:
        writer = csv.writer(output)
        writer.writerow(["status", "benchmark", "operations_per_iteration", "mean_ns_per_iteration", "mean_ns_per_op", "confidence_level", "ci_lower_ns_per_op", "ci_upper_ns_per_op"])
        for result in results:
            ci = result["confidence_interval_ns_per_op"]
            writer.writerow([status, result["benchmark"], result["operations_per_iteration"], result["mean_ns_per_iteration"], result["mean_ns_per_op"], ci["confidence_level"], ci["lower_bound"], ci["upper_bound"]])
    lines = [
        "# VeriHyMem host region/zone benchmark", "", f"Run status: `{status}`.", "",
        "Host software API costs; real ARM barriers/TLB maintenance are excluded.",
        "Each region result times one operation: insertion into a prefilled zone, or removal of the newly inserted target; background setup and cleanup are outside timing.",
        "Region and zone results each describe one operation per iteration; no region or page-count division is applied.",
        "Zone cases named `empty` call add_zone/remove_zone directly with no regions or clear passes; populated cases include mapping/clearing their CPU and IOMMU regions.",
        "The statistics below use Criterion's mean and its confidence interval, both in ns/op.",
        "See [environment.json](environment.json) for source, workload, toolchain and affinity, and [criterion.log](criterion.log) for output.", "",
    ]
    if results:
        lines.extend(["| Operation | Operations/iteration | Mean (ns/op) | Confidence interval (ns/op) |", "|---|---:|---:|---:|"])
        for result in results:
            ci = result["confidence_interval_ns_per_op"]
            lines.append(f"| {result['benchmark']} | {result['operations_per_iteration']} | {result['mean_ns_per_op']:.3f} | {ci['confidence_level'] * 100:g}% [{ci['lower_bound']:.3f}, {ci['upper_bound']:.3f}] |")
    else:
        lines.append("No Criterion estimates were produced by this invocation. Smoke tests, unmatched filters and listing/help modes produce no measurements.")
    (directory / "report.md").write_text("\n".join(lines) + "\n")


def main(arguments):
    if arguments[:1] == ["--"]:
        arguments = arguments[1:]
    workload = workload_environment()
    affinity = benchmark_affinity()
    counts = operation_counts(workload)
    runs = TARGET / "runs"
    runs.mkdir(parents=True, exist_ok=True)
    now = datetime.datetime.now(datetime.timezone.utc)
    directory = Path(tempfile.mkdtemp(prefix=now.strftime("%Y%m%dT%H%M%S.%fZ-"), dir=runs))
    environment = os.environ.copy()
    environment.update({name: str(value) for name, value in workload.items()})
    environment["CRITERION_HOME"] = str(directory / "criterion")
    metadata = {
        "started_at": now.isoformat(), "repository": str(REPOSITORY),
        "criterion_version": CRITERION_VERSION, "criterion_arguments": arguments,
        "workload": workload, "affinity": affinity, "operations_per_iteration": counts,
        "criterion_output_directory": environment["CRITERION_HOME"],
        "uname": platform.uname()._asdict(),
        "build_environment": {
            key: value for key, value in environment.items()
            if key.startswith("CARGO_PROFILE_BENCH_") or key in (
                "RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "CARGO_BUILD_TARGET", "RUSTC", "RUSTC_WRAPPER",
                "RUSTC_WORKSPACE_WRAPPER", "RUSTUP_TOOLCHAIN", "CARGO_BUILD_RUSTFLAGS", "CARGO_HOME",
            ) or (key.startswith("CARGO_TARGET_") and key.endswith(("_RUSTFLAGS", "_LINKER", "_RUNNER")))
        },
        "status": "preparing", "build_exit_code": None, "benchmark_exit_code": None,
    }

    def save_metadata():
        (directory / "environment.json").write_text(json.dumps(metadata, indent=2) + "\n")

    save_metadata()
    print(f"Workload: {workload}\nBenchmark CPU: {affinity['selected_cpu']}\nResults: {directory}", flush=True)
    status = 2
    results = []
    try:
        metadata["source"] = source_metadata()
        cpuinfo = Path("/proc/cpuinfo")
        metadata["cpuinfo"] = cpuinfo.read_text() if cpuinfo.is_file() else None
        lock = (REPOSITORY / "Cargo.lock").read_text()
        version = re.search(r'\[\[package\]\]\s+name = "criterion"\s+version = "([^"]+)"', lock)
        if version is None or version.group(1) != CRITERION_VERSION:
            raise RuntimeError(f"Cargo.lock must pin criterion {CRITERION_VERSION}")
        rustc = capture(["rustc", f"+{TOOLCHAIN}", "-vV"])
        host = next((line[6:] for line in rustc.splitlines() if line.startswith("host: ")), None)
        if not host:
            raise RuntimeError("rustc -vV did not report a host target")
        metadata.update({"rustc": rustc, "cargo": capture(["cargo", f"+{TOOLCHAIN}", "-V"]), "host_target": host})
        command = [
            "cargo", f"+{TOOLCHAIN}", "bench", "--manifest-path", str(REPOSITORY / "Cargo.toml"),
            "--bench", BENCHMARK, "--no-run", "--message-format=json", "--locked", "--offline",
            "--target", host, "--target-dir", str(REPOSITORY / "target"),
        ]
        metadata.update({"build_command": command, "status": "building"})
        save_metadata()
        with (directory / "criterion.log").open("w") as log:
            log.write(f"Build: {shlex.join(command)}\n")
            status, executable = stream_process(command, log, environment, cargo_json=True)
            metadata["build_exit_code"] = status
            if status:
                metadata["status"] = "build_failed"
            elif executable is None:
                metadata["status"] = "missing_benchmark_executable"
                metadata["error"] = "Cargo did not report a benchmark executable"
                status = 1
            else:
                metadata["benchmark_executable_sha256"] = hashlib.sha256(Path(executable).read_bytes()).hexdigest()
                run_command = [executable, *([] if "--bench" in arguments else ["--bench"]), *arguments]
                metadata.update({"benchmark_command": run_command, "status": "running"})
                save_metadata()
                log.write(f"Benchmark: {shlex.join(run_command)}\n")
                status, _ = stream_process(run_command, log, environment, cpu=affinity["selected_cpu"])
                metadata["benchmark_exit_code"] = status
                metadata["status"] = "completed" if status == 0 else "benchmark_failed"
                results = normalized_results(directory / "criterion", counts)
                if status == 0 and not results:
                    metadata["status"] = "test_completed" if "--test" in arguments else "completed_no_measurements"
        metadata["source_after_run"] = source_metadata()
        metadata["source_changed_during_run"] = metadata["source_after_run"] != metadata["source"]
    except KeyboardInterrupt:
        status = 130
        metadata.update({"status": "interrupted", "error": "KeyboardInterrupt"})
    except (OSError, ValueError, RuntimeError, KeyError, subprocess.SubprocessError) as error:
        status = 2
        metadata.update({"status": "failed", "error": str(error)})
        print(f"Region/zone benchmark: {error}", file=sys.stderr)
    finally:
        status = status if status >= 0 else 128 - status
        metadata.update({"exit_code": status, "finished_at": datetime.datetime.now(datetime.timezone.utc).isoformat()})
        save_metadata()
        write_reports(directory, metadata["status"], results)
        for result in results:
            ci = result["confidence_interval_ns_per_op"]
            print(f"{result['benchmark']}: {result['mean_ns_per_op']:.3f} ns/op, {ci['confidence_level'] * 100:g}% CI [{ci['lower_bound']:.3f}, {ci['upper_bound']:.3f}]", flush=True)
        if not results:
            print("No measurements from this invocation; the exported table is empty.", flush=True)
        print(f"Run status: {metadata['status']}\nReport: {directory / 'report.md'}", flush=True)
    return status


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv[1:]))
    except (OSError, ValueError, RuntimeError) as error:
        print(f"Region/zone benchmark: {error}", file=sys.stderr)
        sys.exit(2)
