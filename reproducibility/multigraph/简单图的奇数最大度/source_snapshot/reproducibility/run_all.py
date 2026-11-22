#!/usr/bin/env python3
"""Verify the strong clique certificate using Python and a C17 compiler."""
from datetime import datetime, timezone
from pathlib import Path
import argparse
import hashlib
import json
import os
import platform
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
VERSION = "1.0.0"


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def last_json_line(text):
    for line in reversed(text.splitlines()):
        if line.startswith("{") and line.endswith("}"):
            return json.loads(line)
    raise RuntimeError("Missing machine-readable C result")


def find_compiler(selected):
    if selected:
        path = shutil.which(selected) or selected
        require(Path(path).is_file(), "Selected C compiler does not exist")
        return str(Path(path).resolve())
    for candidate in ("cc", "gcc", "clang"):
        found = shutil.which(candidate)
        if found:
            return str(Path(found).resolve())
    if os.name == "nt":
        candidates = sorted((Path.home() / ".elan/toolchains").glob("*/bin/clang.exe"))
        if candidates:
            return str(candidates[-1])
    raise RuntimeError("C17 compiler required; use --cc PATH (GCC or Clang)")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="New output directory; existing directories are not overwritten")
    parser.add_argument("--cc", help="C17 compiler executable; otherwise detect cc, gcc, clang, or a local Lean clang")
    parser.add_argument("--minimal-windows-crt", action="store_true", help="Use manual CRT declarations for a minimal 64-bit Windows clang without SDK headers")
    args = parser.parse_args()
    require(sys.version_info >= (3, 9), "Python 3.9 or later is required")
    require(__debug__, "Run without -O: the enumeration/model audit uses assertions")
    require(sys.byteorder == "little", "The bundled C audits require a little-endian machine")
    require(platform.architecture()[0] == "64bit", "Use a 64-bit Python/C toolchain")
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    output = (args.output or ROOT / "results" / ("run-" + stamp)).resolve()
    require(not output.exists(), "Output directory already exists; choose a new --output path")
    output.mkdir(parents=True)
    steps = []
    started = time.perf_counter()
    env = os.environ.copy()
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    env["PYTHONOPTIMIZE"] = "0"
    summary = {
        "version": VERSION, "all_passed": False, "exact_bound": "5/4",
        "started_utc": stamp,
        "environment": {"python": platform.python_version(), "platform": platform.platform(), "byteorder": sys.byteorder},
        "steps": steps,
        "scope": "Exact verification of the computational components of the manuscript.",
    }

    def run(name, command, expected=0):
        begin = time.perf_counter()
        result = subprocess.run(command, cwd=ROOT, env=env, text=True, encoding="utf-8", errors="replace", stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (output / (name + ".log")).write_text(result.stdout, encoding="utf-8")
        item = {"check": name, "passed": result.returncode == expected, "return_code": result.returncode, "seconds": time.perf_counter() - begin}
        steps.append(item)
        print(json.dumps(item), flush=True)
        require(item["passed"], name + " failed; inspect its saved log")
        return result.stdout

    def py(script, *arguments):
        return [sys.executable, "-B", str(ROOT / "verifiers" / script), *map(str, arguments)]

    try:
        manifest = json.loads((ROOT / "DATA_SHA256.json").read_text(encoding="utf-8"))
        fingerprints = {}
        for name, expected in manifest["files"].items():
            target = (ROOT / name).resolve()
            require(target.is_relative_to(ROOT / "data"), "Data manifest path escapes data directory")
            raw = target.read_bytes()
            digest = hashlib.sha256(raw).hexdigest()
            require(len(raw) == expected["bytes"] and digest == expected["sha256"], "Data checksum mismatch: " + name)
            fingerprints[name] = digest
        summary["data_sha256"] = fingerprints
        steps.append({"check": "input_checksums", "passed": True, "files": len(fingerprints)})
        compiler = find_compiler(args.cc)
        version = subprocess.run([compiler, "--version"], text=True, encoding="utf-8", errors="replace", stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=True).stdout
        summary["environment"]["c_compiler"] = version.splitlines()[0]
        minimal = args.minimal_windows_crt or (os.name == "nt" and ".elan" in Path(compiler).parts and not (Path(compiler).parent.parent / "include/stdio.h").exists())
        summary["environment"]["minimal_windows_crt"] = bool(minimal)
        compile_flags = ["-std=c17", "-O2", "-Wall", "-Wextra"] + (["-DFGST_NO_C_HEADERS"] if minimal else [])
        build = output / "build"
        build.mkdir()
        executables = {}
        for stem in ("check_index", "check_reverse"):
            executable = build / (stem + (".exe" if os.name == "nt" else ""))
            # Relative paths let Windows GCC use a workspace with non-ASCII parents.
            try:
                output_arg = os.path.relpath(executable, ROOT)
            except ValueError:
                output_arg = str(executable)
            source = Path("verifiers") / (stem + ".c")
            run("compile_" + stem, [compiler, *compile_flags, str(source), "-o", output_arg])
            executables[stem] = executable
        summary["six_position_index"] = last_json_line(
            run("six_position_index", [str(executables["check_index"])])
        )
        run("low_orders_and_bases", py("check_low_orders_and_bases.py", "--output", output / "low_orders_and_bases.json"))
        summary["all_coefficients"] = last_json_line(
            run("all_coefficients", [str(executables["check_reverse"])])
        )
        for check, filename in (
            ("compact_certificate", "compact_certificate.json"),
            ("original_certificate", "original_sharp_certificate.json"),
        ):
            report = output / (check + ".json")
            run(check, py("check_certificate.py", "--certificate", ROOT / "data" / filename, "--output", report))
            summary[check] = json.loads(report.read_text(encoding="utf-8"))
        run("six_finite_models", py("check_finite_models.py", "--output", output / "six_finite_models.json"))
        certificate = json.loads((ROOT / "data/compact_certificate.json").read_text(encoding="utf-8"))
        controls = output / "negative-controls"
        controls.mkdir()
        negative_results = []
        for name in ("negative_factor_weight", "degree_multiplier_plus_one"):
            damaged = json.loads(json.dumps(certificate))
            if name == "negative_factor_weight":
                damaged["rank_one_factors"][0]["weight_numerator"] = -1
            else:
                key = "degree_2_(2,)_1"
                damaged["degree_weights_numerators"][key] = str(int(damaged["degree_weights_numerators"][key]) + 1)
            badfile = controls / (name + ".json")
            badfile.write_text(json.dumps(damaged), encoding="utf-8")
            report = controls / (name + "-unexpected-report.json")
            text = run(
                name,
                py("check_certificate.py", "--certificate", badfile, "--output", report),
                expected=1,
            )
            reason = "Negative rank-one weight" if name == "negative_factor_weight" else "Raw dual bound differs from 5/4"
            require(reason in text, "Negative control failed for an unexpected reason")
            negative_results.append({"check": name, "rejected_for_expected_reason": True})
        summary["negative_controls"] = negative_results
        summary["all_passed"] = all(step["passed"] for step in steps)
        summary["verifier_sha256"] = {str(p.relative_to(ROOT)).replace("\\", "/"): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted((ROOT / "verifiers").iterdir()) if p.is_file()}
        summary["runner_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
        require(summary["all_passed"], "A step did not pass")
    finally:
        summary["seconds"] = time.perf_counter() - started
        (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"all_passed": True, "version": VERSION, "exact_bound": "5/4", "seconds": summary["seconds"]}), flush=True)


if __name__ == "__main__":
    main()
