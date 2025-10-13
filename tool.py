#!/usr/bin/env python3

import argparse
import os
import subprocess
import sys
from pathlib import Path
import shutil
import signal
from typing import Callable, Optional, List, Dict, Tuple
from dataclasses import dataclass, replace


@dataclass(frozen=True)
class Config:
    overwrite: bool
    debug: bool
    yes: bool
    keep_going: bool
    overwrite_depth: int
    log: Optional[str]

    def decrease_depth(self) -> "Config":
        if not self.overwrite:
            return self

        new_depth = self.overwrite_depth - 1
        return replace(
            self,
            overwrite=(new_depth > 0),
            overwrite_depth=new_depth,
        )

    def decrease_depth_to(self, depth) -> "Config":
        if not self.overwrite:
            return self

        new_depth = min(self.overwrite_depth, depth)
        return replace(
            self,
            overwrite=(new_depth > 0),
            overwrite_depth=new_depth,
        )


class TaskFailedError(Exception):
    pass


BENCH_ROOT: Path = Path("benchmarks")
CONFIG_ROOT: Path = BENCH_ROOT / "configs"
ANALYSIS_ROOT: Path = BENCH_ROOT / "analyses"
ANALYSIS_CONFIG_ROOT: Path = BENCH_ROOT / "analysis-configs"
BIN_TEST_DIR: Path = BENCH_ROOT / "bin-tests"
SCRIPT_TEST_DIR: Path = BENCH_ROOT / "script-tests"
RS_ORIG: Path = BENCH_ROOT / "rs"
TRANSFORM_DIRS: Dict[str, Path] = {
    "resolve": BENCH_ROOT / "rs-resolved",
    "expand":  BENCH_ROOT / "rs-expanded",
    "expand-resolve":  BENCH_ROOT / "rs-expand-resolve",
    "resolve-post": BENCH_ROOT / "rs-resolve-post",
    "union": BENCH_ROOT / "rs-union",
    "io": BENCH_ROOT / "rs-io",
    "io-union": BENCH_ROOT / "rs-io-union",
}
TRANSFORM_ORDER: Dict[str, Optional[str]] = {
    "resolve": None,
    "expand": None,
    "expand-resolve": "expand",
    "resolve-post": "expand-resolve",
    "union": "resolve",
    "io": "resolve",
    "io-union": "io",
}
TRANSFORM_ANALYSIS: Dict[str, Optional[Tuple[str, str]]] = {
    "resolve": None,
    "expand": None,
    "expand-resolve": None,
    "resolve-post": None,
    "union": ("union", "points-to-file"),
    "io": None,
    "io-union": ("union", "points-to-file"),
}
TRANSFORM_PASS: Dict[str, str] = {
    "resolve": "preprocess,extern,bin",
    "expand": "expand",
    "expand-resolve": "preprocesse,externe,bin",
    "resolve-post": "unexpand",
    "union": "union",
    "io": "io",
    "io-union": "union",
}
TRANSFORM_CONFIG: Dict[str, Path] = {
    "resolve": CONFIG_ROOT / "resolve",
    "expand": CONFIG_ROOT / "expand",
    "expand-resolve": CONFIG_ROOT / "resolve",
    "resolve-post": CONFIG_ROOT / "post",
    "union": CONFIG_ROOT / "union",
    "io": CONFIG_ROOT / "io",
    "io-union": CONFIG_ROOT / "union",
}
ANALYSIS_DIRS: Dict[str, Path] = {
    "union": ANALYSIS_ROOT / "union",
    "io-union": ANALYSIS_ROOT / "io-union",
}
ANALYSIS_ORDER: Dict[str, str] = {
    "union": "resolve",
    "io-union": "io",
}
ANALYSIS_PASS: Dict[str, str] = {
    "union": "andersen",
    "io-union": "andersen",
}
ANALYSIS_CONFIG: Dict[str, Path] = {
    "union": ANALYSIS_CONFIG_ROOT / "union",
    "io-union": ANALYSIS_CONFIG_ROOT / "io-union",
}
current_dst: Optional[Path] = None


def handle_interrupt(_, __):
    global current_dst
    print("\n[Interrupt] Caught Ctrl+C")
    if current_dst and current_dst.exists():
        print(f"[Remove] {current_dst}")
        shutil.rmtree(current_dst)
    sys.exit(1)


signal.signal(signal.SIGINT, handle_interrupt)


def list_benchmarks() -> List[str]:
    return sorted(p.name for p in RS_ORIG.iterdir() if p.is_dir())


def is_benchmark(bench: str) -> bool:
    return (RS_ORIG / bench).is_dir()


def analyze_one(stage: str, bench: str, config: Config):
    dst = ANALYSIS_DIRS[stage] / bench
    if dst.exists() and not config.overwrite:
        print(
            f"[Skip] {dst} already exists (use --overwrite to overwrite or --overwrite-depth to adjust depth)"
        )
        return

    src_stage = ANALYSIS_ORDER[stage]
    src = TRANSFORM_DIRS[src_stage] / bench

    if src_stage and (not src.exists() or config.overwrite):
        transform_one(src_stage, bench, config.decrease_depth())

    config_dir = ANALYSIS_CONFIG[stage]
    config_file = config_dir / f"{bench}.toml"
    config_file = config_file if config_file.exists() else None

    if not dst.parent.exists():
        dst.parent.mkdir(parents=True)

    cmd = ["cargo", "run", "--bin", "crat"]
    if not os.environ.get("DEBUG"):
        cmd.append("--release")
    cmd += ["--", "--analysis-output", str(dst), "--analysis", ANALYSIS_PASS[stage]]
    if config_file:
        cmd.extend(["--config", str(config_file)])
    if config.log:
        cmd.extend(["-l", config.log])
    cmd.append(str(src))

    global current_dst
    current_dst = dst
    print("[Running]", " ".join(cmd))
    try:
        subprocess.run(cmd, check=True)
    except subprocess.CalledProcessError:
        print(f"[Error] Analysis failed: {src} -> {dst}")
        if current_dst.exists():
            print(f"[Remove] {current_dst}")
            shutil.rmtree(current_dst)
        if config.keep_going:
            raise TaskFailedError()
        else:
            sys.exit(1)
    finally:
        current_dst = None


def transform_one(stage: str, bench: str, config: Config):
    dst = TRANSFORM_DIRS[stage] / bench
    if dst.exists() and not config.overwrite:
        print(
            f"[Skip] {dst} already exists (use --overwrite to overwrite or --overwrite-depth to adjust depth)"
        )
        return

    src_stage = TRANSFORM_ORDER[stage]
    src = RS_ORIG / bench if src_stage is None else TRANSFORM_DIRS[src_stage] / bench

    if src_stage and (not src.exists() or config.overwrite):
        transform_one(src_stage, bench, config.decrease_depth())

    analysis_stage_opt = TRANSFORM_ANALYSIS[stage]
    analysis_file, analysis_opt = None, None
    if analysis_stage_opt:
        analysis_stage, analysis_opt = analysis_stage_opt
        analysis_file = ANALYSIS_DIRS[analysis_stage] / bench

        if not analysis_file.exists() or config.overwrite:
            analyze_one(analysis_stage, bench, config.decrease_depth().decrease_depth_to(1))

    config_dir = TRANSFORM_CONFIG[stage]
    config_file = config_dir / f"{bench}.toml"
    config_file = config_file if config_file.exists() else None

    if not dst.parent.exists():
        dst.parent.mkdir(parents=True)

    cmd = ["cargo", "run", "--bin", "crat"]
    if not os.environ.get("DEBUG"):
        cmd.append("--release")
    cmd += ["--", "-o", str(dst.parent), "--pass", TRANSFORM_PASS[stage]]
    if analysis_file and analysis_opt:
        cmd += [f"--{analysis_opt}", str(analysis_file)]
    if config_file:
        cmd.extend(["--config", str(config_file)])
    if config.log:
        cmd.extend(["-l", config.log])
    cmd.append(str(src))

    global current_dst
    current_dst = dst
    print("[Running]", " ".join(cmd))
    try:
        subprocess.run(cmd, check=True)
    except subprocess.CalledProcessError:
        print(f"[Error] Transformation failed: {src} -> {dst}")
        if current_dst.exists():
            print(f"[Remove] {current_dst}")
            shutil.rmtree(current_dst)
        if config.keep_going:
            raise TaskFailedError()
        else:
            sys.exit(1)
    finally:
        current_dst = None


def build_one(stage: str, bench: str, config: Config):
    bench_dir = TRANSFORM_DIRS[stage] / bench
    if not bench_dir.exists() or config.overwrite:
        transform_one(stage, bench, config)

    env = os.environ.copy()
    env["RUSTFLAGS"] = "-Awarnings"
    cmd = ["cargo", "build"]
    if not config.debug:
        cmd.append("--release")

    print(f"[Building] {bench_dir}")
    try:
        subprocess.run(cmd, cwd=bench_dir, env=env, check=True)
    except subprocess.CalledProcessError:
        print(f"[Error] Build failed: {bench_dir}")
        if config.keep_going:
            raise TaskFailedError()
        else:
            sys.exit(1)


def test_one(stage: str, bench: str, config: Config):
    build_one(stage, bench, config)

    print(f"[Test] {bench}")

    test_file = BIN_TEST_DIR / f"{bench}.txt"
    script_file = SCRIPT_TEST_DIR / f"{bench}.sh"

    if test_file.exists():
        bench_dir = TRANSFORM_DIRS[stage] / bench
        bin_subdir = "debug" if config.debug else "release"
        with open(test_file) as f:
            for line in f:
                line = line.strip()
                if not line or line.startswith("#"):
                    continue

                expected_failure = line.startswith("!")
                name = line[1:] if expected_failure else line
                bin_path = Path("target") / bin_subdir / name

                print(f"[Exec] {bin_path}")
                result = subprocess.run([str(bin_path)], cwd=bench_dir)
                success = (result.returncode == 0 and not expected_failure) or (
                    result.returncode != 0 and expected_failure
                )
                status = "ok" if success else "FAIL"
                print(f"  => {status}")

                if not success:
                    if config.keep_going:
                        raise TaskFailedError()
                    else:
                        sys.exit(1)

    elif script_file.exists():
        tmp_dir = BENCH_ROOT / "tmp"
        tmp_dir.mkdir(exist_ok=True)

        cmd = [str(script_file), str(tmp_dir), str(TRANSFORM_DIRS[stage])]
        if not config.debug:
            cmd.append("--release")

        print(f"[Exec] {' '.join(cmd)}")
        try:
            subprocess.run(cmd, check=True)
            print("  => ok")
        except subprocess.CalledProcessError:
            print("  => FAIL")
            if config.keep_going:
                raise TaskFailedError()
            else:
                sys.exit(1)

    else:
        print(f"[Skip] No test: {bench}")


def clean_one(stage: str, bench: str, _: Config):
    path = TRANSFORM_DIRS[stage]
    target = path / bench
    if target.exists():
        print(f"[Remove] {target}")
        shutil.rmtree(target)


def make_runner(
    f: Callable[[str, str, Config], None],
    need_confirm: bool = False,
) -> Callable[[str, Optional[str], List[str], Config], None]:
    def runner(stage: str, bench: Optional[str], excludes: List[str], config: Config):
        if bench:
            if is_benchmark(bench):
                benchmarks = [bench]
            else:
                benchmarks = [
                    name for name in list_benchmarks() if name.startswith(bench)
                ]
        else:
            benchmarks = list_benchmarks()

        if not benchmarks:
            print(f"[Error] No benchmark: {bench}")
            sys.exit(1)
        else:
            benchmarks = [
                b for b in benchmarks if not any(b.startswith(ex) for ex in excludes)
            ]
            if need_confirm and not config.yes and len(benchmarks) > 1:
                print(f"[Warning] {len(benchmarks)} benchmarks found:")
                for bench in benchmarks:
                    print(f"  - {bench}")
                confirm = input("Continue? (y/n): ").strip().lower()
                if confirm != "y":
                    print("[Aborted]")
                    return

            failed_benchmarks = []

            for bench in benchmarks:
                try:
                    f(stage, bench, config)
                except TaskFailedError:
                    failed_benchmarks.append(bench)

            if failed_benchmarks:
                print("[Error] The following benchmarks failed:")
                for bench in failed_benchmarks:
                    print(f"  - {bench}")
                sys.exit(1)

    return runner


analyze = make_runner(analyze_one)
transform = make_runner(transform_one)
build = make_runner(build_one)
test = make_runner(test_one)
clean = make_runner(clean_one, need_confirm=True)


def parse_overwrite_depth(value: str) -> int:
    if value == "max":
        return sys.maxsize
    try:
        ivalue = int(value)
        if ivalue <= 0:
            raise ValueError()
        return ivalue
    except ValueError:
        raise argparse.ArgumentTypeError(
            f"overwrite-depth must be a positive integer or 'max', got: {value}"
        )


def main():
    parser = argparse.ArgumentParser(prog="tool.py")
    parser.add_argument(
        "command",
        choices=["analyze", "transform", "build", "test", "clean"],
        help="Main operation to perform",
    )
    parser.add_argument(
        "stage",
        help="Stage to operate on (e.g., resolve, union, io, etc.)",
    )
    parser.add_argument(
        "benchmark",
        nargs="?",
        help="Name of the benchmark (optional)",
    )
    parser.add_argument("--overwrite", action="store_true", help="Overwrite existing")
    parser.add_argument(
        "--debug", action="store_true", help="Use debug mode for build/test"
    )
    parser.add_argument(
        "-y", "--yes", action="store_true", help="Automatically say yes to prompts"
    )
    parser.add_argument("--keep-going", action="store_true", help="Continue on errors")
    parser.add_argument(
        "--overwrite-depth",
        type=parse_overwrite_depth,
        default=1,
        help="Overwrite depth: positive integer or 'max' (default: 1)",
    )
    parser.add_argument(
        "-l",
        "--log",
        help="Log file",
    )
    parser.add_argument(
        "--exclude",
        action="append",
        help="Excluded benchmarks. Supports comma-separated or multiple --exclude.",
    )

    args = parser.parse_args()

    if args.command == "analyze":
        if args.stage not in ANALYSIS_ORDER:
            print(f"Unknown analysis stage: {args.stage}")
            sys.exit(1)
    else:
        if args.stage not in TRANSFORM_DIRS:
            print(f"Unknown stage: {args.stage}")
            sys.exit(1)

    config = Config(
        overwrite=args.overwrite,
        debug=args.debug,
        yes=args.yes,
        keep_going=args.keep_going,
        overwrite_depth=args.overwrite_depth,
        log=args.log,
    )

    excludes = []
    if args.exclude:
        for item in args.exclude:
            excludes.extend(item.split(","))

    if args.command == "analyze":
        runner = analyze
    elif args.command == "transform":
        runner = transform
    elif args.command == "build":
        runner = build
    elif args.command == "test":
        runner = test
    else:
        runner = clean
    runner(args.stage, args.benchmark, excludes, config)


if __name__ == "__main__":
    main()
