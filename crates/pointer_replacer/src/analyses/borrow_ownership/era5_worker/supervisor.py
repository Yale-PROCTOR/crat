"""Sealed evaluation-host supervisor; importing this module launches nothing.

One invocation reserves and launches one model. A crashed Running row is held
for seat review; terminal rows are never retried. There is no corpus loop.
Run mock tests with python3 -B to avoid changing the analysis input tree.
"""
import contextlib
import hashlib
import json
import os
from pathlib import Path
import signal
import resource
import subprocess
import time

PROGRAMS = frozenset(("bst", "avl", "ht", "libcsv", "buffer", "quadtree",
    "urlparser", "robotfindskitten", "rgba", "genann", "libtree", "json.h",
    "binn", "libzahl", "lil", "heman", "bzip2", "lodepng", "tulipindicators", "brotli"))
GUARDS = {"worker_seconds": 14400, "query_seconds": 600, "emission_seconds": 900}
WORKER = "analyses::borrow_ownership::era5_worker::era5_model_worker"
U64_MAX = (1 << 64) - 1


class Refusal(ValueError):
    pass


def require(condition, detail):
    if not condition:
        raise Refusal(detail)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def encoded(value, sort=True):
    return json.dumps(value, sort_keys=sort, ensure_ascii=False,
                      separators=(",", ":"), allow_nan=False).encode()


def is_digest(value):
    return isinstance(value, str) and len(value) == 64 and all(c in "0123456789abcdef" for c in value)


def positive(value):
    return type(value) is int and 0 < value <= U64_MAX


def logical(value):
    return isinstance(value, str) and bool(value) and "\\" not in value and all(
        part not in ("", ".", "..") for part in value.split("/"))


def decode(data):
    def unique(pairs):
        out = {}
        for key, value in pairs:
            require(key not in out, "duplicate JSON identity")
            out[key] = value
        return out
    return json.loads(data, object_pairs_hook=unique)


def semantic_key(inputs):
    require(set(inputs) == {"program", "files", "analysis", "toolchain", "dependencies", "configuration"},
            "semantic input fields")
    require(inputs["program"] in PROGRAMS and inputs["files"], "semantic program/files")
    require(all(logical(p) and is_digest(h) for p, h in inputs["files"].items()), "semantic logical files")
    require(all(is_digest(inputs[k]) for k in ("analysis", "toolchain", "dependencies", "configuration")),
            "semantic digests")
    # Rust SemanticInputs struct declaration order, with BTreeMap file order.
    ordered = {"program": inputs["program"], "files": dict(sorted(inputs["files"].items()))}
    ordered.update((k, inputs[k]) for k in ("analysis", "toolchain", "dependencies", "configuration"))
    return digest(b"era5a-model-cache-v1\0" + encoded(ordered, sort=False))


def resource_rows(seal, active):
    require(seal["guards"] == GUARDS, "guard change")
    require(positive(seal["physical_mib"]) and positive(seal["headroom_mib"])
            and seal["headroom_mib"] < seal["physical_mib"], "physical/headroom seal")
    rows = {}
    for row in seal["reservations"]:
        require(row["id"] and row["id"] not in rows and row["host"] == seal["host"]
                and row["class"] in ("heavy", "small") and positive(row["cap_mib"]), "reservation seal")
        rows[row["id"]] = row
    require(len(active) == len(set(active)), "reservation already active")
    require(all(key in rows for key in active), "unknown reservation")
    require(len(active) <= 3, "more than three workers")
    require(sum(rows[key]["class"] == "heavy" for key in active) <= 2, "more than two heavy workers")
    total = sum(rows[key]["cap_mib"] for key in active)
    require(total <= U64_MAX and total <= seal["physical_mib"] - seal["headroom_mib"], "aggregate cap")
    return rows


def inventory_seal(manifest):
    return digest(encoded({"inventory": manifest["inventory"], "resources": manifest["resources"]}))


def validate_manifest(manifest, expected):
    require(manifest["schema"] == "era5a-worker-manifest-v1" and is_digest(expected)
            and inventory_seal(manifest) == expected, "immutable inventory seal")
    require(set(manifest["inventory"]) == PROGRAMS and set(manifest["states"]) == PROGRAMS,
            "exact twenty-program manifest required")
    rows = resource_rows(manifest["resources"], [])
    for program, entry in manifest["inventory"].items():
        require(is_digest(entry["input_sha256"]) and is_digest(entry["job_sha256"])
                and Path(entry["job_path"]).is_absolute() and entry["reservation"] in rows,
                "unsealed program identity")
        require(manifest["states"][program]["status"] in ("pending", "running", "complete", "failure"),
                "unclassified manifest state")


def sealed(runtime, seal):
    require(Path(seal["path"]).is_absolute() and is_digest(seal["sha256"]), "sealed file identity")
    data = runtime.read(seal["path"])
    require(digest(data) == seal["sha256"], "sealed file changed: " + seal["path"])
    return data


def validate_job(runtime, job, after_process=False):
    require(job["schema"] == "era5a-model-job-v1"
            and job["admission"] == "era5a-freeze-seat-accepted", "seat-accepted era5a freeze admission")
    require(job["host_role"] == "evaluation" and not job["host"].split(".")[0].startswith("lambda7")
            and runtime.host() == job["host"] == job["resources"]["host"], "evaluation host guard")
    require(runtime.physical_mib() == job["resources"]["physical_mib"], "physical host changed")
    require(job["program"] in PROGRAMS and job["cache_namespace"] == "era5a-candidate", "candidate namespace")
    require(all(Path(job[k]).is_absolute() for k in ("input_root", "cache_dir", "receipt")), "absolute job paths")
    resource_rows(job["resources"], [job["reservation"]])
    for key in ("input", "source", "toolchain", "dependencies", "launch", "binary"):
        sealed(runtime, job[key])
    require(set(job["semantic"]) == {"analysis", "toolchain", "dependencies", "configuration"}
            and all(is_digest(v) for v in job["semantic"].values()), "semantic seal")
    require(job["semantic"]["toolchain"] == job["toolchain"]["sha256"]
            and job["semantic"]["dependencies"] == job["dependencies"]["sha256"], "semantic producer seals")
    require(job.get("expected_key") is None or is_digest(job["expected_key"]), "optional expected key")
    if job.get("expected_inputs") is not None:
        key = semantic_key(job["expected_inputs"])
        require(job.get("expected_key") in (None, key), "optional expected inputs/key mismatch")
    require(all(isinstance(k, str) and isinstance(v, str) for k, v in job["environment"].items()),
            "sealed environment strings")
    require(job["environment"].get("CRAT_ERA5_LAUNCH_DIGEST") == job["launch"]["sha256"],
            "explicit launch digest environment")
    files = decode(sealed(runtime, job["input_manifest"]))
    root = runtime.resolve(job["input_root"])
    require(files and all(logical(p) and is_digest(h) for p, h in files.items()), "full input manifest")
    for name, expected in files.items():
        path = runtime.resolve(str(Path(root) / name))
        require(Path(path).is_relative_to(root) and digest(runtime.read(path)) == expected,
                "input manifest changed or escapes root")
    entry = runtime.resolve(job["input"]["path"])
    require(Path(entry).is_relative_to(root), "input outside root")
    require(files.get(str(Path(entry).relative_to(root))) == job["input"]["sha256"], "input absent from manifest")
    require(after_process or not runtime.exists(job["receipt"]), "worker receipt already exists; no rerun")
    return files


def reconcile(runtime, job, job_hash, files, process):
    """Transport custody only; receiver still runs Rust CompleteEntry validation."""
    if process["limit"] is not None:
        require(process["limit"] in ("timeout", "oom"), "unclassified enforced limit")
        return {"status": "failure", "kind": process["limit"], "detail": "supervisor enforced sealed limit"}
    if not runtime.exists(job["receipt"]):
        return {"status": "failure", "kind": "missing", "detail": "worker receipt absent"}
    receipt_bytes = runtime.read(job["receipt"])
    receipt = decode(receipt_bytes)
    require(receipt["schema"] == "era5a-worker-receipt-v1"
            and receipt["program"] == job["program"] and receipt["host"] == job["host"]
            and receipt["job_sha256"] == job_hash, "worker receipt identity")
    for key in ("source", "toolchain", "launch"):
        require(receipt[key + "_sha256"] == job[key]["sha256"], "receipt provenance: " + key)
    if receipt["status"] == "failure":
        require(receipt.get("completed") is None and isinstance(receipt.get("failure"), dict), "failure receipt shape")
        failure = receipt["failure"]
        kind = failure["kind"] if failure["kind"] in ("unknown", "decline") else "invalid"
        return {"status": "failure", "kind": kind, "detail": failure["detail"],
                "receipt_sha256": digest(receipt_bytes)}
    require(receipt["status"] == "complete" and receipt.get("failure") is None and process["exit_code"] == 0,
            "non-success process cannot complete")
    complete = receipt["completed"]
    require(complete["model_entries"] == 1, "exactly one model entry required")
    key = semantic_key(complete["inputs"])
    require(key == complete["key"] and job.get("expected_key") in (None, key), "actual semantic key")
    inputs = complete["inputs"]
    require(inputs["program"] == job["program"]
            and all(inputs[k] == v for k, v in job["semantic"].items())
            and all(files.get(p) == h for p, h in inputs["files"].items())
            and job.get("expected_inputs") in (None, inputs), "actual compiler file/producer custody")
    entry_path = runtime.resolve(complete["cache_entry"])
    require(Path(entry_path).is_relative_to(runtime.resolve(job["cache_dir"])), "entry outside candidate cache")
    body = runtime.read(entry_path)
    require(digest(body) == complete["entry_sha256"], "entry body digest")
    entry = decode(body)
    require(entry["schema"] == "era5a-model-cache-v1" and entry["key"] == key and entry["inputs"] == inputs,
            "entry semantic identity")
    universe = entry["universe"]
    require(len(universe) == len(set(universe)) and set(entry["model"]) == set(universe)
            and set(entry["baseline"]) == set(universe)
            and all(kind in ("raw", "ref", "owning") for model in (entry["model"], entry["baseline"])
                    for kind in model.values()), "entry model universe")
    require({"status=ok", "data=true"}.issubset(entry["receipt"].splitlines())
            and isinstance(entry["exports"], dict) and isinstance(entry["origin"], dict), "complete receipt/exports")
    payload = digest(encoded([entry["model"], entry["baseline"], entry["receipt"]]))
    exports = digest(encoded([entry["exports"], entry["origin"]]))
    require(payload == complete["payload_sha256"] and exports == complete["export_sha256"], "payload/export digest")
    return {"status": "complete", "key": key, "inputs": inputs, "entry_sha256": digest(body),
            "payload_sha256": payload, "export_sha256": exports, "receipt_sha256": digest(receipt_bytes),
            "job_sha256": job_hash, "host": job["host"],
            "host_provenance_sha256": digest(encoded(job["resources"]))}


def launch_one(runtime, manifest_path, manifest_hash, job_path, job_hash):
    """No launch until all seals pass and Pending is durably changed to Running."""
    require(Path(job_path).is_absolute() and is_digest(job_hash), "detached job identity")
    job_bytes = runtime.read(job_path)
    require(digest(job_bytes) == job_hash, "detached job digest changed")
    job = decode(job_bytes)
    files = validate_job(runtime, job)
    program = job["program"]
    with runtime.lock(manifest_path):
        manifest = decode(runtime.read(manifest_path))
        validate_manifest(manifest, manifest_hash)
        sealed_row = manifest["inventory"][program]
        require(sealed_row == {"input_sha256": job["input"]["sha256"], "job_sha256": job_hash,
                "job_path": job_path, "reservation": job["reservation"]}, "job/inventory identity")
        require(manifest["resources"] == job["resources"], "reservation profile changed")
        require(manifest["states"][program]["status"] == "pending", "no rerun of Running or terminal rows")
        active = [manifest["inventory"][p]["reservation"] for p, state in manifest["states"].items()
                  if state["status"] == "running"] + [job["reservation"]]
        resource_rows(job["resources"], active)
        manifest["states"][program] = {"status": "running", "job_sha256": job_hash}
        runtime.write_atomic(manifest_path, encoded(manifest))
    # Exceptions after this durable transition are terminal. Never auto-retry.
    try:
        process = runtime.launch(job, job_path, job_hash)
        require(digest(runtime.read(job_path)) == job_hash, "job changed during worker")
        require(validate_job(runtime, job, after_process=True) == files, "input manifest changed during worker")
        require(digest(runtime.read(process["log"])) == process["log_sha256"], "closed log digest changed")
        result = reconcile(runtime, job, job_hash, files, process)
        result["process"] = process
    except (OSError, ValueError, KeyError, TypeError) as error:
        result = {"status": "failure", "kind": "invalid", "detail": str(error)}
        if "process" in locals():
            result["process"] = process
    with runtime.lock(manifest_path):
        manifest = decode(runtime.read(manifest_path))
        validate_manifest(manifest, manifest_hash)
        require(manifest["states"][program] == {"status": "running", "job_sha256": job_hash}, "running custody changed")
        manifest["states"][program] = result
        runtime.write_atomic(manifest_path, encoded(manifest))
    return result


class RealRuntime:
    """Explicit future execution only. No host, cap, job, or retry defaults."""
    def read(self, path):
        return Path(path).read_bytes()

    def exists(self, path):
        return Path(path).exists()

    def resolve(self, path):
        return str(Path(path).resolve())

    def host(self):
        return self.read("/proc/sys/kernel/hostname").decode().strip()

    def physical_mib(self):
        line = next(line for line in self.read("/proc/meminfo").decode().splitlines() if line.startswith("MemTotal:"))
        return int(line.split()[1]) // 1024

    @contextlib.contextmanager
    def lock(self, path):
        import fcntl
        with open(str(path) + ".lock", "a+b") as handle:
            fcntl.flock(handle, fcntl.LOCK_EX)
            try:
                yield
            finally:
                fcntl.flock(handle, fcntl.LOCK_UN)

    def write_atomic(self, path, data):
        import tempfile
        target = Path(path)
        fd, name = tempfile.mkstemp(prefix=target.name + ".", dir=target.parent)
        try:
            with os.fdopen(fd, "wb") as handle:
                handle.write(data)
                handle.flush()
                os.fsync(handle.fileno())
            os.replace(name, target)
            directory = os.open(target.parent, os.O_RDONLY | os.O_DIRECTORY)
            try:
                os.fsync(directory)
            finally:
                os.close(directory)
        finally:
            if os.path.exists(name):
                os.unlink(name)

    def launch(self, job, job_path, job_hash):
        row = resource_rows(job["resources"], [job["reservation"]])[job["reservation"]]
        log = job["receipt"] + ".log"
        environment = {k: v for k, v in os.environ.items() if not k.startswith("CRAT_")}
        environment.update(job["environment"])
        required = {"CRAT_ERA5_EXECUTION_ROLE": "derive",
                    "CRAT_ERA5_JOB_PATH": job_path, "CRAT_ERA5_JOB_SHA256": job_hash,
                    "CRAT_ERA5_PROGRAM": job["program"], "CRAT_ERA5_INPUT_ROOT": job["input_root"],
                    "CRAT_ERA5_TOOLCHAIN_DIGEST": job["semantic"]["toolchain"],
                    "CRAT_ERA5_DEPENDENCY_DIGEST": job["semantic"]["dependencies"],
                    "CRAT_ERA5_LAUNCH_DIGEST": job["launch"]["sha256"]}
        require(all(k not in job["environment"] or job["environment"][k] == v for k, v in required.items()),
                "conflicting required worker environment")
        environment.update(required)
        started = time.monotonic()
        peak_rss_kib = 0
        limit = None
        command = [job["binary"]["path"], "--ignored", "--exact", WORKER, "--nocapture", "--test-threads=1"]
        # The hard address-space limit and sampled RSS guard use the SAME sealed
        # cap. This is RLIMIT_AS plus sampling, not a cgroup/peak-RSS guarantee.
        cap_bytes = row["cap_mib"] * 1024 * 1024
        require(cap_bytes <= U64_MAX, "address-space cap overflow")
        def address_limit():
            resource.setrlimit(resource.RLIMIT_AS, (cap_bytes, cap_bytes))
        with open(log, "xb") as output:
            child = subprocess.Popen(command, env=environment, stdout=output, stderr=subprocess.STDOUT,
                                     stdin=subprocess.DEVNULL, start_new_session=True, preexec_fn=address_limit)
            try:
                while child.poll() is None:
                    try:
                        status = Path(f"/proc/{child.pid}/status").read_text()
                        values = [int(line.split()[1]) for line in status.splitlines()
                                  if line.startswith(("VmRSS:", "VmHWM:"))]
                        peak_rss_kib = max([peak_rss_kib] + values)
                    except FileNotFoundError:
                        pass
                    elapsed = time.monotonic() - started
                    if elapsed >= GUARDS["worker_seconds"]:
                        limit = "timeout"
                    elif peak_rss_kib > row["cap_mib"] * 1024:
                        limit = "oom"
                    if limit is not None:
                        os.killpg(child.pid, signal.SIGKILL)
                        break
                    time.sleep(0.05)
                exit_code = child.wait()
            finally:
                if child.poll() is None:
                    os.killpg(child.pid, signal.SIGKILL)
                    child.wait()
            output.flush()
            os.fsync(output.fileno())
        # An unexplained SIGKILL stays a missing/invalid failure, never guessed OOM.
        return {"exit_code": exit_code, "wall_seconds": time.monotonic() - started,
                "peak_rss_kib": peak_rss_kib, "rss_measurement": "proc-vmrss-vmhwm-sampled-50ms",
                "cap_mib": row["cap_mib"], "limit": limit, "log": log,
                "enforcement": {"address_space": "RLIMIT_AS-soft-and-hard", "address_space_bytes": cap_bytes,
                                "rss": "sampled-50ms-kill-process-group", "wall_seconds": GUARDS["worker_seconds"]},
                "log_sha256": digest(self.read(log)), "command": command}


def main():
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--execute", action="store_true", required=True)
    parser.add_argument("--manifest", required=True)
    parser.add_argument("--manifest-seal", required=True)
    parser.add_argument("--job", required=True)
    parser.add_argument("--job-sha256", required=True)
    args = parser.parse_args()
    result = launch_one(RealRuntime(), args.manifest, args.manifest_seal, args.job, args.job_sha256)
    print(encoded(result).decode())
    return 0 if result["status"] == "complete" else 1


if __name__ == "__main__":
    raise SystemExit(main())
