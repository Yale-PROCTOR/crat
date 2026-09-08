"""Mock-only custody controls. No compiler, worker, solver, filesystem or network.

Invoke this file with python3 -B; source-tree bytecode is never generated.
Synthetic transport bodies do not claim Rust CompleteEntry semantic validation.
"""
import sys
sys.dont_write_bytecode = True
import contextlib
import copy
import io
import os
from types import SimpleNamespace
import unittest
from unittest import mock

import supervisor as s


class MemoryRuntime:
    def __init__(self):
        self.files = {}
        self.calls = []
        self.writes = []
        self.actual_host = "lambda7"
        self.memory = 1024
        self.outcome = "complete"
        self.after_launch = lambda runtime, job: None

    def read(self, path):
        try:
            return self.files[str(path)]
        except KeyError:
            raise FileNotFoundError(str(path)) from None

    def exists(self, path):
        return str(path) in self.files

    def resolve(self, path):
        return os.path.normpath(str(path))

    def host(self):
        return self.actual_host

    def physical_mib(self):
        return self.memory

    def lock(self, path):
        return contextlib.nullcontext()

    def write_atomic(self, path, data):
        self.files[str(path)] = data
        self.writes.append((str(path), data))

    def seal(self, path, data):
        self.files[path] = data
        return {"path": path, "sha256": s.digest(data)}

    def launch(self, job, job_path, job_hash):
        # A launch can only observe a durably reserved Running row.
        assert s.decode(self.read("/manifest"))["states"][job["program"]]["status"] == "running"
        self.calls.append((job_path, job_hash))
        log = job["receipt"] + ".log"
        self.files[log] = b"synthetic closed worker log\n"
        process = {"exit_code": 0, "wall_seconds": 0.25, "peak_rss_kib": 32,
                   "cap_mib": 256, "limit": None, "log": log, "log_sha256": s.digest(self.files[log])}
        if self.outcome in ("timeout", "oom", "missing"):
            process.update(exit_code=-9, limit=None if self.outcome == "missing" else self.outcome)
        else:
            receipt = {"schema": "era5a-worker-receipt-v1", "program": job["program"],
                "host": job["host"], "job_sha256": job_hash, "source_sha256": job["source"]["sha256"],
                "toolchain_sha256": job["toolchain"]["sha256"], "launch_sha256": job["launch"]["sha256"],
                "status": "complete", "completed": None, "failure": None}
            if self.outcome in ("unknown", "decline"):
                receipt.update(status="failure", failure={"kind": self.outcome, "detail": "typed synthetic outcome"})
                process["exit_code"] = 101
            else:
                inputs = {"program": job["program"], "files": {"main.rs": job["input"]["sha256"]}, **job["semantic"]}
                key = s.semantic_key(inputs)
                entry = {"schema": "era5a-model-cache-v1", "key": key, "inputs": inputs,
                    "functions": ["crate::f"], "universe": ["crate::f::_1@0"],
                    "model": {"crate::f::_1@0": "ref"}, "baseline": {"crate::f::_1@0": "raw"},
                    "receipt": "status=ok\ndata=true\n", "exports": {"synthetic": "transport-only"},
                    "origin": {"functions": [{"function": "crate::f"}]}}
                path = job["cache_dir"] + "/" + key + ".json"
                self.files[path] = s.encoded(entry)
                receipt["completed"] = {"key": key, "inputs": inputs, "cache_entry": path,
                    "entry_sha256": s.digest(self.files[path]), "model_entries": 1,
                    "payload_sha256": s.digest(s.encoded([entry["model"], entry["baseline"], entry["receipt"]])),
                    "export_sha256": s.digest(s.encoded([entry["exports"], entry["origin"]]))}
            self.files[job["receipt"]] = s.encoded(receipt)
        self.after_launch(self, job)
        return process


class Fixture:
    def __init__(self):
        self.runtime = MemoryRuntime()
        self.resources = {"host": self.runtime.host(), "physical_mib": 1024, "headroom_mib": 128,
            "guards": dict(s.GUARDS), "reservations": [
                {"id": name, "host": self.runtime.host(), "class": "heavy" if name in ("bst", "avl", "ht") else "small",
                 "cap_mib": 256} for name in sorted(s.PROGRAMS)]}
        seal = self.runtime.seal
        input_seal = seal("/input/main.rs", b"synthetic source")
        unused = seal("/input/unused.rs", b"sealed but not compiler-loaded")
        self.job = {"schema": "era5a-model-job-v1", "admission": "era5a-freeze-seat-accepted", "program": "bst",
            "host": self.runtime.host(), "host_role": "evaluation", "input": input_seal, "input_root": "/input",
            "input_manifest": seal("/input-manifest", s.encoded({"main.rs": input_seal["sha256"], "unused.rs": unused["sha256"]})),
            "source": seal("/source-seal", b"source"), "toolchain": seal("/toolchain", b"toolchain"),
            "dependencies": seal("/dependencies", b"dependencies"), "launch": seal("/launch", b"launch"),
            "binary": seal("/worker-binary", b"NOT AN EXECUTABLE; synthetic fixture"),
            "semantic": {"analysis": s.digest(b"analysis"), "toolchain": s.digest(b"toolchain"),
                         "dependencies": s.digest(b"dependencies"), "configuration": s.digest(b"configuration")},
            "expected_inputs": None, "expected_key": None, "resources": self.resources, "reservation": "bst",
            "environment": {"CRAT_ERA5_LAUNCH_DIGEST": s.digest(b"launch")}, "cache_dir": "/candidate",
            "cache_namespace": "era5a-candidate", "receipt": "/receipt"}
        self.manifest = {"schema": "era5a-worker-manifest-v1", "resources": self.resources,
            "inventory": {name: {"input_sha256": s.digest(name.encode()), "job_sha256": s.digest((name + "job").encode()),
                                 "job_path": "/jobs/" + name, "reservation": name} for name in s.PROGRAMS},
            "states": {name: {"status": "pending"} for name in s.PROGRAMS}}
        self.persist()

    def persist(self):
        self.runtime.files["/jobs/bst"] = s.encoded(self.job)
        self.job_hash = s.digest(self.runtime.files["/jobs/bst"])
        self.manifest["inventory"]["bst"] = {"input_sha256": self.job["input"]["sha256"], "job_sha256": self.job_hash,
                                              "job_path": "/jobs/bst", "reservation": "bst"}
        self.manifest_hash = s.inventory_seal(self.manifest)
        self.runtime.files["/manifest"] = s.encoded(self.manifest)

    def run(self):
        return s.launch_one(self.runtime, "/manifest", self.manifest_hash, "/jobs/bst", self.job_hash)


def rewrite_receipt(runtime, job, edit):
    receipt = s.decode(runtime.read(job["receipt"]))
    edit(receipt)
    runtime.files[job["receipt"]] = s.encoded(receipt)


class SupervisorTests(unittest.TestCase):
    def test_one_process_complete_exact_inventory_and_no_rerun(self):
        f = Fixture()
        result = f.run()
        self.assertEqual(result["status"], "complete")
        self.assertEqual(len(f.runtime.calls), 1)
        self.assertEqual(result["process"]["log_sha256"], s.digest(f.runtime.read("/receipt.log")))
        self.assertEqual(set(s.decode(f.runtime.read("/manifest"))["states"]), s.PROGRAMS)
        self.assertEqual(s.decode(f.runtime.writes[0][1])["states"]["bst"]["status"], "running")
        self.assertEqual(s.decode(f.runtime.writes[-1][1])["states"]["bst"], result)
        self.assertEqual(set(result["inputs"]["files"]), {"main.rs"})
        with self.assertRaises(s.Refusal):
            f.run()
        self.assertEqual(len(f.runtime.calls), 1)

    def test_host_admission_launch_digest_and_input_refuse_before_launch(self):
        edits = [lambda f: f.job.update(admission="accepted-w3b-landing-and-era5-freeze"),
                 lambda f: f.job.update(host_role="development"),
                 lambda f: f.job.update(host="other-evaluation-host"),
                 lambda f: f.job["environment"].clear(),
                 lambda f: f.job["resources"]["guards"].update(query_seconds=601),
                 lambda f: f.runtime.files.update({"/input/unused.rs": b"drift"})]
        for edit in edits:
            with self.subTest(edit=edit):
                f = Fixture()
                edit(f)
                f.persist()
                with self.assertRaises(s.Refusal):
                    f.run()
                self.assertEqual(f.runtime.calls, [])

    def test_terminal_failure_distinctions_and_no_retry(self):
        for kind in ("timeout", "oom", "unknown", "decline", "missing"):
            with self.subTest(kind=kind):
                f = Fixture()
                f.runtime.outcome = kind
                result = f.run()
                self.assertEqual((result["status"], result["kind"]), ("failure", kind))
                with self.assertRaises(s.Refusal):
                    f.run()
                self.assertEqual(len(f.runtime.calls), 1)
        f = Fixture()
        f.manifest["states"]["bst"] = {"status": "running", "job_sha256": f.job_hash}
        f.persist()
        with self.assertRaises(s.Refusal):
            f.run()
        self.assertEqual(f.runtime.calls, [])

    def test_exact_twenty_and_sealed_resource_reservations(self):
        f = Fixture()
        self.assertEqual(len(f.manifest["inventory"]), 20)
        s.resource_rows(f.resources, ["bst", "avl", "buffer"])
        for active in (["bst", "avl", "ht"], ["bst", "avl", "buffer", "binn"], ["bst", "bst"], ["absent"]):
            with self.assertRaises(s.Refusal):
                s.resource_rows(f.resources, active)
        changed = copy.deepcopy(f.resources)
        changed["headroom_mib"] = 300
        with self.assertRaises(s.Refusal):
            s.resource_rows(changed, ["bst", "avl", "buffer"])
        del f.manifest["inventory"]["brotli"]
        f.persist()
        with self.assertRaises(s.Refusal):
            f.run()
        self.assertEqual(f.runtime.calls, [])

    def test_active_rows_reserve_before_launch(self):
        f = Fixture()
        f.manifest["states"]["avl"] = {"status": "running"}
        f.manifest["states"]["ht"] = {"status": "running"}
        f.persist()
        with self.assertRaises(s.Refusal):
            f.run()
        self.assertEqual(f.runtime.calls, [])

    def test_detached_identity_and_post_worker_seals(self):
        f = Fixture()
        f.runtime.files["/jobs/bst"] += b" "
        with self.assertRaises(s.Refusal):
            f.run()
        self.assertEqual(f.runtime.calls, [])
        for path in ("/jobs/bst", "/source-seal", "/toolchain", "/dependencies", "/launch",
                     "/worker-binary", "/input/main.rs", "/input/unused.rs", "/receipt.log"):
            with self.subTest(path=path):
                f = Fixture()
                f.runtime.after_launch = lambda runtime, job, path=path: runtime.files.update({path: b"changed"})
                result = f.run()
                self.assertEqual((result["status"], result["kind"]), ("failure", "invalid"))
                self.assertEqual(len(f.runtime.calls), 1)

    def test_actual_key_body_payload_exports_and_model_count_are_checked(self):
        edits = [lambda receipt: receipt["completed"].update(model_entries=0),
                 lambda receipt: receipt["completed"].update(model_entries=2),
                 lambda receipt: receipt["completed"].update(key="0" * 64),
                 lambda receipt: receipt["completed"].update(entry_sha256="0" * 64),
                 lambda receipt: receipt["completed"].update(payload_sha256="0" * 64),
                 lambda receipt: receipt["completed"].update(export_sha256="0" * 64),
                 lambda receipt: receipt.update(launch_sha256="0" * 64)]
        for edit in edits:
            with self.subTest(edit=edit):
                f = Fixture()
                f.runtime.after_launch = lambda runtime, job, edit=edit: rewrite_receipt(runtime, job, edit)
                result = f.run()
                self.assertEqual((result["status"], result["kind"]), ("failure", "invalid"))

    def test_optional_exact_inputs_and_unknown_loaded_file(self):
        f = Fixture()
        f.job["expected_inputs"] = {"program": "bst", "files": {"main.rs": f.job["input"]["sha256"]}, **f.job["semantic"]}
        f.job["expected_key"] = s.semantic_key(f.job["expected_inputs"])
        f.persist()
        self.assertEqual(f.run()["status"], "complete")
        f = Fixture()
        def corrupt(receipt):
            receipt["completed"]["inputs"]["files"]["unsealed.rs"] = s.digest(b"unsealed")
            receipt["completed"]["key"] = s.semantic_key(receipt["completed"]["inputs"])
        f.runtime.after_launch = lambda runtime, job: rewrite_receipt(runtime, job, corrupt)
        result = f.run()
        self.assertEqual((result["status"], result["kind"]), ("failure", "invalid"))
        self.assertIn("compiler file/producer", result["detail"])

    def test_real_launcher_mocked_exact_process_hard_limit_and_environment(self):
        # Exercise RealRuntime.launch while replacing every external operation.
        f = Fixture()
        class Output(io.BytesIO):
            def close(self):
                pass
            def fileno(self):
                return 7
        output = Output()
        runtime = s.RealRuntime()
        runtime.read = lambda path: output.getvalue()
        child = SimpleNamespace(pid=123, poll=mock.Mock(side_effect=[None, 0, 0]), wait=mock.Mock(return_value=0))
        def popen(command, **kwargs):
            kwargs["preexec_fn"]()
            kwargs["stdout"].write(b"closed mock log")
            return child
        with mock.patch("builtins.open", return_value=output), \
             mock.patch.object(s.subprocess, "Popen", side_effect=popen) as launch, \
             mock.patch.object(s.resource, "setrlimit") as setlimit, \
             mock.patch.object(s.Path, "read_text", return_value="VmRSS: 1024 kB\nVmHWM: 2048 kB\n"), \
             mock.patch.object(s.os, "fsync"), \
             mock.patch.object(s.time, "sleep"), \
             mock.patch.object(s.time, "monotonic", side_effect=[0.0, 0.1, 0.2]):
            result = runtime.launch(f.job, "/jobs/bst", f.job_hash)
        self.assertEqual(launch.call_count, 1)
        self.assertEqual(launch.call_args.args[0], ["/worker-binary", "--ignored", "--exact", s.WORKER,
                                                  "--nocapture", "--test-threads=1"])
        cap = 256 * 1024 * 1024
        setlimit.assert_called_once_with(s.resource.RLIMIT_AS, (cap, cap))
        self.assertEqual(launch.call_args.kwargs["env"]["CRAT_ERA5_LAUNCH_DIGEST"], f.job["launch"]["sha256"])
        self.assertEqual(launch.call_args.kwargs["env"]["CRAT_ERA5_EXECUTION_ROLE"], "derive")
        self.assertEqual(result["enforcement"]["address_space_bytes"], cap)
        self.assertEqual(result["enforcement"]["wall_seconds"], 14400)
        self.assertEqual(result["peak_rss_kib"], 2048)
        self.assertEqual(result["log_sha256"], s.digest(b"closed mock log"))
        self.assertIsNone(result["limit"])


if __name__ == "__main__":
    unittest.main()
