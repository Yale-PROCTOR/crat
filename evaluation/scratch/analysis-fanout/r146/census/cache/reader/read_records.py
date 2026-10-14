#!/usr/bin/env python3
"""r110 (copy of r088 reader, SOLVE re-pointed to L01^14u): stream the L01^14u solve cache entries and read, per program,
what the records say about guarded repair, rounds, pins, field-own repair and
Unknown/timeouts.

Read-only. One entry at a time, streamed with ijson (yajl2_c); the parse stops
at the top-level `origin` key (everything read here lives before it).
Semantics (code at d09892164, crates/pointer_replacer/src/analyses/borrow_ownership/):
  * receipt repair keys: construction.rs:667-705 (repair_keys).
  * retirement-rounds: one record per validation round of EVERY verify_rounds
    run inside the worker's single capture scope (borrow_verify.rs:247-255,
    1313-1446; export.rs:1034-1052 never clears retirement_rounds;
    era5_worker.rs:338 + construction.rs:1738-1753 = one scope for both
    verifications). `round` = global ordinal (portable_export.rs:1250-1253).
  * demand-evidence: one construction per KindSolver (construction.rs:1215/1427),
    one epoch per selector solve (solver.rs:929-949, 3219), so epochs per
    construction = solve_round calls of that verification (all runs).
  * pins: a round whose RetirementReview has demotions with non-empty chains
    (local_outcome.rs:165-173; borrow_verify.rs:1458-1497).
  * |K| = len(universe) (model_cache.rs:667-684) = n of round_cap
    (borrow_verify.rs:2752-2763) = Planner slot_count (borrow_verify.rs:1272-1281).
"""
import collections
import glob
import json
import os
import re
import sys
import time

import ijson

# r141: SOLVE from env READER_SOLVE (control: era5c-l01p14u-solve; 58''': era5c-r211-s39pp); OUT = READER_OUT
SOLVE = os.environ["READER_SOLVE"]
CACHE = SOLVE + "/cache/era5b-model-cache-v1"
OUT = os.environ["READER_OUT"]

LOCAL_KEY = re.compile(r"::_\d+@d\d+$")

RR = "exports.families.retirement-rounds.records.item"
RRF = RR + ".fields"
DE = "exports.families.demand-evidence.records.item.fields.constructions.item"
RC = "exports.families.residual-conflicts.records.item"
FAM = "exports.families."


def is_field(key):
    return LOCAL_KEY.search(key) is None


def read_entry(path):
    s = {
        "universe": 0, "universe_fields": 0,
        "model_kinds": collections.Counter(), "model_field_kinds": collections.Counter(),
        "baseline_field_kinds": collections.Counter(),
        "receipt": None, "families": collections.Counter(),
        "rr": [], "cons": [], "residual": [], "final_round": None,
    }
    rec = None      # current retirement-rounds record
    con = None      # current demand construction
    q = None        # current query
    fsel = None     # current final selection
    res = None      # current residual record
    with open(path, "rb") as f:
        for prefix, event, value in ijson.parse(f):
            if prefix == "origin":
                break
            if prefix == "universe.item":
                s["universe"] += 1
                if is_field(value):
                    s["universe_fields"] += 1
                continue
            if prefix.startswith("model.") and event == "string":
                k = prefix[6:]
                s["model_kinds"][value] += 1
                if is_field(k):
                    s["model_field_kinds"][value] += 1
                continue
            if prefix.startswith("baseline.") and event == "string":
                if is_field(prefix[9:]):
                    s["baseline_field_kinds"][value] += 1
                continue
            if prefix == "receipt":
                s["receipt"] = value
                continue
            if not prefix.startswith(FAM):
                continue
            # family record counts
            if prefix.endswith(".records.item") and event == "start_map":
                s["families"][prefix[len(FAM):].split(".")[0]] += 1
            # ---- retirement-rounds
            if prefix.startswith(RR):
                if prefix == RR:
                    if event == "start_map":
                        rec = {"round": None, "conflicts": 0, "demotions": 0, "chain": [],
                               "holders": [], "dem_fns": [], "dem_receipts": [],
                               "unresolved": 0, "discharged": 0, "targets": set()}
                    elif event == "end_map":
                        s["rr"].append(rec)
                        rec = None
                    continue
                if prefix == RRF + ".round":
                    rec["round"] = int(value)
                elif prefix == RRF + ".conflicts.item" and event == "start_map":
                    rec["conflicts"] += 1
                elif prefix == RRF + ".conflicts.item.target":
                    rec["targets"].add(value)
                elif prefix == RRF + ".demotions.item" and event == "start_map":
                    rec["demotions"] += 1
                elif prefix == RRF + ".demotions.item.chain.item":
                    rec["chain"].append(value)
                elif prefix == RRF + ".demotions.item.holder":
                    rec["holders"].append(value)
                elif prefix == RRF + ".demotions.item.function":
                    rec["dem_fns"].append(value)
                elif prefix == RRF + ".demotions.item.receipt":
                    rec["dem_receipts"].append(value)
                elif prefix == RRF + ".unresolved.item" and event == "start_map":
                    rec["unresolved"] += 1
                elif prefix == RRF + ".discharged.item" and event == "start_map":
                    rec["discharged"] += 1
                continue
            if prefix == ("exports.families.retirement-final.records.item.fields."
                          "stack_entry_acceptance.retirement_round"):
                s["final_round"] = int(value)
                continue
            # ---- demand-evidence
            if prefix.startswith(DE):
                if prefix == DE:
                    if event == "start_map":
                        con = {"id": None, "endpoints": 0, "queries": 0, "q_epochs": set(),
                               "q_outcomes": collections.Counter(), "q_phase": collections.Counter(),
                               "unknown_reasons": collections.Counter(), "fs": []}
                    elif event == "end_map":
                        s["cons"].append(con)
                        con = None
                    continue
                if prefix == DE + ".construction":
                    con["id"] = int(value)
                elif prefix == DE + ".endpoints.item" and event == "start_map":
                    con["endpoints"] += 1
                elif prefix == DE + ".queries.item":
                    if event == "start_map":
                        q = {"epoch": None, "state": None, "reason": None, "phase": None}
                    elif event == "end_map":
                        con["queries"] += 1
                        con["q_epochs"].add(q["epoch"])
                        con["q_outcomes"][q["state"]] += 1
                        con["q_phase"][q["phase"]] += 1
                        if q["state"] not in ("sat", "unsat"):
                            con["unknown_reasons"][str(q["reason"])] += 1
                        q = None
                elif q is not None and prefix == DE + ".queries.item.epoch":
                    q["epoch"] = int(value)
                elif q is not None and prefix == DE + ".queries.item.phase":
                    q["phase"] = value
                elif q is not None and prefix == DE + ".queries.item.outcome.state":
                    q["state"] = value
                elif q is not None and prefix == DE + ".queries.item.outcome.reason":
                    q["reason"] = value
                elif prefix == DE + ".final_selections.item":
                    if event == "start_map":
                        fsel = {"epoch": None, "state": None, "reason": None, "dropped": None}
                    elif event == "end_map":
                        con["fs"].append(fsel)
                        fsel = None
                elif fsel is not None and prefix == DE + ".final_selections.item.epoch":
                    fsel["epoch"] = int(value)
                elif fsel is not None and prefix == DE + ".final_selections.item.outcome.state":
                    fsel["state"] = value
                elif fsel is not None and prefix == DE + ".final_selections.item.outcome.reason":
                    fsel["reason"] = value
                elif fsel is not None and prefix == DE + ".final_selections.item.dropped":
                    if event == "start_array":
                        fsel["dropped"] = 0
                elif fsel is not None and prefix == DE + ".final_selections.item.dropped.item" \
                        and event == "start_map":
                    fsel["dropped"] += 1
                continue
            # ---- residual-conflicts (final accepting round only, export.rs:1096-1098)
            if prefix.startswith(RC):
                if prefix == RC:
                    if event == "start_map":
                        res = {"slots": []}
                    elif event == "end_map":
                        s["residual"].append(res)
                        res = None
                elif res is not None and event == "string" and "@d" in value:
                    res["slots"].append(value)
                continue
    return s


def parse_receipt(text):
    out = {}
    for line in (text or "").splitlines():
        if "=" in line:
            k, v = line.split("=", 1)
            out[k] = v
    return out


def parse_fallbacks(text):
    # "<reason>@rounds:<r>@commits:<c>,..."  (construction.rs:690-701)
    rows = []
    if not text:
        return rows
    for part in text.split(","):
        m = re.match(r"^(.*)@rounds:(\d+)@commits:(\d+)$", part)
        rows.append((m.group(1), int(m.group(2)), int(m.group(3))) if m else (part, None, None))
    return rows


def split_runs(n_records, epochs, fallbacks):
    """Assign the global retirement-round ordinals to runs.

    Per verify_rounds run: records == stats.rounds (one finish_retirement per loop
    iteration, borrow_verify.rs:1313-1446, no early return in 423-712).
    Solves (= demand epochs): an accepting run solves once before round 1 and once
    after every non-accepting round => solves == rounds. A guarded run declined
    INSIDE a round (planner decline, field-conflict, source-retirement, empty-round
    cap) => solves == rounds; declined by a failed re-solve/initial solve
    (solver-unsat / solver-unknown, borrow_verify.rs:1046-1070) => solves == rounds+1.
    Returns (runs, status) with runs = list of (verification, run, rounds) or None.
    """
    if len(epochs) != 2:
        return None, "constructions!=2"
    e0, e1 = epochs
    fb = list(fallbacks)

    def solves(fbrow):
        reason, rounds, _ = fbrow
        return rounds + (1 if reason.startswith("solver-") else 0)

    candidates = []
    if len(fb) == 0:
        candidates.append([("baseline", "guarded", e0), ("precise", "guarded", e1)])
    elif len(fb) == 2:
        m0 = e0 - solves(fb[0])
        m1 = e1 - solves(fb[1])
        candidates.append([("baseline", "guarded-declined", fb[0][1]), ("baseline", "mode-a", m0),
                           ("precise", "guarded-declined", fb[1][1]), ("precise", "mode-a", m1)])
    elif len(fb) == 1:
        m0 = e0 - solves(fb[0])
        candidates.append([("baseline", "guarded-declined", fb[0][1]), ("baseline", "mode-a", m0),
                           ("precise", "guarded", e1)])
        m1 = e1 - solves(fb[0])
        candidates.append([("baseline", "guarded", e0),
                           ("precise", "guarded-declined", fb[0][1]), ("precise", "mode-a", m1)])
    else:
        return None, "fallbacks>2"
    ok = [c for c in candidates
          if all(r[2] is not None and r[2] >= 0 for r in c) and sum(r[2] for r in c) == n_records]
    if len(ok) == 1:
        return ok[0], "consistent"
    if len(ok) == 0:
        return None, "inconsistent(records=%d,epochs=%s,fallbacks=%s)" % (n_records, epochs, fb)
    # Both single-fallback assignments fit the counts (in-round decline):
    # the counts alone cannot name the verification that fell back.
    return None, "ambiguous:" + "|".join(
        ";".join("%s/%s=%d" % r for r in c) for c in ok)


def ledger_scan(program):
    path = os.path.join(CACHE, program + ".raw-cause-ledger.tsv")
    out = {"rows": 0, "retirement_raw": 0, "unknown_cells": 0, "field_forbid": 0,
           "retirement_raw_rounds": collections.Counter()}
    if not os.path.exists(path):
        return None
    with open(path) as f:
        header = f.readline().rstrip("\n").split("\t")
        ix = {h: i for i, h in enumerate(header)}
        for line in f:
            cells = line.rstrip("\n").split("\t")
            out["rows"] += 1
            if cells[ix["first_noref_kind"]] == "retirement-raw":
                out["retirement_raw"] += 1
                out["retirement_raw_rounds"][cells[ix["noref_round"]]] += 1
            if any(c.startswith("unknown") or c == "unprobed" for c in cells[1:]):
                out["unknown_cells"] += 1
            if "field-forbid" in line:
                out["field_forbid"] += 1
    return out


def main():
    # r141: completion and key from each worker receipt (workers/<p>.json completed.key); the S39 row's progress.jsonl
    # covers only its ten host-a solves (A2's ten were solved on host-b and copied in, era-5c 168 s3)
    order = sorted(os.path.basename(f)[:-5] for f in glob.glob(SOLVE + "/workers/*.json"))
    done = {}
    for p in order:
        w = json.load(open(os.path.join(SOLVE, "workers", p + ".json")))
        if w.get("completed") and w["completed"].get("key"):
            done[p] = {"key": w["completed"]["key"]}
    absent = [p for p in order if p not in done]
    progs = sorted(done, key=lambda p: os.path.getsize(os.path.join(CACHE, done[p]["key"] + ".json")))
    only = sys.argv[1:]
    if only:
        progs = [p for p in progs if p in only]
    log = open(os.path.join(OUT, "read_records.log"), "a")
    log.write("# run %s; complete=%d absent=%s\n" % (time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), len(done), absent))
    cols = ["program", "key", "entry_bytes", "repair", "guarded_verifications", "guarded_fallbacks",
            "fallback_reasons", "K", "K_fields", "planner_cap_10K+1", "loop_cap_10K+2", "modeA_cap_K+8",
            "rr_records", "final_round_ordinal", "demand_constructions", "epochs_per_construction",
            "run_split", "split_status", "max_run_rounds_vs_caps",
            "pin_rounds", "pin_rounds_by_run", "pin_slots", "pin_slot_sample",
            "unresolved_rounds", "field_own_evidence", "field_kinds_final", "field_kinds_baseline",
            "residual_records", "residual_field_records",
            "demand_query_outcomes", "demand_final_selection_outcomes", "unknown_reasons",
            "ledger_rows", "ledger_retirement_raw(rounds)", "ledger_probe_unknown_or_unprobed",
            "ledger_field_forbid_rows", "worker_log_flags", "parse_s", "rr_file_order_is_ordinal"]
    rows = []
    detail = {}
    for p in progs:
        key = done[p]["key"]
        path = os.path.join(CACHE, key + ".json")
        size = os.path.getsize(path)
        t0 = time.time()
        s = read_entry(path)
        dt = time.time() - t0
        r = parse_receipt(s["receipt"])
        fbs = parse_fallbacks(r.get("guarded_fallback_reasons"))
        K = s["universe"]
        cons = sorted(s["cons"], key=lambda c: c["id"])
        epochs = []
        for c in cons:
            ep = set(c["q_epochs"]) | {x["epoch"] for x in c["fs"]}
            epochs.append(len(ep))
        n = len(s["rr"])
        # Records are stored in key order, not ordinal order (the key is built from
        # "round", portable_export.rs:666); restore the ordinal order.
        file_order_sorted = [x["round"] for x in s["rr"]] == sorted(x["round"] for x in s["rr"])
        s["rr"].sort(key=lambda x: x["round"])
        ordinals = [x["round"] for x in s["rr"]]
        assert ordinals == list(range(n)), (p, "round ordinals are not 0..n-1")
        runs, status = split_runs(n, epochs, fbs)
        # attribute records to runs
        owner = [None] * n
        if runs:
            i = 0
            for v, kind, cnt in runs:
                for _ in range(cnt):
                    owner[i] = "%s/%s" % (v, kind)
                    i += 1
        pin_idx = [i for i, x in enumerate(s["rr"]) if x["chain"]]
        pin_by_run = collections.Counter(owner[i] or "?" for i in pin_idx)
        pin_slots = sorted({c for i in pin_idx for c in s["rr"][i]["chain"]})
        unresolved_idx = [i for i, x in enumerate(s["rr"]) if x["unresolved"]]
        res_field = sum(1 for x in s["residual"] if any(is_field(k) for k in x["slots"]))
        qo = collections.Counter()
        fo = collections.Counter()
        ur = collections.Counter()
        for c in cons:
            qo.update(c["q_outcomes"])
            fo.update(x["state"] for x in c["fs"])
            ur.update(c["unknown_reasons"])
            for x in c["fs"]:
                if x["state"] not in ("sat",):
                    ur["final:%s:%s" % (x["state"], x["reason"])] += 1
        led = ledger_scan(p)
        wlp = os.path.join(SOLVE, "workers", p + ".json.log")
        if not os.path.exists(wlp):  # r141: A2's ten (host-b) keep their logs in staging-A2/workers
            wlp = os.path.join(SOLVE, "staging-A2", "workers", p + ".json.log")
        wl = open(wlp).read()
        flags = [w for w in ("guarded_fallback", "l2_decline", "unknown", "timeout", "panicked", "E5C_ALSO")
                 if w in wl]
        if runs:
            mx = ";".join("%s/%s=%d" % r for r in runs)
            over = [r for r in runs if (r[1] == "mode-a" and r[2] > K + 8) or r[2] > 10 * K + 2]
            vs = "max=%d of planner %d / modeA %d%s" % (max(r[2] for r in runs), 10 * K + 1, K + 8,
                                                        " OVER" if over else "")
        else:
            mx, vs = "-", "-"
        row = {
            "program": p, "key": key, "entry_bytes": size,
            "repair": r.get("repair", "-"),
            "guarded_verifications": r.get("guarded_verifications", "-"),
            "guarded_fallbacks": r.get("guarded_fallbacks", "-"),
            "fallback_reasons": r.get("guarded_fallback_reasons", "-"),
            "K": K, "K_fields": s["universe_fields"],
            "planner_cap_10K+1": 10 * K + 1, "loop_cap_10K+2": 10 * K + 2, "modeA_cap_K+8": K + 8,
            "rr_records": n, "final_round_ordinal": s["final_round"],
            "demand_constructions": len(cons), "epochs_per_construction": ",".join(map(str, epochs)),
            "run_split": mx, "split_status": status, "max_run_rounds_vs_caps": vs,
            "pin_rounds": len(pin_idx),
            "pin_rounds_by_run": ";".join("%s=%d" % kv for kv in sorted(pin_by_run.items())) or "-",
            "pin_slots": len(pin_slots),
            "pin_slot_sample": ",".join(pin_slots[:4]) or "-",
            "unresolved_rounds": len(unresolved_idx),
            "field_own_evidence": "not-recorded",
            "field_kinds_final": ",".join("%s:%d" % kv for kv in sorted(s["model_field_kinds"].items())) or "-",
            "field_kinds_baseline": ",".join("%s:%d" % kv for kv in sorted(s["baseline_field_kinds"].items())) or "-",
            "residual_records": len(s["residual"]), "residual_field_records": res_field,
            "demand_query_outcomes": ",".join("%s:%d" % kv for kv in sorted(qo.items())) or "-",
            "demand_final_selection_outcomes": ",".join("%s:%d" % kv for kv in sorted(fo.items())) or "-",
            "unknown_reasons": ";".join("%s=%d" % kv for kv in sorted(ur.items())) or "-",
            "ledger_rows": led["rows"] if led else "-",
            "ledger_retirement_raw(rounds)": ("%d(%s)" % (led["retirement_raw"], ",".join(
                "r%s:%d" % kv for kv in sorted(led["retirement_raw_rounds"].items(), key=lambda kv: int(kv[0]) if kv[0].isdigit() else -1)))) if led else "-",
            "ledger_probe_unknown_or_unprobed": led["unknown_cells"] if led else "-",
            "ledger_field_forbid_rows": led["field_forbid"] if led else "-",
            "worker_log_flags": ",".join(flags) or "-",
            "parse_s": "%.1f" % dt,
            "rr_file_order_is_ordinal": file_order_sorted,
        }
        rows.append(row)
        detail[p] = {
            "receipt_repair": {k: v for k, v in r.items() if k.startswith(("repair", "guarded"))},
            "families": dict(s["families"]),
            "runs": runs, "split_status": status,
            "constructions": [{"id": c["id"], "endpoints": c["endpoints"], "queries": c["queries"],
                               "epochs": e, "q_outcomes": dict(c["q_outcomes"]), "q_phase": dict(c["q_phase"]),
                               "final_selections": [(x["epoch"], x["state"], x["reason"], x["dropped"]) for x in c["fs"]]}
                              for c, e in zip(cons, epochs)],
            "rounds": [{"ordinal": i, "run": owner[i], "conflicts": x["conflicts"], "targets": len(x["targets"]),
                        "demotions": x["demotions"], "chain": x["chain"], "holders": x["holders"],
                        "functions": sorted(set(x["dem_fns"])), "receipts": sorted(set(x["dem_receipts"])),
                        "unresolved": x["unresolved"], "discharged": x["discharged"]}
                       for i, x in enumerate(s["rr"])],
            "residual": s["residual"],
        }
        line = "%s size=%d parse=%.1fs K=%d rr=%d epochs=%s fb=%s split=%s pins=%d\n" % (
            p, size, dt, K, n, epochs, r.get("guarded_fallback_reasons", "-"), status, len(pin_idx))
        log.write(line)
        log.flush()
        sys.stderr.write(line)
    suffix = ("-" + "-".join(only)) if only else ""
    with open(os.path.join(OUT, "records%s.tsv" % suffix), "w") as f:
        f.write("\t".join(cols) + "\n")
        for row in rows:
            f.write("\t".join(str(row[c]) for c in cols) + "\n")
    with open(os.path.join(OUT, "records-detail%s.json" % suffix), "w") as f:
        json.dump({"absent": absent, "programs": detail}, f, indent=1, default=list)
    log.write("# absent (no complete 'program' event): %s\n" % absent)
    log.close()


if __name__ == "__main__":
    main()
