"""relay 141 item 3: re-pin every proof.* row to central's frozen print of 10-11 (crat-proof ARTIFACT/frozen-2026-10-11/).
Reads origin/main of crat-proof with git show; checks every count against the print's own files; writes staged.tsv."""
import json, re, subprocess
P = "crat-proof"; D = "ARTIFACT/frozen-2026-10-11"
REC = "scratch/analysis-fanout/r141/record-current.md"
def die(m): raise SystemExit("stage_proof: FAIL: " + m)
def need(c, m):
    if not c: die(m)
def show(path, rev="origin/main"):
    return subprocess.run(["git", "-C", P, "show", rev + ":" + path], capture_output=True, text=True, check=True).stdout
man = json.loads(show(D + "/manifest.json")); ver = json.loads(show(D + "/verification.json"))
glob_ = json.loads(show(D + "/global-assumptions.json")); steps = show(D + "/step-lemmas-list.md")
FS = man["frozen_source_commit"]; need(FS == ver["frozen_source_commit"] == "d78ed85679b2c5c22de791cc966190ba7d43f103", "source commit")
need(man["counts"] == {"A": 15, "X": 8, "B": 2, "main": 23} == ver["artifact_counts"], "counts")
need(man["discharged"] == ver["discharged"] == 12 and man["remaining"] == ver["remaining"] == 30, "rows")
need(man["kernel_checks_complete"] and man["publication_ready"] and man["publication_STOP"] is None, "publication")
need(man["publication_resolution"]["frozen_formal_text_unchanged"] is True, "frozen text")
part1 = steps.split("## Part 1")[1].split("## Extension X")[0]
a4 = [l for l in part1.splitlines() if l.startswith("| *(paper session)* | A.4 |")]
need(len(a4) == 14, "A.4 rows %d" % len(a4))
need(len([l for l in part1.splitlines() if l.startswith("| *(paper session)*")]) == 15, "A rows")
disc = steps.split("## Discharged rows")[1].split("\n## ")[0]
need(len([l for l in disc.splitlines() if l.startswith("| *")]) == 12, "discharged rows")
need("**Counts (status of record, the index's own fields):** 42 rows, 12 discharged, 30 remaining" in steps, "42 rows")
need(sorted(glob_["A"]["names"]) == ["Classical_Prop.classic", "IndefiniteDescription.constructive_indefinite_description"]
     and glob_["X"]["names"] == [] == glob_["B"]["names"], "globals")
adeq = show("theories/Adequacy.v", FS)
m = re.search(r"Definition admitted_ambient \(P : main_predicates\) \(ctx : main_context\) : Prop :=(.*?)\.\n", adeq, re.S)
conds = [c.strip().split()[0] for c in m.group(1).split("/\\")]
need(len(conds) == 14 and conds[0] == "DefinedSource_A", "conditions %s" % conds)
need("Adequacy.admitted_ambient P ctx ->" in show(D + "/statements-and-assumptions-A.txt"), "A print uses admitted_ambient")
files = [l for l in show("_CoqProject", FS).splitlines() if re.match(r"^theories/.*\.v$", l)]
lines = sum(show(f, FS).count("\n") for f in files)
need((len(files), lines) == (150, 209145), "theories %d %d" % (len(files), lines))
need(len(json.loads(show(D + "/frozen-source.json"))["theories"]) == 150, "frozen-source theories")

PRE = ("frozen print of 10-11 (relay 141 item 3, R972-1): crat-proof ARTIFACT/frozen-2026-10-11/ at origin/main c044aade9 (printed "
       "969d4c35d 09:59Z 'Print frozen theorem interfaces and preserve all remaining hypotheses', central 424; R975-2's code-output "
       "exception recorded at c044aade9 13:08Z with the frozen formal text unchanged); manifest.json: frozen_source_commit d78ed8567, "
       "accepted_theory_commit ef5690db3, counts A 15 / X 8 / B 2 / main 23, discharged 12, remaining 30, kernel_checks_complete true, "
       "publication_ready true; verification.json agrees (step_counts, artifact_counts, theory_sources_unchanged 150); the development is "
       "open again until 10-14 06:00Z (R972-1), so a second print may move the A counts and these rows are read again on it; "
       "analysis-fanout 117 (relay 141): ")
C = {
 "proof.rows": "42 rows (step-lemmas-list.md: '42 rows, 12 discharged, 30 remaining', the index's own fields); three further rows outside the claim (the secondary model) are not counted.",
 "proof.rows.discharged": "12 (manifest.json discharged; step-lemmas-list.md 'Discharged rows, with the lemma that replaced them (12)'); verification.json new_discharge_on_documentation_date false.",
 "proof.rows.remaining": "30 (manifest.json remaining) = A 15 + X 8 + B 2 + 5 rows in no theorem's footprint (step-lemmas-list.md 'MARKED': gap_A16_observation_preservation, gap_A18_retained_interference, gap_A18_later_source_fault, gap_BorrowCoverage_contract_accesses, gap_A4_contract_call_step).",
 "proof.A.step-lemmas": "15 (manifest.json counts.A; step-lemmas-list.md Part 1 'Theorem A (Tree Borrows): its step lemmas (15)': indices 4-10, 12-14, 18-21, 27).",
 "proof.A4.step-lemmas": "14: the Part 1 rows whose package is A.4 (step-lemmas-list.md), i.e. Theorem A's 15 less gap_A7_A20_tree_nonretag_interfaces (index 27, package A.7/A.20).",
 "proof.X.step-lemmas": "8 (manifest.json counts.X; step-lemmas-list.md 'Extension X: its step lemmas (8)': indices 34-41, ExtensionX_Assembly.v:1580-1629). R977-1 (USER, addendum 977): the extension to owning types is out of this submission, so the paper does not use this key; it stays as the print's count until a relay retires it.",
 "proof.main.step-lemmas": "23 (manifest.json counts.main) = A 15 + X 8. R977-1 (USER, addendum 977): with the extension out of the submission the paper's N is proof.A.step-lemmas (15), not this key; it stays as the print's count until a relay retires it.",
 "proof.B.step-lemmas": "2 (manifest.json counts.B; step-lemmas-list.md 'Source responsibility: its step lemmas (2)': gap_B_source_step_accounting, gap_B_endpoint_correspondence, PARKED - OPEN). R977-1 (USER, seat addendum 977, 13:11Z, after relay 141): the ownership-conservation result is out of the paper, so the paper does not use this key; it stays as the print's count until a relay retires it.",
 "proof.conditions.A": "14: the conjuncts of Adequacy.admitted_ambient at the frozen source commit (theories/Adequacy.v:100-105: " + ", ".join(conds) + "), the premise of theorem_A_tree_borrows_statement in statements-and-assumptions-A.txt.",
 "proof.axioms.global": "2: global-assumptions.json A = IndefiniteDescription.constructive_indefinite_description and Classical_Prop.classic (Rocq's standard library); X and B closed under the global context (verification.json exported_global_axioms).",
 "proof.admitted": "0: Admitted, admit, give_up, Axiom(s), Parameter(s), Conjecture outside comments and strings in the 150 _CoqProject theories at d78ed8567: 0 each (r141/proof/scan.py; control: the same scan at f87c2aef7 reproduces 098's 129 files, 0 each). Unproved rows are Section Hypotheses (gap_*), not Admitted.",
 "proof.theory-files": "150 Rocq theory files at the frozen source commit d78ed8567: theories/*.v exactly as listed in its _CoqProject (-Q theories crat_proof), = frozen-source.json's 150 hashed theories and verification.json theory_sources_unchanged 150; vendor/, REPORTS/ and NOTES/ excluded. Control: the same count at f87c2aef7 reproduces 098's 129. previously at f87c2aef7: 129",
 "proof.theory-lines": "209,145 total lines of the 150 theory files at d78ed8567 (r141/proof/scan.py; control: f87c2aef7 reproduces 098's 201,918). previously at f87c2aef7: 201918",
 "proof.rocq-version": "Coq 8.20.1: not in the print; ENV.md at d78ed8567 (coq / coq-core / coq-stdlib 8.20.1, lines 178-183), unchanged from 098's reading.",
 "proof.tb-artifact": "not in the print; proof-package/SEALS.md:50-51 at d78ed8567 (10.5281/zenodo.15002703, coq_artifact.zip MD5 2459c03c413abaec74c8bd83bfaa61f8) and NOTES/bootstrap-inputs.md:58-65, unchanged from 098's reading.",
}
VAL = {"proof.rows": "42", "proof.rows.discharged": "12", "proof.rows.remaining": "30", "proof.A.step-lemmas": "15",
       "proof.A4.step-lemmas": "14", "proof.X.step-lemmas": "8", "proof.main.step-lemmas": "23", "proof.B.step-lemmas": "2",
       "proof.conditions.A": "14", "proof.axioms.global": "2", "proof.admitted": "0", "proof.theory-files": "150",
       "proof.theory-lines": "209145", "proof.rocq-version": "Coq 8.20.1",
       "proof.tb-artifact": "Tree Borrows artifact v1, DOI 10.5281/zenodo.15002703"}
rec = {}
for l in open(REC):
    c = [x.strip() for x in l.split("|")]
    if len(c) > 6 and c[1].startswith("proof."): rec[c[1]] = c[2]
need(set(rec) == set(VAL), "record proof keys %s" % sorted(set(rec) ^ set(VAL)))
with open("staged.tsv", "w") as f:
    f.write("key\tvalue_now\tvalue_58ppp\tverdict\tcause\n")
    for k in sorted(VAL):
        v = VAL[k]; verdict = "equal" if rec[k] == v else "differs"
        cause = PRE + C[k]
        need("|" not in cause and "\t" not in cause, k)
        f.write("\t".join([k, rec[k], v, verdict, cause]) + "\n")
        print(k, rec[k], "->", v, verdict)
