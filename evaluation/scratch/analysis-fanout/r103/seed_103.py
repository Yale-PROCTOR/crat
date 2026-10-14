#!/usr/bin/env python3
"""relay 103: pre-register the pair-rule hold keys (pending, empty, measured at 57's census on the new frame of record) + the raw-twin keys."""
import sys
NR = sys.argv[1]
P = ('PRE-REGISTERED (relay 103, analysis-fanout 079): EMPTY until 57\'s census on the frame of record then current (the uniform-objective frame, R858-1, once landed). '
     'The pair rule (R833-1): at a call inside the program, a pair that may overlap keeps both sides raw. ')
F = ('Figures of record today, for provenance only (first order, NOT values): at the L01^14 frame census the pending-hold subjects 140 (136 parameters, 4 locals; '
     'main 181 section 3; agents/artifacts/2026-10-06-main-179b/hold-price-frame14.tsv), the raw-view peers 73 (all parameters; 65 beyond the 140, union 205; raw-view-peers-frame14.tsv); '
     'at 54\' 141 / 75 (R833-1, main 181 section 3); rq5.pair.not-proven 461. ')
rows = [
 ('hold.pair.caller.subjects', 'decided', 'count', P + F + 'This key: the caller-side hold (R855-1; main\'s decision-layer hold, local/main-57-hold @ bf193febd, pending_hold.rs:82-86): the source declarations decided raw because a pair at one of their calls is not shown disjoint (reason held:pair-not-shown-disjoint), counted by declaration; the hold recurses up the call chain (a held formal is a raw target for its own callers, bo_rewriter/mod.rs:8753-8755).'),
 ('hold.pair.caller.delivered-lost', 'delivered', 'count', P + F + 'This key: delivered declarations the caller-side hold withdraws, by identity against the same frame\'s census without the hold (the held declarations and any sibling the signature-class hold takes with them; plan/mod.rs:1601 exempts no such reason, not yet measured).'),
 ('hold.pair.callee.formals', 'decided', 'count', P + F + 'This key: the callee-side peer rule (wave-5d; 8bbe20565, rebuilt in 883bb1f6b / 2872a4bc3): the callee formals held raw for every caller because a peer at some call is raw and the pair is not shown disjoint (co_conversion.rs:1491-1495, 1687-1706 at 8bbe20565), including peers with no pair row (the rebuilt line). At wave-5d 137 f14b: 4 formals (heman, libzahl, lodepng), 18 peers left unheld by 8bbe20565.'),
 ('hold.pair.callee.delivered-lost', 'delivered', 'count', P + F + 'This key: delivered declarations the callee-side rule withdraws. The held formal keeps a Pair arm raw_form_discharges does not pay, so plan/mod.rs:1585-1622 holds the callee\'s whole signature class (blocked-subject:pair-not-shown-disjoint), body locals included. At wave-5d 137 (f14b vs f14a, the eighteen, NOT against the record): -9 = 4 held formals + 5 siblings (heman -4, libzahl -4, lodepng -1; copy_row, zdiv, zsub, removePaddingBits drop to 0 delivered).'),
 ('hold.pair.callee.sibling-lost', 'delivered', 'count', P + F + 'This key: of hold.pair.callee.delivered-lost, the sibling declarations (not the held formals) withdrawn with the callee\'s signature class. At wave-5d 137 f14b: 5.'),
]
txt = open(NR).read().rstrip('\n') + '\n'
for k, l, u, p in rows:
    assert f'| {k} |' not in txt and '|' not in p
    txt += f'| {k} |  | pending | {l} | {u} | {p} |\n'
T = ('at the frame of record L01^14 (landed 2026-10-06, R852-1): the emitted trees of census scratch/main/frame14 (code 4a47f16f7); analysis-fanout 079 (relay 103 S13). '
     'The raw twin __crat_raw_<callee> (counted_void.rs:605-609, insert_raw_twin :2541-2597, calls renamed :649-651): a clone of the input callee with its raw formals, '
     'called at a call that could not be split (counted-void RawTwin, :565-574, 1043-1101, 1195-1213; aliased-storage twin R408-7, :1544-1605, seam.rs:5372-5423, PAIR-owned calls excluded :5375-5386), '
     'while every other caller keeps the converted signature; leaf callees only (:1149-1191), and only when the callee\'s signature is converted (:2380-2392). Re-seeded at the next frame of record. ')
for k, v, p in [('codegen.raw-twin.functions', '18', T + 'Twins printed in the emitted trees: binn 2, brotli 7, bzip2 1, heman 6, lodepng 2.'),
                ('codegen.raw-twin.calls', '31', T + 'Calls to a twin printed in the emitted trees: binn 4, brotli 9, bzip2 1, heman 11, lodepng 6 (the plan has 62 rows; the other 31 name callees whose signature was never converted, so no twin is printed); 4 of the 31 are A5 raw-view sites, 0 carry a pair row.')]:
    assert f'| {k} |' not in txt and '|' not in p
    txt += f'| {k} | {v} | pending | delivered | count | {p} |\n'
open(NR, 'w').write(txt); print('ok')
