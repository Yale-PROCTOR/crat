"""r140 census group: rq2.wins.decl / rq2.ties.decl RECOUNTED under R945-1 (relay 139 rulings: CROWN's counter in full, as
Tables 4/5): per program, our declarations made safe (ours_made, Table 5's rq1.<p>.decl.delivered) against CROWN's
(crown_made) over the same U declarations; win = ours > CROWN, tie = equal. Input: a t5r945 per-program.tsv (read-only)."""
import csv, sys
for path in sys.argv[1:]:
    rows = list(csv.DictReader(open(path), delimiter='\t'))
    w = [r['program'] for r in rows if int(r['ours_made']) > int(r['crown_made'])]
    t = [r['program'] for r in rows if int(r['ours_made']) == int(r['crown_made'])]
    l = [r['program'] for r in rows if int(r['ours_made']) < int(r['crown_made'])]
    wt = [r['program'] for r in rows if int(r['ours_twin_made']) > int(r['crown_made'])]
    tt = [r['program'] for r in rows if int(r['ours_twin_made']) == int(r['crown_made'])]
    print(path); print(f'  programs {len(rows)}; wins {len(w)} {w}; ties {len(t)} {t}; losses {len(l)} {l}')
    print(f'  (twin reading, information: wins {len(wt)} {wt}; ties {len(tt)} {tt})')
