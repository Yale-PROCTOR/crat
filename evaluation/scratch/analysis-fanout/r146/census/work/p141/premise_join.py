#!/usr/bin/env python3
"""Join the accepted model's premise-receipted retirement discharges
(out/<p>.final-discharged.jsonl, from final_discharges.py) to the frame-14
census through the r100 slot index (reverse-index.tsv).
A row 'rests on' a premise when its receipt carries the premise tag
(retirement.rs:101-123 at 4a47f16f7).  site = the release event
(source.function, block, statement, role); declaration = a census subject
(or field transaction / return certificate) delivered with the target slot
behind it (reverse-index behind_delivered=1)."""
import json, glob, os, csv, collections, sys
import sys as _s141; _s141.path.insert(0, 'scratch/analysis-fanout/r146/census/work'); import frame146  # r141: FRAME=58pp (control) | s39
RI = 'scratch/analysis-fanout/r146/census/work/g088b/keymap141/' + frame146.FRAME + '/reverse-index.tsv'  # r141
OUT141 = 'scratch/analysis-fanout/r146/census/cache/s17/' + {'s39': 'out-s39', '60sp': 'out-60sp'}[frame146.FRAME]  # r146
ri = {}
with open(RI) as f:
    for r in csv.DictReader(f, delimiter='\t'):
        ri[(r['program'], r['slot_key'])] = r
PREM = {'typed-release': 'premise=typed-release@R604-1', 'realloc-nonzero': 'premise=realloc-nonzero@R684-1'}
tot = collections.defaultdict(collections.Counter)
detail = open('premise-targets.tsv', 'w')
detail.write('premise\tprogram\ttarget\treceipts\tevents\tslot_kind_class\tmodel_kind_l01p14\tbehind_delivered\tdelivered_roles\tdelivered_by\tsubject_key\n')
sites = open('premise-sites.tsv', 'w')
sites.write('premise\tprogram\tevent_function\tblock\tstatement\trole\treceipts\ttargets\n')
for prem, tag in PREM.items():
    print('==', prem)
    for f in sorted(glob.glob(OUT141 + '/*.final-discharged.jsonl')):
        p = os.path.basename(f).split('.final')[0]
        rec = 0; ev = collections.defaultdict(lambda: [0, set()]); tg = collections.defaultdict(lambda: [0, set()])
        for line in open(f):
            if tag not in line: continue
            r = json.loads(line)
            if tag not in r['receipt']: continue
            rec += 1; s = r['source']; e = (s['function'], s['block'], s['statement'], s['role'])
            ev[e][0] += 1; ev[e][1].add(r['target']); tg[r['target']][0] += 1; tg[r['target']][1].add(e)
        if not rec: continue
        decl = set(); miss = 0; behind = 0; kinds = collections.Counter(); cls = collections.Counter()
        for t, (n, es) in sorted(tg.items()):
            x = ri.get((p, t))
            if x is None:
                miss += 1; detail.write(f'{prem}\t{p}\t{t}\t{n}\t{len(es)}\tNOT-IN-INDEX\t-\t-\t-\t-\t-\n'); continue
            kinds[x['model_kind_l01p14']] += 1; cls[x['slot_kind_class']] += 1
            if x['behind_delivered'] == '1':
                behind += 1
                for d in x['delivered_by'].split(','):
                    decl.add(d)
            detail.write('\t'.join([prem, p, t, str(n), str(len(es)), x['slot_kind_class'], x['model_kind_l01p14'], x['behind_delivered'], x['delivered_roles'], x['delivered_by'], x['subject_key']]) + '\n')
        for e, (n, ts) in sorted(ev.items()):
            sites.write('\t'.join([prem, p, e[0], str(e[1]), str(e[2]), e[3], str(n), str(len(ts))]) + '\n')
        print(f'{p}\treceipts={rec}\tsites={len(ev)}\ttargets={len(tg)}\tnot_in_index={miss}\tkinds={dict(kinds)}\tclass={dict(cls)}\ttargets_behind_delivered={behind}\tdeclarations={len(decl)}')
        t = tot[prem]; t['receipts'] += rec; t['sites'] += len(ev); t['targets'] += len(tg); t['behind'] += behind; t['declarations'] += len(decl); t['programs'] += 1
        with open(f'decl-{prem}.txt', 'a') as o:
            for d in sorted(decl): o.write(f'{p}\t{d}\n')
    print('TOTAL', prem, dict(tot[prem]))
