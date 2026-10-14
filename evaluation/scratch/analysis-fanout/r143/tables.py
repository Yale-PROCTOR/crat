"""relay 143: write inator-table.tsv (per program buckets) and positions-both.tsv (every position on both sides)."""
import json, collections, csv
R = json.load(open('reconcile.json')); S = R['summary']; inj = json.load(open('inator-positions.json'))
P = ["running-example", "ulidgen", "leftpad", "amp", "nandc", "rbtree", "carrays", "jccc", "tisp"]
B = ["ref", "mut", "box", "rc", "cell", "refcell", "ghost", "other"]
with open('inator-table.tsv', 'w') as f:
    f.write("program\tpositions\t" + "\t".join(B) + "\tfnptr\tunmatched\tbinary\n")
    tot = collections.Counter(); tp = tf = tu = 0
    for p in P:
        b = S[p]['buckets']; un = len(S[p]['only_inator']) + len(S[p]['only_c2rust'])
        f.write("\t".join([p, str(S[p]['both'])] + [str(b.get(k, 0)) for k in B] + [str(S[p]['fnptr']), str(un), inj['out'][p]['binary']]) + "\n")
        tot.update(b); tp += S[p]['both']; tf += S[p]['fnptr']; tu += un
    f.write("\t".join(["total", str(tp)] + [str(tot.get(k, 0)) for k in B] + [str(tf), str(tu), "-"]) + "\n")
with open('positions-both.tsv', 'w') as f:
    w = csv.writer(f, delimiter='\t', lineterminator='\n')
    w.writerow(["program", "kind", "owner", "index", "name", "c2rust_type", "inator_type", "inator_source_type", "bucket", "ghost_inner"])
    for r in R['rows']:
        w.writerow([r['program'], r['kind'], r['owner'], r['index'], r['name'], r['c2rust'], r['inator'], r['inator_stype'], r['bucket'], r['ghost_inner']])
