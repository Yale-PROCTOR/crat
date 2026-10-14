import sys, collections, importlib.util, csv, glob, os
spec = importlib.util.spec_from_file_location('c57', 'scratch/main/clause57.py')
c57 = importlib.util.module_from_spec(spec); sys.argv_save = sys.argv
src = open('scratch/main/clause57.py').read().split("\nif __name__")[0]
exec(compile(src, 'clause57', 'exec'), c57.__dict__)
csv.field_size_limit(10**9)
for d in sys.argv[1:]:
    safe, delivered, reason = c57.load(d)
    held = collections.Counter(); heldp = collections.Counter()
    for k in safe:
        kd = c57.kind(*reason[k])
        if kd and not kd.startswith('cascade'):
            held[kd] += 1; heldp[k[0]] += 1
    dp = collections.Counter(p for p, _ in delivered)
    print(d, 'safe', len(safe), 'delivered', len(delivered), 'first-order', sum(held.values()), dict(held))
    print('  holds by program', dict(sorted(heldp.items())))
    print('  delivered by program', dict(sorted(dp.items())))
