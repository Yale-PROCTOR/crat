#!/usr/bin/env python3
"""relay 108 (analysis-fanout), keys conf.fact.subjects, conf.cert.total, conf.cert.matched,
conf.retire.sites (and conf.retire.matched for the cross-check against ec2.mapped).

usage: conf_keys.py <census_dir> [<wave-6o conformance out dir with c1.txt/c2.txt>] > keys.tsv
       (also writes <scratch>/departures-<census basename>.tsv beside this script)

conf.fact.subjects : sum over programs of C1 FactFidelity `subjects=` (census subjects whose
                     consumed model_kind carries a key in the sealed entry), read from wave-6o's
                     c1.txt when given; recomputed independently from the census as the count of
                     <p>.raw-boundary-subjects.tsv rows with model_kind != 'unmodeled'.
conf.cert.total    : realized subjects (<p>.raw-boundary-subject-outcomes.tsv delivery =
                     realized-as-predicted) whose delivered class differs from the model kind
                     (survey analysis-fanout 008 / r5 factfidelity-r610 §(10)(b) method).
                     class(emitted_form): 'box' if 'box' in form; 'raw' if form in (raw, unchanged);
                     else 'ref'. model owning <-> class box.
conf.cert.matched  : of those, the ones whose `fn::local` (subject_key's last two '::' components,
                     '#N' stripped) equals the last two '::' components of a token of one of the
                     census's certificate receipts for the program: raw-boundary-box-param-receipt,
                     return-certificate-receipts, raw-boundary-allocator-contract-receipt,
                     raw-boundary-field-transactions (detail/subject columns, tokenised).
conf.retire.sites / .matched : sums of C2 RetainedLifecycle source_release_sites / matched (c2.txt).
"""
import csv, glob, os, re, sys, collections
csv.field_size_limit(1 << 30)
F = sys.argv[1].rstrip('/')
CONF = sys.argv[2] if len(sys.argv) > 2 else None
HERE = os.path.dirname(os.path.abspath(__file__))
CERT = [('box-param', '{p}.raw-boundary-box-param-receipt.tsv'),
        ('return-certificate', '{p}.return-certificate-receipts.tsv'),
        ('allocator-contract', '{p}.raw-boundary-allocator-contract-receipt.tsv'),
        ('field-transactions', '{p}.raw-boundary-field-transactions.tsv')]
META = {'corpus','analysis_frame','code_frame','raw_boundary_wave','data','build_profile',
        'resource_configured_mib','resource_effective_mib','a5_mode','a5_world','a5_attestation',
        'cache_manifest_sha256','launch_env_sha256','program'}
TOK = re.compile(r"[^\s=,\[\]\(\)\{\};'\"`<>|]+")

def last2(s):
    s = re.sub(r'(#\d+)?(@d\d+)?$', '', s)
    parts = s.split('::')
    return '::'.join(parts[-2:]) if len(parts) >= 2 else None

def cls(form):
    if 'box' in form: return 'owning'
    if form in ('raw', 'unchanged'): return 'raw'
    return 'ref'

progs = sorted(os.path.basename(f).split('.raw-boundary-subjects.tsv')[0]
               for f in glob.glob(F + '/*.raw-boundary-subjects.tsv'))
modeled = 0; total = 0; matched = 0
by_pair = collections.Counter(); by_fam = collections.Counter(); per_prog = {}
out = []
for p in progs:
    subj = {r['subject_key']: r for r in csv.DictReader(open(f'{F}/{p}.raw-boundary-subjects.tsv'), delimiter='\t')}
    modeled += sum(1 for r in subj.values() if r['model_kind'] != 'unmodeled')
    toks = collections.defaultdict(set)   # fam -> set of last2
    for fam, pat in CERT:
        path = f'{F}/' + pat.format(p=p)
        if not os.path.exists(path): continue
        for r in csv.DictReader(open(path), delimiter='\t'):
            for k, v in r.items():
                if k in META or v is None: continue
                for t in TOK.findall(v):
                    if '::' in t:
                        l2 = last2(t)
                        if l2: toks[fam].add(l2)
    pt = pm = 0
    for r in csv.DictReader(open(f'{F}/{p}.raw-boundary-subject-outcomes.tsv'), delimiter='\t'):
        if r['delivery'] != 'realized-as-predicted': continue
        mk = subj[r['subject_key']]['model_kind']; ef = r['emitted_form']
        if mk == 'unmodeled' or cls(ef) == mk: continue
        total += 1; pt += 1; by_pair[(mk, ef)] += 1
        l2 = last2(r['subject_key'])
        fams = [fam for fam, _ in CERT if l2 in toks[fam]]
        if fams: matched += 1; pm += 1; by_fam['+'.join(fams)] += 1
        out.append((p, r['subject_key'], mk, ef, '+'.join(fams) or '-'))
    if pt: per_prog[p] = (pm, pt)

tag = os.path.basename(F)
with open(os.path.join(HERE, f'departures-{tag}.tsv'), 'w') as fh:
    fh.write('program\tsubject_key\tmodel_kind\temitted_form\tcertificate_family_by_member\n')
    for row in out: fh.write('\t'.join(row) + '\n')

def conf_sum(fname, field):
    s = 0; n = 0
    for line in open(os.path.join(CONF, fname)):
        m = re.search(r'\b' + field + r'=(\d+)', line)
        if m: s += int(m.group(1)); n += 1
    return s, n

prov_dep = (f'{F}: realized subjects (subject-outcomes delivery=realized-as-predicted) whose delivered class '
            f'(box-forms=owning; raw/unchanged=raw; else ref) != subjects.model_kind; pairs '
            + ', '.join(f'{a}->{b} {c}' for (a, b), c in sorted(by_pair.items()))
            + '; per program matched/total ' + ', '.join(f'{p} {m}/{t}' for p, (m, t) in per_prog.items()))
print('key\tvalue\tprovenance')
if CONF:
    c1, n1 = conf_sum('c1.txt', 'subjects')
    print(f'conf.fact.subjects\t{c1}\t{CONF}/c1.txt: sum of subjects= over {n1} programs (wave-6o C1 FactFidelity); '
          f'cross-check from census: subjects.tsv rows with model_kind!=unmodeled = {modeled}')
else:
    print(f'conf.fact.subjects\t{modeled}\t{F}/*.raw-boundary-subjects.tsv rows with model_kind != unmodeled (C1 population)')
print(f'conf.cert.total\t{total}\t{prov_dep}')
print(f'conf.cert.matched\t{matched}\tof conf.cert.total, fn::local member-name join to the census certificate receipts '
      f'(box-param, return-certificate, allocator-contract, field-transactions); by family '
      + ', '.join(f'{k} {v}' for k, v in sorted(by_fam.items())) + f'; rows in departures-{tag}.tsv')
if CONF:
    s, n = conf_sum('c2.txt', 'source_release_sites'); m, _ = conf_sum('c2.txt', 'matched')
    print(f'conf.retire.sites\t{s}\t{CONF}/c2.txt: sum of source_release_sites= over {n} programs (wave-6o C2 RetainedLifecycle)')
    print(f'conf.retire.matched\t{m}\t{CONF}/c2.txt: sum of matched= over {n} programs (= ec2.mapped)')
