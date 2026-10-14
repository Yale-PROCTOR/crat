#!/usr/bin/env python3
"""cvformals146.py <base-census> <census>: the 11 call-view formals of premise.bridge-dereferenceable.call-view (record provenance; its #N is the parameter index, so the match is fn::name#)
-- family / model_kind / decision / reason in each census's <p>.raw-boundary-subjects.tsv. Read-only; fails closed via SystemExit."""
import csv, sys
csv.field_size_limit(10 ** 9)
F11 = [('binn', 'binn_list_get::psize#'), ('binn', 'binn_map_get::psize#'), ('binn', 'binn_object_get::psize#'),
       ('binn', 'IsValidBinnHeader::pheadersize#'), ('binn', 'IsValidBinnHeader::ptype#'), ('binn', 'binn_get_type_info::pextra_type#'),
       ('brotli', 'CopyStat::input_path#'), ('heman', 'kmQuaternionRotationMatrix::pIn#'), ('heman', 'heman_color_from_cpcf::texture#'),
       ('json.h', 'json_parse_ex::result#'), ('libtree', 'print_error::runpath#')]
def load(C):
    out = {}
    for p, suf in F11:
        rows = [r for r in csv.DictReader(open(f'{C}/{p}.raw-boundary-subjects.tsv'), delimiter='\t', quoting=csv.QUOTE_NONE)
                if r['subject_key'].endswith('::' + suf) or (suf.endswith('#') and ('::' + suf) in r['subject_key'])]
        if len(rows) != 1:
            raise SystemExit(f'{C} {p} {suf}: {len(rows)} rows')
        r = rows[0]
        out[(p, suf)] = (r['subject_key'], r['family'], r['model_kind'], r['decision'], r['reason'])
    return out
a, b = load(sys.argv[1].rstrip('/')), load(sys.argv[2].rstrip('/'))
same = 0
for k in a:
    print(k[0], a[k][0], a[k][1:], '->', b[k][1:], 'SAME' if a[k] == b[k] else 'MOVED')
    same += a[k] == b[k]
print(f'call-view formals identical: {same} / {len(a)}')
