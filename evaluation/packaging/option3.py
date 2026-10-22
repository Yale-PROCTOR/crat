#!/usr/bin/env python3
"""Option 3 (relay 005 s0, zip only): the legacy rewriter out. Keeps exactly what the BO code uses:
rewriter::collector::collect_fn_ptrs and rewriter::diagnostics::DiagnosticsMode, plus rewriter::Config."""
import os, re, sys
W = os.environ['W'].rstrip('/')
R = W + '/crates/pointer_replacer/src/rewriter/'
# 1. collector.rs -> collect_fn_ptrs only (the last item of the file)
s = open(R + 'collector.rs').read()
i = s.index('pub fn collect_fn_ptrs(')
body = s[i:]
collector = '''use rustc_hash::FxHashSet;
use rustc_hir::{
    ExprKind, QPath, TyKind,
    def::{DefKind, Res},
    intravisit::{Visitor, walk_expr},
};
use rustc_span::def_id::LocalDefId;

use crate::utils::rustc::RustProgram;

''' + body
open(R + 'collector.rs', 'w').write(collector)
# 2. diagnostics.rs -> DiagnosticsMode only
s = open(R + 'diagnostics.rs').read()
i = s.index('pub enum DiagnosticsMode {')
j = s.index('impl DiagnosticsMode {')
k = s.index('\n}\n', j) + 3
head = s[:i]
derive = ''
m = re.search(r'(#\[derive\([^\n]*\)\]\n)$', head)
if m: derive = m.group(1)
open(R + 'diagnostics.rs', 'w').write(derive + s[i:k])
# 3. rewriter/mod.rs -> Config + the two modules
open(R + 'mod.rs', 'w').write('''use rustc_hash::FxHashSet;
use serde::Deserialize;

pub(crate) mod collector;
pub(crate) mod diagnostics;

#[derive(Debug, Default, Clone, Deserialize)]
pub struct Config {
    pub c_exposed_fns: FxHashSet<String>,
    #[serde(default)]
    pub verbose: bool,
}
''')
for f in ['decision.rs', 'lifetimes.rs', 'epoch_split.rs', 'struct_array_field_pre.rs', 'array_local_index_rewriter.rs', 'array_local_trace.rs']:
    p = R + f
    if os.path.exists(p): os.remove(p); print('   removed', 'rewriter/' + f)
import shutil
if os.path.isdir(R + 'transform'): shutil.rmtree(R + 'transform'); print('   removed rewriter/transform/')
# 4. lib.rs: the legacy entry points out of the public API
p = W + '/crates/pointer_replacer/src/lib.rs'; s = open(p).read()
s2 = re.sub(r'pub use rewriter::\{[^}]*\};', 'pub use rewriter::Config;', s, flags=re.S)
assert s2 != s, 'lib.rs export not found'
open(p, 'w').write(s2); print('   lib.rs: pub use rewriter::Config')
# 5. analyses/mod.rs: the legacy-only analyses out (the orphan sweep removes their files)
p = W + '/crates/pointer_replacer/src/analyses/mod.rs'; s = open(p).read()
gone = []
for m in ['array_local_provenance', 'fn_ptr_groups', 'fn_ptr_rewrite_decision', 'nullity', 'ownership', 'struct_array_field', 'struct_copy']:
    n = re.subn(r'^\s*(pub(\([a-z]+\))? )?mod ' + m + r';\s*\n', '', s, flags=re.M)
    s, c = n
    if c: gone.append(m)
open(p, 'w').write(s); print('   analyses/mod.rs: removed', gone)
