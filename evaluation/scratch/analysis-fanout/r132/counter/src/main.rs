//! rq2_pos_counter — analysis-fanout 031 (relay 043, R753-1): crat's TYPED pointer-position counter.
//!
//! usage: rq2_pos_counter --root <crate root .rs> --out <dir> [--universe <keys file>] [--strip-src] [--sites]
//!
//! r132 (relay 132) extension: `--sites` also writes `sites.tsv`, the raw-to-safe conversion sites (src/sites.rs; its
//! header defines every column) and `sites-status.txt` (`ok\t<rows>`, or `panic\t<message>`: the pass runs under
//! catch_unwind, so its panic never loses T1 / T2; `status.txt` stays T1 / T2's). T1 / T2 below are unchanged.
//!
//! Compiles one crate under crat's pinned nightly-2025-06-23 with the census's own configuration (copied from
//! `crates/utils/src/compilation.rs`: edition 2021, rlib, `deps_crate`'s rlibs as externs; lints capped at allow, so
//! only a hard error rejects a crate) and writes:
//!
//! `positions.tsv` (T1) — one row per pointer-like LAYER of every declaration:
//!   kind      param | return | local | field | static
//!   owner     `tcx.def_path_str` of the function / struct / static (`src::avl::insert`)
//!   name      the binding / field name (`_0` for a return)
//!   idx       params: the argument index; locals: the ordinal among same-named bindings of the function
//!   binding   locals: `typed` (`let x: T`), `untyped` (the type is typeck's), `byref` (a `ref`/`ref mut` binding,
//!             whose type is a reference to an existing place, c2rust's `let ref mut freshN`); `-` otherwise
//!   synthetic `yes` for a binding named `__crat_*` or produced by an expansion / desugaring
//!   depth     0 = the declared type's outermost layer; +1 under every pointer-like layer
//!   layer     the ordinal of the layer among the declaration's layers at that depth (tuples, arrays of pointers)
//!   form      raw-mut | raw-const | ref | mut-ref | slice-ref | slice-mut | str-ref | box | box-slice | cursor |
//!             cursor-mut | nonnull | opt-<any of these> (an `Option` around the layer)
//!   ctx       `-`; `elem` (inside an array / slice element); `arg` (inside another generic container's argument);
//!             `fnptr` (inside a function-pointer type's signature)
//!   type      the declaration's full type
//!
//! `uses.tsv` (T2) — per function:
//!   official       the usage instrument's registered rule on `mir_drops_elaborated_and_const_checked`: places outside
//!                  non-use contexts, rooted at a debug-named local whose `fn::name` is in --universe, whose projection
//!                  holds a Deref (its 2025 calibration is 12,172, analysis-fanout 031)
//!   official_raw   the same, keyed through the exposure wrapper's twin (`__crat_safe_f` read as `f`; the C-named
//!                  wrapper's body skipped when a twin exists) and restricted to raw-pointer-typed roots: the
//!                  REMAINING raw official uses on an output
//!   full_roots     every place, outside non-use contexts and cleanup blocks, rooted at ANY local whose declared type
//!                  is a raw pointer, whose projection holds a Deref — on `mir_promoted` (before the runtime passes,
//!                  so a Box dereference is a Box dereference, not a raw temporary)
//!   full_deref     every such place holding a Deref whose base type is a raw pointer, whatever its root's type
#![feature(rustc_private)]

extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_feature;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

mod sites;

use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    fmt::Write as _,
    fs,
    path::{Path, PathBuf},
    process::Command,
};

use rustc_data_structures::fx::FxHashMap;
use rustc_errors::{
    ColorConfig, DiagInner, Level,
    emitter::{Emitter, HumanEmitter},
    registry::Registry,
};
use rustc_feature::UnstableFeatures;
use rustc_hir::{
    self as hir, ByRef, OwnerNode,
    def::DefKind,
    intravisit::{self, Visitor as HirVisitor},
};
use rustc_interface::Config;
use rustc_middle::{
    mir::{
        Body, Local, Location, Place, PlaceRef, ProjectionElem, VarDebugInfoContents,
        visit::{PlaceContext, Visitor as MirVisitor},
    },
    ty::{self, Ty, TyCtxt},
};
use rustc_session::{
    EarlyDiagCtxt,
    config::{CrateType, ErrorOutputType, Input, Options},
};
use rustc_span::{def_id::LocalDefId, edition::Edition, source_map::SourceMap, sym};

// ---------------------------------------------------------------------------------------------------------------
// the compiler configuration: crates/utils/src/compilation.rs, copied (the census's verify configuration)

fn find_deps() -> Options {
    let mut args = vec!["a.rs".to_string()];
    let dir = std::env::var("DIR").unwrap_or_else(|_| "crat".to_owned());
    let dep = format!("{dir}/deps_crate/target/debug/deps");
    assert!(Path::new(&dep).exists(), "deps_crate not found at {dep}");
    if let Ok(entries) = fs::read_dir(&dep) {
        args.push("-L".to_string());
        args.push(format!("dependency={dep}"));
        for f in entries.flatten() {
            let f = f.file_name().to_str().unwrap().to_string();
            if !f.ends_with(".rlib") {
                continue;
            }
            let i = f.find('-').unwrap();
            let name = f[3..i].to_string();
            args.push("--extern".to_string());
            args.push(format!("{name}={dep}/{f}"));
        }
    }
    let mut handler = EarlyDiagCtxt::new(ErrorOutputType::default());
    let matches = rustc_driver::handle_options(&handler, &args).unwrap();
    rustc_session::config::build_session_options(&mut handler, &matches)
}

fn sys_root() -> PathBuf {
    if let Ok(s) = std::env::var("SYSROOT") {
        return PathBuf::from(s);
    }
    let out = Command::new("rustc").arg("--print").arg("sysroot").output().expect("rustc --print sysroot");
    PathBuf::from(String::from_utf8(out.stdout).unwrap().trim())
}

struct ErrorEmitter(HumanEmitter);

impl Emitter for ErrorEmitter {
    fn source_map(&self) -> Option<&SourceMap> {
        self.0.source_map()
    }
    fn emit_diagnostic(&mut self, diag: DiagInner, registry: &Registry) {
        if matches!(diag.level(), Level::Fatal | Level::Error) {
            self.0.emit_diagnostic(diag, registry);
        }
    }
    fn translator(&self) -> &rustc_errors::translation::Translator {
        self.0.translator()
    }
}

fn make_config(input: Input) -> Config {
    let opts = find_deps();
    Config {
        opts: Options {
            sysroot: sys_root(),
            search_paths: opts.search_paths,
            externs: opts.externs,
            unstable_features: UnstableFeatures::Allow,
            crate_types: vec![CrateType::Rlib],
            debug_assertions: false,
            edition: Edition::Edition2021,
            // `--cap-lints allow`: only a hard error rejects a crate (a deny-by-default lint does not)
            lint_cap: Some(rustc_session::lint::Level::Allow),
            ..Options::default()
        },
        crate_cfg: vec![],
        crate_check_cfg: vec![],
        input,
        output_dir: None,
        output_file: None,
        ice_file: None,
        file_loader: None,
        locale_resources: rustc_driver::DEFAULT_LOCALE_RESOURCES.to_vec(),
        lint_caps: FxHashMap::default(),
        psess_created: Some(Box::new(|ps| {
            let sm = ps.clone_source_map();
            let emitter = HumanEmitter::new(
                rustc_errors::emitter::stderr_destination(ColorConfig::Never),
                rustc_driver::default_translator(),
            )
            .sm(Some(sm));
            ps.dcx().set_emitter(Box::new(ErrorEmitter(emitter)));
        })),
        register_lints: None,
        override_queries: None,
        extra_symbols: vec![],
        make_codegen_backend: None,
        registry: Registry::new(rustc_errors::codes::DIAGNOSTICS),
        hash_untracked_state: None,
        using_internal_features: &rustc_driver::USING_INTERNAL_FEATURES,
        expanded_args: vec![],
    }
}

// ---------------------------------------------------------------------------------------------------------------
// T1: the type walk

struct Row {
    kind: &'static str,
    owner: String,
    name: String,
    idx: String,
    binding: &'static str,
    synthetic: bool,
    ty: String,
}

struct Layer {
    depth: usize,
    form: String,
    ctx: &'static str,
}

fn crat_helper(tcx: TyCtxt<'_>, did: rustc_span::def_id::DefId) -> Option<&'static str> {
    match tcx.item_name(did).as_str() {
        "SliceCursor" => Some("cursor"),
        "SliceCursorMut" => Some("cursor-mut"),
        _ => None,
    }
}

/// The head form of a pointer-like layer, the type one indirection below it, and whether that type is an element.
fn head<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<(String, Ty<'tcx>, bool)> {
    match ty.kind() {
        ty::RawPtr(inner, m) => Some((if m.is_mut() { "raw-mut" } else { "raw-const" }.into(), *inner, false)),
        ty::Ref(_, inner, m) => match inner.kind() {
            ty::Slice(elem) => Some((if m.is_mut() { "slice-mut" } else { "slice-ref" }.into(), *elem, true)),
            ty::Str => Some(("str-ref".into(), *inner, false)),
            _ => Some((if m.is_mut() { "mut-ref" } else { "ref" }.into(), *inner, false)),
        },
        ty::Adt(def, args) if def.is_box() => {
            let inner = args.type_at(0);
            match inner.kind() {
                ty::Slice(elem) => Some(("box-slice".into(), *elem, true)),
                _ => Some(("box".into(), inner, false)),
            }
        }
        ty::Adt(def, args) if tcx.is_diagnostic_item(sym::NonNull, def.did()) => {
            Some(("nonnull".into(), args.type_at(0), false))
        }
        ty::Adt(def, args) => crat_helper(tcx, def.did())
            .and_then(|form| args.types().next().map(|elem| (form.to_owned(), elem, true))),
        _ => None,
    }
}

fn walk<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, depth: usize, ctx: &'static str, out: &mut Vec<Layer>) {
    if depth > 16 || out.len() > 256 {
        return;
    }
    if let ty::Adt(def, args) = ty.kind()
        && tcx.is_diagnostic_item(sym::Option, def.did())
    {
        let inner = args.type_at(0);
        if let Some((form, below, elem)) = head(tcx, inner) {
            out.push(Layer { depth, form: format!("opt-{form}"), ctx });
            walk(tcx, below, depth + 1, if elem { "elem" } else { ctx_below(ctx) }, out);
        } else {
            walk(tcx, inner, depth, ctx, out);
        }
        return;
    }
    if let Some((form, below, elem)) = head(tcx, ty) {
        out.push(Layer { depth, form, ctx });
        walk(tcx, below, depth + 1, if elem { "elem" } else { ctx_below(ctx) }, out);
        return;
    }
    match ty.kind() {
        ty::Array(elem, _) | ty::Slice(elem) => walk(tcx, *elem, depth, "elem", out),
        ty::Tuple(tys) => {
            for t in tys.iter() {
                walk(tcx, t, depth, ctx, out);
            }
        }
        // a function pointer's signature: its pointer layers are counted, marked `fnptr`
        ty::FnPtr(sig_tys, _) => {
            for t in sig_tys.skip_binder().inputs_and_output.iter() {
                walk(tcx, t, depth, "fnptr", out);
            }
        }
        // another generic container's arguments are positions at this depth, marked `arg`; a struct's own fields are
        // counted at the struct, never through a declaration of the struct type
        ty::Adt(_, args) => {
            for t in args.types() {
                walk(tcx, t, depth, "arg", out);
            }
        }
        _ => {}
    }
}

/// Below a pointer layer an `elem` / `arg` / `fnptr` context persists only for `fnptr` (the signature stays a
/// signature); an element's pointee is an ordinary position.
fn ctx_below(ctx: &'static str) -> &'static str {
    if ctx == "fnptr" { "fnptr" } else { "-" }
}

struct Bindings<'a, 'tcx> {
    typeck: &'tcx ty::TypeckResults<'tcx>,
    owner: String,
    params: HashSet<hir::HirId>,
    typed_lets: HashSet<hir::HirId>,
    seen: BTreeMap<String, usize>,
    rows: &'a mut Vec<(Row, hir::HirId)>,
}

impl<'tcx> HirVisitor<'tcx> for Bindings<'_, 'tcx> {
    fn visit_local(&mut self, l: &'tcx hir::LetStmt<'tcx>) {
        if l.ty.is_some() {
            let mut ids = Vec::new();
            l.pat.each_binding(|_, id, _, _| ids.push(id));
            self.typed_lets.extend(ids);
        }
        intravisit::walk_local(self, l);
    }
    fn visit_pat(&mut self, p: &'tcx hir::Pat<'tcx>) {
        if let hir::PatKind::Binding(_, id, ident, _) = p.kind
            && !self.params.contains(&id)
        {
            let byref = self
                .typeck
                .pat_binding_modes()
                .get(id)
                .is_some_and(|mode| matches!(mode.0, ByRef::Yes(_)));
            let name = ident.to_string();
            let n = self.seen.entry(name.clone()).or_insert(0);
            let synthetic = name.starts_with("__crat_")
                || ident.span.from_expansion()
                || ident.span.desugaring_kind().is_some()
                || p.span.from_expansion();
            self.rows.push((
                Row {
                    kind: "local",
                    owner: self.owner.clone(),
                    name,
                    idx: n.to_string(),
                    binding: if byref {
                        "byref"
                    } else if self.typed_lets.contains(&id) {
                        "typed"
                    } else {
                        "untyped"
                    },
                    synthetic,
                    ty: String::new(),
                },
                id,
            ));
            *n += 1;
        }
        intravisit::walk_pat(self, p);
    }
}

fn items(tcx: TyCtxt<'_>) -> (Vec<LocalDefId>, Vec<LocalDefId>, Vec<LocalDefId>) {
    let (mut fns, mut adts, mut statics) = (vec![], vec![], vec![]);
    for maybe_owner in tcx.hir_crate(()).owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else { continue };
        let OwnerNode::Item(item) = owner.node() else { continue };
        let did = item.owner_id.def_id;
        match tcx.def_kind(did) {
            DefKind::Fn => fns.push(did),
            DefKind::Struct | DefKind::Union | DefKind::Enum => adts.push(did),
            DefKind::Static { .. } => statics.push(did),
            _ => {}
        }
    }
    (fns, adts, statics)
}

fn t1<'tcx>(tcx: TyCtxt<'tcx>) -> String {
    let (fns, adts, statics) = items(tcx);
    let mut out: Vec<(Row, Vec<Layer>)> = Vec::new();
    let push = |out: &mut Vec<(Row, Vec<Layer>)>, mut r: Row, ty: Ty<'tcx>| {
        let mut layers = Vec::new();
        walk(tcx, ty, 0, "-", &mut layers);
        if !layers.is_empty() {
            r.ty = ty.to_string();
            out.push((r, layers));
        }
    };
    for &did in &fns {
        let owner = tcx.def_path_str(did);
        let body = tcx.hir_body_owned_by(did);
        let typeck = tcx.typeck(did);
        let mut params = HashSet::new();
        for (i, p) in body.params.iter().enumerate() {
            let ty = typeck.node_type(p.pat.hir_id);
            let name = match p.pat.kind {
                hir::PatKind::Binding(_, id, ident, _) => {
                    params.insert(id);
                    ident.to_string()
                }
                _ => format!("_arg{i}"),
            };
            let r = Row {
                kind: "param",
                owner: owner.clone(),
                synthetic: name.starts_with("__crat_"),
                name,
                idx: i.to_string(),
                binding: "-",
                ty: String::new(),
            };
            push(&mut out, r, ty);
        }
        let sig = tcx.fn_sig(did).instantiate_identity().skip_binder();
        let r = Row {
            kind: "return",
            owner: owner.clone(),
            name: "_0".into(),
            idx: "-".into(),
            binding: "-",
            synthetic: false,
            ty: String::new(),
        };
        push(&mut out, r, sig.output());
        let mut locals = Vec::new();
        let mut v = Bindings {
            typeck,
            owner: owner.clone(),
            params,
            typed_lets: HashSet::new(),
            seen: BTreeMap::new(),
            rows: &mut locals,
        };
        // a `let`'s typed bindings are recorded in visit_local before its pattern is visited
        intravisit::walk_body(&mut v, body);
        for (r, id) in locals {
            push(&mut out, r, typeck.node_type(id));
        }
    }
    for &did in &adts {
        if crat_helper(tcx, did.to_def_id()).is_some() {
            continue;
        }
        let owner = tcx.def_path_str(did);
        for field in tcx.adt_def(did).all_fields() {
            let r = Row {
                kind: "field",
                owner: owner.clone(),
                name: field.name.to_string(),
                idx: "-".into(),
                binding: "-",
                synthetic: false,
                ty: String::new(),
            };
            push(&mut out, r, tcx.type_of(field.did).instantiate_identity());
        }
    }
    for &did in &statics {
        let path = tcx.def_path_str(did);
        let (owner, name) = path
            .rsplit_once("::")
            .map(|(a, b)| (a.to_owned(), b.to_owned()))
            .unwrap_or((String::new(), path.clone()));
        let r = Row { kind: "static", owner, name, idx: "-".into(), binding: "-", synthetic: false, ty: String::new() };
        push(&mut out, r, tcx.type_of(did).instantiate_identity());
    }
    let mut s = String::from("kind\towner\tname\tidx\tbinding\tsynthetic\tdepth\tlayer\tform\tctx\ttype\n");
    for (r, layers) in out {
        let mut at_depth: BTreeMap<usize, usize> = BTreeMap::new();
        for l in layers {
            let n = at_depth.entry(l.depth).or_insert(0);
            let _ = writeln!(
                s,
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                r.kind,
                r.owner,
                r.name,
                r.idx,
                r.binding,
                if r.synthetic { "yes" } else { "no" },
                l.depth,
                n,
                l.form,
                l.ctx,
                r.ty.replace(['\t', '\n'], " ")
            );
            *n += 1;
        }
    }
    s
}

// ---------------------------------------------------------------------------------------------------------------
// T2

const TWIN: &str = "__crat_safe_";

fn detwin(path: &str) -> (String, bool) {
    match path.rsplit_once("::") {
        Some((head, last)) if last.starts_with(TWIN) => (format!("{head}::{}", &last[TWIN.len()..]), true),
        None if path.starts_with(TWIN) => (path[TWIN.len()..].to_owned(), true),
        _ => (path.to_owned(), false),
    }
}

fn key_path(path: String, strip_src: bool) -> String {
    if strip_src { path.strip_prefix("src::").map(str::to_owned).unwrap_or(path) } else { path }
}

/// The registered rule (crown_usage_calibration.rs: `DefUse::for_place(..).is_some()` + `visit_projection`): a
/// non-use context is not an occurrence; a place whose projection holds a Deref is ONE occurrence.
struct Official<'a> {
    roots: &'a BTreeSet<Local>,
    n: u64,
}

impl<'tcx> MirVisitor<'tcx> for Official<'_> {
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        if matches!(context, PlaceContext::NonUse(_)) {
            return;
        }
        if self.roots.contains(&place.local) && place.projection.iter().any(|p| matches!(p, ProjectionElem::Deref)) {
            self.n += 1;
        }
        self.visit_projection(place.as_ref(), context, location);
    }
}

/// The full scope on pre-runtime MIR, cleanup blocks skipped.
struct Full<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    roots: u64,
    deref: u64,
}

impl<'tcx> MirVisitor<'tcx> for Full<'_, 'tcx> {
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        if matches!(context, PlaceContext::NonUse(_)) || self.body.basic_blocks[location.block].is_cleanup {
            return;
        }
        if place.projection.iter().any(|p| matches!(p, ProjectionElem::Deref)) {
            if matches!(self.body.local_decls[place.local].ty.kind(), ty::RawPtr(..)) {
                self.roots += 1;
            }
            let through_raw = place.projection.iter().enumerate().any(|(i, elem)| {
                matches!(elem, ProjectionElem::Deref)
                    && matches!(
                        PlaceRef { local: place.local, projection: &place.projection[..i] }.ty(self.body, self.tcx).ty.kind(),
                        ty::RawPtr(..)
                    )
            });
            if through_raw {
                self.deref += 1;
            }
        }
        self.visit_projection(place.as_ref(), context, location);
    }
}

/// Pre-runtime MIR for every fn, cloned before borrowck steals it (`mir_promoted`).
fn promoted_bodies(tcx: TyCtxt<'_>) -> HashMap<LocalDefId, Body<'_>> {
    let (fns, _, _) = items(tcx);
    fns.into_iter().map(|did| (did, tcx.mir_promoted(did).0.borrow().clone())).collect()
}

fn t2<'tcx>(
    tcx: TyCtxt<'tcx>,
    promoted: &HashMap<LocalDefId, Body<'tcx>>,
    universe: &BTreeSet<String>,
    strip_src: bool,
) -> (String, BTreeSet<String>) {
    let (fns, _, _) = items(tcx);
    let paths: BTreeSet<String> = fns.iter().map(|&d| tcx.def_path_str(d)).collect();
    let has_twin: BTreeSet<String> =
        paths.iter().filter_map(|p| detwin(p).1.then(|| detwin(p).0)).filter(|p| paths.contains(p)).collect();
    let mut seen = BTreeSet::new();
    let mut s = String::from("function\ttwin\tofficial\tofficial_raw\tfull_roots\tfull_deref\n");
    for &did in &fns {
        let path = tcx.def_path_str(did);
        let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
        // the registered rule: keyed as compiled
        let function = key_path(path.clone(), strip_src);
        let (twin_path, is_twin) = detwin(&path);
        let twin_function = key_path(twin_path, strip_src);
        let wrapper = has_twin.contains(&path);
        let (mut official, mut official_raw) = (BTreeSet::new(), BTreeSet::new());
        for info in &body.var_debug_info {
            if let VarDebugInfoContents::Place(place) = &info.value
                && let Some(local) = place.as_local()
            {
                let k = format!("{function}::{}", info.name);
                if universe.contains(&k) {
                    official.insert(local);
                    seen.insert(k);
                }
                let kt = format!("{twin_function}::{}", info.name);
                if !wrapper
                    && universe.contains(&kt)
                    && matches!(body.local_decls[local].ty.kind(), ty::RawPtr(..))
                {
                    official_raw.insert(local);
                }
            }
        }
        let mut o = Official { roots: &official, n: 0 };
        o.visit_body(&body);
        let mut oraw = Official { roots: &official_raw, n: 0 };
        oraw.visit_body(&body);
        let pb = &promoted[&did];
        let mut f = Full { tcx, body: pb, roots: 0, deref: 0 };
        f.visit_body(pb);
        let twin = if is_twin { "twin" } else if wrapper { "wrapper" } else { "-" };
        let _ = writeln!(s, "{path}\t{twin}\t{}\t{}\t{}\t{}", o.n, oraw.n, f.roots, f.deref);
    }
    (s, seen)
}

// ---------------------------------------------------------------------------------------------------------------

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let get = |flag: &str| args.iter().position(|a| a == flag).map(|i| args[i + 1].clone());
    let root = PathBuf::from(get("--root").expect("--root"));
    let out = PathBuf::from(get("--out").expect("--out"));
    let strip_src = args.iter().any(|a| a == "--strip-src");
    let sites_on = args.iter().any(|a| a == "--sites");
    let root_dir = root.parent().map(Path::to_path_buf).unwrap_or_default();
    let universe: BTreeSet<String> = get("--universe")
        .map(|p| fs::read_to_string(p).expect("universe").lines().filter(|l| !l.is_empty()).map(str::to_owned).collect())
        .unwrap_or_default();
    fs::create_dir_all(&out).expect("out dir");
    for f in ["positions.tsv", "uses.tsv", "universe-unmapped.txt", "status.txt", "sites.tsv", "sites-status.txt"] {
        let _ = fs::remove_file(out.join(f));
    }
    let config = make_config(Input::File(root.clone()));
    let result = rustc_driver::catch_fatal_errors(|| {
        rustc_interface::run_compiler(config, |compiler| {
            let krate = rustc_interface::parse(&compiler.sess);
            rustc_interface::create_and_enter_global_ctxt(compiler, krate, |tcx| {
                if tcx.dcx().has_errors().is_some() {
                    return Err("errors before analysis (parse / expansion)".to_owned());
                }
                // the pre-runtime bodies first: borrowck (inside `analysis`) steals `mir_promoted`
                let promoted = promoted_bodies(tcx);
                // r132: every fn / method / closure body, cloned at the same point (before borrowck steals it)
                let site_bodies = if sites_on { sites::clone_bodies(tcx) } else { Vec::new() };
                if tcx.dcx().has_errors().is_some() {
                    return Err("errors in type checking".to_owned());
                }
                let _ = tcx.analysis(());
                if tcx.dcx().has_errors().is_some() {
                    return Err("errors in analysis (borrow check)".to_owned());
                }
                let positions = t1(tcx);
                let (uses, seen) = t2(tcx, &promoted, &universe, strip_src);
                // r132: a panic in the site pass (e.g. `Dominators::dominates` on an unreachable block,
                // rustc_data_structures dominators/mod.rs:384) must not lose T1 / T2: catch it and report it in
                // sites-status.txt (`catch_fatal_errors` re-raises any panic that is not a fatal-error marker)
                let site_rows = sites_on.then(|| {
                    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                        sites::sites(tcx, &site_bodies, &root_dir)
                    }))
                    .map_err(|e| {
                        e.downcast_ref::<String>()
                            .cloned()
                            .or_else(|| e.downcast_ref::<&str>().map(|s| (*s).to_owned()))
                            .unwrap_or_else(|| "non-string panic payload".to_owned())
                    })
                });
                Ok((positions, uses, seen, site_rows))
            })
        })
    });
    match result {
        Ok(Ok((positions, uses, seen, site_rows))) => {
            match site_rows {
                Some(Ok(rows)) => {
                    let n = rows.lines().count().saturating_sub(1);
                    fs::write(out.join("sites.tsv"), rows).expect("write sites");
                    fs::write(out.join("sites-status.txt"), format!("ok\t{n}\n")).expect("write sites status");
                }
                Some(Err(msg)) => {
                    let msg = msg.replace(['\t', '\n', '\r'], " ");
                    fs::write(out.join("sites-status.txt"), format!("panic\t{msg}\n")).expect("write sites status");
                    eprintln!("rq2_site_counter: {}: the site pass panicked: {msg}", root.display());
                }
                None => {}
            }
            fs::write(out.join("positions.tsv"), positions).expect("write positions");
            fs::write(out.join("uses.tsv"), uses).expect("write uses");
            let missing: Vec<_> = universe.difference(&seen).cloned().collect();
            fs::write(out.join("universe-unmapped.txt"), missing.join("\n")).expect("write unmapped");
            fs::write(out.join("status.txt"), format!("ok\t{}\n", root.display())).expect("write status");
            println!("ok root={} universe={} unmapped={}", root.display(), universe.len(), missing.len());
        }
        Ok(Err(e)) => {
            let _ = fs::write(out.join("status.txt"), format!("error\t{}\t{e}\n", root.display()));
            eprintln!("rq2_pos_counter: {}: {e}", root.display());
            std::process::exit(2);
        }
        Err(_) => {
            let _ = fs::write(out.join("status.txt"), format!("rejected\t{}\n", root.display()));
            eprintln!("rq2_pos_counter: {}: rustc rejected the crate", root.display());
            std::process::exit(3);
        }
    }
}
