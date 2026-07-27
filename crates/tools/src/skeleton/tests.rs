use rustc_ast::{AngleBracketedArg, GenericArg, GenericArgs, visit::Visitor as _};
use utils::compilation::run_compiler_on_str;

use super::*;

#[path = "amendment4_sources.rs"]
mod amendment4_sources;
use amendment4_sources::*;

fn exact_a4_source(name: &str) -> &'static str {
    let delimited = match name {
        "A4-SRC-MOTIVATING" => A4_SRC_MOTIVATING,
        "A4-SRC-IMPORTS" => A4_SRC_IMPORTS,
        "A4-SRC-CANDIDATES" => A4_SRC_CANDIDATES,
        "A4-SRC-CANDIDATE-PRECEDENCE" => A4_SRC_CANDIDATE_PRECEDENCE,
        "A4-SRC-REEXPORTS" => A4_SRC_REEXPORTS,
        "A4-SRC-LOCAL-FALLBACK-ROUTES" => A4_SRC_LOCAL_FALLBACK_ROUTES,
        "A4-SRC-EXTERNAL-ROOT-ALIAS" => A4_SRC_EXTERNAL_ROOT_ALIAS,
        "A4-SRC-SOURCE-PATHS" => A4_SRC_SOURCE_PATHS,
        "A4-SRC-SOURCE-HINT-EDGES" => A4_SRC_SOURCE_HINT_EDGES,
        "A4-SRC-DIRECT-HINTS" => A4_SRC_DIRECT_HINTS,
        "A4-SRC-RECURSIVE-TYPES" => A4_SRC_RECURSIVE_TYPES,
        "A4-SRC-POINTERS" => A4_SRC_POINTERS,
        "A4-SRC-COMPOUND" => A4_SRC_COMPOUND,
        "A4-SRC-RAW-IDENTIFIERS" => A4_SRC_RAW_IDENTIFIERS,
        "A4-SRC-QUALIFIED-RAW-FALLBACK" => A4_SRC_QUALIFIED_RAW_FALLBACK,
        "A4-SRC-STANDARD-CONSTRUCTORS" => A4_SRC_STANDARD_CONSTRUCTORS,
        "A4-SRC-STANDARD-BARE-IMPORTS" => A4_SRC_STANDARD_BARE_IMPORTS,
        "A4-SRC-NO-STD-OPTION-SUCCESS" => A4_SRC_NO_STD_OPTION_SUCCESS,
        "A4-SRC-NAMED-OPTIONAL-BOX" => A4_SRC_NAMED_OPTIONAL_BOX,
        "A4-SRC-OPTION-COLLISION" => A4_SRC_OPTION_COLLISION,
        "A4-SRC-BOX-COLLISION" => A4_SRC_BOX_COLLISION,
        "A4-SRC-RENAMED-CONSTRUCTOR-COLLISION" => A4_SRC_RENAMED_CONSTRUCTOR_COLLISION,
        "A4-SRC-GLOB-CONSTRUCTOR-COLLISION" => A4_SRC_GLOB_CONSTRUCTOR_COLLISION,
        "A4-SRC-OPTBOX-PARTIAL-CONSTRUCTOR-COLLISION" => {
            A4_SRC_OPTBOX_PARTIAL_CONSTRUCTOR_COLLISION
        }
        "A4-SRC-LOCAL-BOX-COLLISION" => A4_SRC_LOCAL_BOX_COLLISION,
        "A4-SRC-EXTERN-PRELUDE-CONSTRUCTOR-COLLISION" => {
            A4_SRC_EXTERN_PRELUDE_CONSTRUCTOR_COLLISION
        }
        "A4-SRC-IRRELEVANT-COLLISIONS" => A4_SRC_IRRELEVANT_COLLISIONS,
        "A4-SRC-NO-IMPLICIT-PRELUDE-REJECTION" => A4_SRC_NO_IMPLICIT_PRELUDE_REJECTION,
        "A4-SRC-NO-STD-BOX-REJECTION" => A4_SRC_NO_STD_BOX_REJECTION,
        "A4-SRC-BOX-NO-IMPLICIT-PRELUDE-REJECTION" => A4_SRC_BOX_NO_IMPLICIT_PRELUDE_REJECTION,
        "A4-SRC-MODULE-NO-IMPLICIT-PRELUDE-REJECTION" => {
            A4_SRC_MODULE_NO_IMPLICIT_PRELUDE_REJECTION
        }
        "A4-SRC-ANCESTOR-NO-IMPLICIT-PRELUDE-REJECTION" => {
            A4_SRC_ANCESTOR_NO_IMPLICIT_PRELUDE_REJECTION
        }
        "A4-SRC-PRESERVED-PARENT" => A4_SRC_PRESERVED_PARENT,
        "A4-SRC-UNNAMEABLE" => A4_SRC_UNNAMEABLE,
        "A4-SRC-TREE" => A4_SRC_TREE,
        "A4-SRC-COMPREHENSIVE" => A4_SRC_COMPREHENSIVE,
        _ => panic!("missing Amendment 4 source constant {name}"),
    };
    delimited
        .strip_prefix('\n')
        .and_then(|source| source.strip_suffix('\n'))
        .unwrap_or_else(|| panic!("invalid literal boundaries for {name}"))
}

fn generate(source: &str) -> Vec<ItemRecord> {
    run_compiler_on_str(source, |tcx| make_skeletons(source, tcx).unwrap()).unwrap()
}

#[test]
fn every_exact_amendment_4_source_baseline_compiles_independently() {
    let names = [
        "A4-SRC-MOTIVATING",
        "A4-SRC-IMPORTS",
        "A4-SRC-CANDIDATES",
        "A4-SRC-CANDIDATE-PRECEDENCE",
        "A4-SRC-REEXPORTS",
        "A4-SRC-LOCAL-FALLBACK-ROUTES",
        "A4-SRC-EXTERNAL-ROOT-ALIAS",
        "A4-SRC-SOURCE-PATHS",
        "A4-SRC-SOURCE-HINT-EDGES",
        "A4-SRC-DIRECT-HINTS",
        "A4-SRC-RECURSIVE-TYPES",
        "A4-SRC-POINTERS",
        "A4-SRC-COMPOUND",
        "A4-SRC-RAW-IDENTIFIERS",
        "A4-SRC-QUALIFIED-RAW-FALLBACK",
        "A4-SRC-STANDARD-CONSTRUCTORS",
        "A4-SRC-STANDARD-BARE-IMPORTS",
        "A4-SRC-NO-STD-OPTION-SUCCESS",
        "A4-SRC-NAMED-OPTIONAL-BOX",
        "A4-SRC-OPTION-COLLISION",
        "A4-SRC-BOX-COLLISION",
        "A4-SRC-RENAMED-CONSTRUCTOR-COLLISION",
        "A4-SRC-GLOB-CONSTRUCTOR-COLLISION",
        "A4-SRC-OPTBOX-PARTIAL-CONSTRUCTOR-COLLISION",
        "A4-SRC-LOCAL-BOX-COLLISION",
        "A4-SRC-EXTERN-PRELUDE-CONSTRUCTOR-COLLISION",
        "A4-SRC-IRRELEVANT-COLLISIONS",
        "A4-SRC-NO-IMPLICIT-PRELUDE-REJECTION",
        "A4-SRC-NO-STD-BOX-REJECTION",
        "A4-SRC-BOX-NO-IMPLICIT-PRELUDE-REJECTION",
        "A4-SRC-MODULE-NO-IMPLICIT-PRELUDE-REJECTION",
        "A4-SRC-ANCESTOR-NO-IMPLICIT-PRELUDE-REJECTION",
        "A4-SRC-PRESERVED-PARENT",
        "A4-SRC-UNNAMEABLE",
        "A4-SRC-TREE",
        "A4-SRC-COMPREHENSIVE",
    ];
    for name in names {
        let source = exact_a4_source(name);
        assert!(
            !source.starts_with('\n'),
            "{name} has a leading fence newline"
        );
        assert!(
            !source.ends_with('\n'),
            "{name} has a trailing fence newline"
        );
        run_compiler_on_str(source, |_| ())
            .unwrap_or_else(|_| panic!("{name} did not baseline-compile"));
    }
    assert!(A4_SRC_MOTIVATING.starts_with('\n'));
    assert!(A4_SRC_MOTIVATING.ends_with('\n'));
    assert!(exact_a4_source("A4-SRC-MOTIVATING").starts_with("unsafe extern \"C\""));
    assert!(exact_a4_source("A4-SRC-MOTIVATING").ends_with('}'));
}

fn local_def(name: &str, tcx: TyCtxt<'_>) -> LocalDefId {
    tcx.hir_free_items()
        .find_map(|item_id| {
            let item = tcx.hir_item(item_id);
            item.kind
                .ident()
                .is_some_and(|ident| ident.name.as_str() == name)
                .then_some(item_id.owner_id.def_id)
        })
        .unwrap()
}

fn local_def_path(path: &str, tcx: TyCtxt<'_>) -> LocalDefId {
    tcx.hir_free_items()
        .find_map(|item_id| {
            (tcx.def_path_str(item_id.owner_id.def_id) == path).then_some(item_id.owner_id.def_id)
        })
        .unwrap_or_else(|| panic!("missing local definition {path}"))
}

fn tools_pointer_decisions(tcx: TyCtxt<'_>) -> InitialPointerDecisions {
    initial_pointer_decisions(
        &pointer_replacer::Config::default(),
        PointerDecisionOptions {
            assume_nonnegative_offsets: true,
        },
        tcx,
    )
}

fn local_binding_hir_id(function: LocalDefId, binding_name: &str, tcx: TyCtxt<'_>) -> HirId {
    struct BindingFinder<'a> {
        name: &'a str,
        hir_id: Option<HirId>,
    }

    impl<'tcx> rustc_hir::intravisit::Visitor<'tcx> for BindingFinder<'_> {
        fn visit_pat(&mut self, pattern: &'tcx rustc_hir::Pat<'tcx>) {
            if let rustc_hir::PatKind::Binding(_, hir_id, ident, _) = pattern.kind
                && ident.name.as_str() == self.name
            {
                assert!(
                    self.hir_id.replace(hir_id).is_none(),
                    "binding `{}` is not unique",
                    self.name
                );
            }
            rustc_hir::intravisit::walk_pat(self, pattern);
        }
    }

    let mut finder = BindingFinder {
        name: binding_name,
        hir_id: None,
    };
    finder.visit_body(tcx.hir_body_owned_by(function));
    finder
        .hir_id
        .unwrap_or_else(|| panic!("missing binding `{binding_name}`"))
}

fn local_binding_decision(
    function: LocalDefId,
    binding_name: &str,
    decisions: &InitialPointerDecisions,
    tcx: TyCtxt<'_>,
) -> PtrKind {
    decisions.bindings[&local_binding_hir_id(function, binding_name, tcx)]
}

fn local_binding_ty<'tcx>(
    function: LocalDefId,
    binding_name: &str,
    tcx: TyCtxt<'tcx>,
) -> ty::Ty<'tcx> {
    tcx.typeck(function)
        .node_type(local_binding_hir_id(function, binding_name, tcx))
}

fn local_binding_order(function: LocalDefId, tcx: TyCtxt<'_>) -> Vec<String> {
    struct BindingCollector {
        names: Vec<String>,
    }

    impl<'tcx> rustc_hir::intravisit::Visitor<'tcx> for BindingCollector {
        fn visit_local(&mut self, local: &'tcx rustc_hir::LetStmt<'tcx>) {
            if let rustc_hir::PatKind::Binding(_, _, ident, None) = local.pat.kind {
                self.names.push(ident.to_string());
            }
            rustc_hir::intravisit::walk_local(self, local);
        }
    }

    let mut collector = BindingCollector { names: vec![] };
    collector.visit_body(tcx.hir_body_owned_by(function));
    collector.names
}

fn resolve_one_segment_type(function: LocalDefId, spelling: &str, tcx: TyCtxt<'_>) -> DefId {
    let module: LocalDefId = tcx.parent_module_from_def_id(function).into();
    let matches = tcx
        .module_children_local(module)
        .iter()
        .filter(|child| {
            child.ident.to_string() == spelling && child.res.ns() == Some(Namespace::TypeNS)
        })
        .filter_map(|child| child.res.opt_def_id())
        .collect::<Vec<_>>();
    let [def_id] = matches[..] else {
        panic!(
            "expected one TypeNS binding `{spelling}` in `{}`, found {matches:?}",
            tcx.def_path_str(module)
        )
    };
    def_id
}

fn resolve_emitted_type_path(
    rendered: &str,
    function: LocalDefId,
    speller: &TypeSpeller<'_, '_>,
    tcx: TyCtxt<'_>,
) -> DefId {
    let parsed = utils::ast::try_parse_ty(rendered.to_owned()).unwrap();
    let TyKind::Path(None, path) = &parsed.kind else {
        panic!("emitted type is not a path: {rendered}")
    };
    assert!(
        path.segments.iter().all(|segment| segment.args.is_none()),
        "identity path unexpectedly has generic arguments: {rendered}"
    );
    let mut segments = path
        .segments
        .iter()
        .map(|segment| segment.ident.to_string())
        .collect::<Vec<_>>();
    if segments
        .first()
        .is_some_and(|segment| segment == "{{root}}")
    {
        segments.remove(0);
    }
    let containing_module: LocalDefId = tcx.parent_module_from_def_id(function).into();
    let (mut module, first_child, external) = if rendered.starts_with("::") {
        let root = &segments[0];
        let roots = speller
            .external_roots
            .iter()
            .filter(|(name, _)| name == root)
            .map(|(_, def_id)| *def_id)
            .collect::<Vec<_>>();
        let [root_def_id] = roots[..] else {
            panic!("expected one source-visible extern root `{root}`, found {roots:?}")
        };
        (root_def_id, 1, true)
    } else if segments.first().is_some_and(|segment| segment == "crate") {
        (CRATE_DEF_ID.to_def_id(), 1, false)
    } else {
        assert_eq!(
            segments.len(),
            1,
            "test resolver requires an absolute or one-segment path: {rendered}"
        );
        (containing_module.to_def_id(), 0, false)
    };

    for (index, segment) in segments.iter().enumerate().skip(first_child) {
        let children = if module.is_local() {
            tcx.module_children_local(module.expect_local())
        } else {
            tcx.module_children(module)
        };
        let matches = children
            .iter()
            .filter(|child| {
                child.ident.to_string() == *segment
                    && child.res.ns() == Some(Namespace::TypeNS)
                    && if external {
                        child.vis.is_public()
                    } else {
                        child.vis.is_accessible_from(containing_module, tcx)
                    }
            })
            .filter_map(|child| child.res.opt_def_id())
            .collect::<Vec<_>>();
        let [def_id] = matches[..] else {
            panic!("expected one accessible TypeNS segment `{segment}` in `{rendered}`")
        };
        if index + 1 == segments.len() {
            return def_id;
        }
        assert!(
            matches!(tcx.def_kind(def_id), DefKind::Mod | DefKind::ForeignMod),
            "non-module intermediate segment `{segment}` in `{rendered}`"
        );
        module = def_id;
    }
    panic!("path has no terminal TypeNS segment: {rendered}")
}

fn assert_constructor_failure_pointer_prerequisites(name: &str, tcx: TyCtxt<'_>) {
    let decisions = tools_pointer_decisions(tcx);
    let signature = |path: &str| &decisions.signatures.data[&local_def_path(path, tcx)];
    match name {
        "A4-SRC-OPTION-COLLISION" => {
            let signature = signature("wrapped::read");
            assert_eq!(
                signature.input_decs,
                [Some(PtrKind::OptRef(false)), Some(PtrKind::OptRef(false))]
            );
        }
        "A4-SRC-BOX-COLLISION" | "A4-SRC-GLOB-CONSTRUCTOR-COLLISION" => {
            let path = if name == "A4-SRC-BOX-COLLISION" {
                "wrapped::allocate"
            } else {
                "globbed::allocate"
            };
            let def_id = local_def_path(path, tcx);
            assert_eq!(signature(path).output_dec, Some(PtrKind::Box));
            assert_eq!(
                local_binding_decision(def_id, "p", &decisions, tcx),
                PtrKind::Box
            );
        }
        "A4-SRC-RENAMED-CONSTRUCTOR-COLLISION"
        | "A4-SRC-EXTERN-PRELUDE-CONSTRUCTOR-COLLISION"
        | "A4-SRC-NO-IMPLICIT-PRELUDE-REJECTION"
        | "A4-SRC-MODULE-NO-IMPLICIT-PRELUDE-REJECTION"
        | "A4-SRC-ANCESTOR-NO-IMPLICIT-PRELUDE-REJECTION" => {
            let path = match name {
                "A4-SRC-RENAMED-CONSTRUCTOR-COLLISION" => "renamed::read",
                "A4-SRC-ANCESTOR-NO-IMPLICIT-PRELUDE-REJECTION" => "outer::middle::inner::read",
                _ => "wrapped::read",
            };
            assert_eq!(signature(path).input_decs[0], Some(PtrKind::OptRef(false)));
        }
        "A4-SRC-OPTBOX-PARTIAL-CONSTRUCTOR-COLLISION" => {
            let owned_id = local_def_path("wrapped::owned_id", tcx);
            assert_eq!(
                decisions.signatures.data[&owned_id].input_decs[0],
                Some(PtrKind::OptBox)
            );
            assert_eq!(
                decisions.signatures.data[&owned_id].output_dec,
                Some(PtrKind::OptBox)
            );
            let foo = local_def_path("wrapped::foo", tcx);
            assert_eq!(
                decisions.signatures.data[&foo].output_dec,
                Some(PtrKind::OptBox)
            );
            assert_eq!(
                local_binding_decision(foo, "p", &decisions, tcx),
                PtrKind::Box
            );
            assert_eq!(
                local_binding_decision(foo, "q", &decisions, tcx),
                PtrKind::OptBox
            );
        }
        "A4-SRC-LOCAL-BOX-COLLISION" => {
            let def_id = local_def_path("consumer::local_only", tcx);
            for binding in ["first", "second"] {
                assert_eq!(
                    local_binding_decision(def_id, binding, &decisions, tcx),
                    PtrKind::Box
                );
            }
        }
        "A4-SRC-NO-STD-BOX-REJECTION" | "A4-SRC-BOX-NO-IMPLICIT-PRELUDE-REJECTION" => {
            let def_id = local_def_path("allocate", tcx);
            assert_eq!(
                decisions.signatures.data[&def_id].output_dec,
                Some(PtrKind::Box)
            );
            assert_eq!(
                local_binding_decision(def_id, "p", &decisions, tcx),
                PtrKind::Box
            );
        }
        _ => panic!("unhandled constructor failure source {name}"),
    }
}

fn resolve_accessible_local_type_path(
    path: &str,
    from_module: LocalDefId,
    tcx: TyCtxt<'_>,
) -> Option<DefId> {
    let mut module = CRATE_DEF_ID.to_def_id();
    let segments = path
        .strip_prefix("crate::")?
        .split("::")
        .collect::<Vec<_>>();
    for (index, segment) in segments.iter().enumerate() {
        let child = tcx
            .module_children_local(module.expect_local())
            .iter()
            .find(|child| {
                child.ident.to_string() == *segment
                    && child.vis.is_accessible_from(from_module, tcx)
                    && child.res.ns() == Some(Namespace::TypeNS)
            })?;
        let def_id = child.res.opt_def_id()?;
        if index + 1 == segments.len() {
            return Some(def_id);
        }
        if !matches!(child.res, Res::Def(DefKind::Mod, _)) {
            return None;
        }
        module = def_id;
    }
    None
}

fn resolved_bare_constructor(function: LocalDefId, symbol: Symbol, tcx: TyCtxt<'_>) -> DefId {
    let module: LocalDefId = tcx.parent_module_from_def_id(function).into();
    if let Some(def_id) = tcx
        .module_children_local(module)
        .iter()
        .find(|child| child.ident.name == symbol && child.res.ns() == Some(Namespace::TypeNS))
        .and_then(|child| child.res.opt_def_id())
    {
        return def_id;
    }
    let prelude = tcx
        .hir_free_items()
        .find_map(|item_id| {
            let item = tcx.hir_item(item_id);
            if !tcx
                .hir_attrs(item.hir_id())
                .iter()
                .any(|attribute| attribute.has_name(sym::prelude_import))
            {
                return None;
            }
            let hir::ItemKind::Use(path, hir::UseKind::Glob) = item.kind else {
                return None;
            };
            path.segments
                .last()
                .and_then(|segment| segment.res.opt_def_id())
        })
        .unwrap();
    tcx.module_children(prelude)
        .iter()
        .find(|child| child.ident.name == symbol && child.res.ns() == Some(Namespace::TypeNS))
        .and_then(|child| child.res.opt_def_id())
        .unwrap()
}

fn function<'a>(records: &'a [ItemRecord], path: &str) -> &'a FunctionRecord {
    records
        .iter()
        .find_map(|record| match record {
            ItemRecord::Function(function) if function.path == path => Some(function),
            _ => None,
        })
        .unwrap()
}

fn record<'a>(records: &'a [ItemRecord], path: &str) -> &'a ItemRecord {
    records.iter().find(|record| record.path() == path).unwrap()
}

fn value<'a>(records: &'a [ItemRecord], path: &str) -> &'a ValueRecord {
    match record(records, path) {
        ItemRecord::Value(value) => value,
        _ => panic!("{path} is not a value record"),
    }
}

fn type_record<'a>(records: &'a [ItemRecord], path: &str) -> &'a TypeRecord {
    match record(records, path) {
        ItemRecord::Type(value) => value,
        _ => panic!("{path} is not a type record"),
    }
}

fn generate_error(source: &str) -> GenerationError {
    run_compiler_on_str(source, |tcx| {
        let result = make_skeletons(source, tcx);
        let json = result
            .as_ref()
            .ok()
            .map(|records| skeletons_to_json(records).unwrap());
        assert!(
            json.is_none(),
            "failed generation returned records that could be serialized"
        );
        result.unwrap_err()
    })
    .unwrap()
}

fn compact(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn assert_unsupported_semantic_type<'tcx>(
    semantic_ty: ty::Ty<'tcx>,
    expected_shape: &str,
    tcx: TyCtxt<'tcx>,
) {
    let mut output = String::new();
    let mut nominal = |def_id| Ok(tcx.def_path_str(def_id));
    let error = utils::ir::format_mir_ty_with_policy(
        &mut output,
        semantic_ty,
        tcx,
        &mut nominal,
        utils::ir::MirTypeFormatPolicy::SourceValid,
    )
    .unwrap_err();
    assert_eq!(
        error,
        utils::ir::MirTypeFormatError::Unsupported(expected_shape.to_owned())
    );
}

fn assert_skeleton(source: &str, path: &str, expected: &str) {
    struct ParenNormalizer;

    impl MutVisitor for ParenNormalizer {
        fn visit_expr(&mut self, expression: &mut Expr) {
            while let ExprKind::Paren(inner) = &expression.kind {
                *expression = (**inner).clone();
            }
            mut_visit::walk_expr(self, expression);
        }
    }

    fn canonical_item(text: &str) -> String {
        let without_labels = text
            .lines()
            .filter(|line| !line.trim_start().starts_with("#[proctor("))
            .collect::<Vec<_>>()
            .join("\n");
        let mut krate = utils::ast::parse_crate(without_labels);
        ParenNormalizer.visit_crate(&mut krate);
        let [item] = &krate.items[..] else { panic!("expected exactly one item in {text}") };
        pprust::item_to_string(item)
    }

    run_compiler_on_str(source, |tcx| {
        let records = make_skeletons(source, tcx).unwrap();
        assert_eq!(
            canonical_item(&function(&records, path).annotated_skeleton),
            {
                let mut expected = utils::ast::parse_crate(expected.to_owned());
                PresentationBindingNormalizer.visit_crate(&mut expected);
                ParenNormalizer.visit_crate(&mut expected);
                pprust::item_to_string(&expected.items[0])
            }
        );
    })
    .unwrap();
}

fn simple_local_types(source: &str) -> Vec<(String, String, String)> {
    struct Finder {
        function_path: String,
        locals: Vec<(String, String, String)>,
    }

    impl<'ast> rustc_ast::visit::Visitor<'ast> for Finder {
        fn visit_local(&mut self, local: &'ast rustc_ast::Local) {
            if let PatKind::Ident(_, ident, None) = local.pat.kind
                && let Some(ty) = &local.ty
            {
                self.locals.push((
                    self.function_path.clone(),
                    ident.to_string(),
                    pprust::ty_to_string(ty),
                ));
            }
            rustc_ast::visit::walk_local(self, local);
        }
    }

    run_compiler_on_str(source, |tcx| {
        let records = make_skeletons(source, tcx).unwrap();
        let mut locals = vec![];
        for record in records {
            let ItemRecord::Function(function) = record else {
                continue;
            };
            let krate = utils::ast::parse_crate(function.annotated_skeleton);
            let mut finder = Finder {
                function_path: function.path,
                locals: vec![],
            };
            finder.visit_crate(&krate);
            locals.extend(finder.locals);
        }
        locals
    })
    .unwrap()
}

fn assert_paths(records: &[ItemRecord], expected: &[(&str, ItemKindName)]) {
    assert_eq!(
        records
            .iter()
            .map(|record| (record.path(), record.kind()))
            .collect::<Vec<_>>(),
        expected
    );
    assert_eq!(
        records.iter().map(ItemRecord::id).collect::<Vec<_>>(),
        (0..records.len() as u64).collect::<Vec<_>>()
    );
}

fn assert_function_record_json_key_order(record: &ItemRecord) {
    let function_json = skeletons_to_json(std::slice::from_ref(record)).unwrap();
    let mut previous = 0;
    for key in [
        "\"id\"",
        "\"path\"",
        "\"kind\"",
        "\"name\"",
        "\"annotated_source\"",
        "\"annotated_skeleton\"",
        "\"source_signature\"",
        "\"target_signature\"",
        "\"needs_transformation\"",
        "\"statements_requiring_transformation\"",
        "\"foreign_function_names\"",
        "\"signature_dependencies\"",
        "\"dependencies\"",
    ] {
        let position = function_json.find(key).unwrap();
        assert!(
            position >= previous,
            "JSON key {key} moved: {function_json}"
        );
        previous = position;
    }
}

#[test]
fn nested_same_module_inferred_local_uses_local_name() {
    let records = generate(exact_a4_source("A4-SRC-MOTIVATING"));
    let record = function(&records, "src::lib::cb_remove_gamma_rgb");
    assert!(record.target_signature.contains("rgb: cb_rgb"));
    assert!(record.annotated_skeleton.contains("let mut init: cb_rgb"));
    assert!(!record.annotated_skeleton.contains("src::lib::cb_rgb"));
}

#[test]
fn direct_renamed_and_glob_imports_name_inferred_locals() {
    let source = exact_a4_source("A4-SRC-IMPORTS");
    run_compiler_on_str(source, |tcx| {
        for (function_path, spelling, definition_path) in [
            ("direct::make", "Direct", "model::Direct"),
            ("renamed::make", "R", "model::Renamed"),
            ("globbed::make", "Globbed", "model::Globbed"),
        ] {
            let function = local_def_path(function_path, tcx);
            assert_eq!(
                resolve_one_segment_type(function, spelling, tcx),
                local_def_path(definition_path, tcx).to_def_id(),
                "{function_path} did not resolve `{spelling}` to {definition_path}"
            );
        }
    })
    .unwrap();
    let locals = simple_local_types(source);
    assert!(locals.contains(&("direct::make".into(), "value".into(), "Direct".into())));
    assert!(locals.contains(&("renamed::make".into(), "value".into(), "R".into())));
    assert!(locals.contains(&("globbed::make".into(), "value".into(), "Globbed".into())));
    for (_, _, ty) in &locals {
        assert!(!ty.starts_with("crate::model::"), "{ty}");
    }
}

#[test]
fn multiple_aliases_are_deterministic_and_source_hint_wins() {
    let candidates_source = exact_a4_source("A4-SRC-CANDIDATES");
    run_compiler_on_str(candidates_source, |tcx| {
        let target = local_def_path("left::Thing", tcx).to_def_id();
        for (function_path, spelling) in [
            ("aliases::inferred", "Alpha"),
            ("aliases::source_hint", "Zed"),
        ] {
            assert_eq!(
                resolve_one_segment_type(local_def_path(function_path, tcx), spelling, tcx),
                target
            );
        }
    })
    .unwrap();
    let first = generate(candidates_source);
    let second = generate(candidates_source);
    assert_eq!(first, second);
    assert_eq!(
        skeletons_to_json(&first).unwrap(),
        skeletons_to_json(&second).unwrap()
    );
    assert!(
        function(&first, "aliases::inferred")
            .annotated_skeleton
            .contains("let mut value: Alpha")
    );
    let source_hint = &function(&first, "aliases::source_hint").target_signature;
    assert!(source_hint.contains("pointer: &Zed"), "{source_hint}");

    let precedence_source = exact_a4_source("A4-SRC-CANDIDATE-PRECEDENCE");
    run_compiler_on_str(precedence_source, |tcx| {
        let own_target = local_def_path("own::Local", tcx).to_def_id();
        assert_eq!(
            resolve_one_segment_type(local_def_path("own::inferred", tcx), "Local", tcx),
            own_target
        );
        assert_eq!(
            resolve_one_segment_type(local_def_path("own::source", tcx), "Alias", tcx),
            own_target
        );
        let item_target = local_def_path("model::Item", tcx).to_def_id();
        let transparent_module: LocalDefId = tcx
            .parent_module_from_def_id(local_def_path("transparent::inferred", tcx))
            .into();
        assert_eq!(
            resolve_accessible_local_type_path("crate::model::Item", transparent_module, tcx),
            Some(item_target)
        );
        assert_ne!(
            resolve_one_segment_type(
                local_def_path("transparent::inferred", tcx),
                "Transparent",
                tcx
            ),
            item_target,
            "transparent alias must remain a distinct resolver definition"
        );
        assert_eq!(
            resolve_one_segment_type(local_def_path("namespace::inferred", tcx), "Name", tcx),
            item_target,
            "the value-namespace `Name` must not hide the type binding"
        );
    })
    .unwrap();
    let records = generate(precedence_source);
    let locals = simple_local_types(precedence_source);
    assert!(locals.contains(&("own::inferred".into(), "value".into(), "Local".into())));
    assert!(
        function(&records, "own::source")
            .target_signature
            .contains("pointer: &Alias")
    );
    assert!(locals.contains(&(
        "transparent::inferred".into(),
        "value".into(),
        "crate::model::Item".into()
    )));
    assert!(locals.contains(&("namespace::inferred".into(), "value".into(), "Name".into())));
}

#[test]
fn wrong_same_spelling_binding_requires_absolute_local_fallback() {
    let source = exact_a4_source("A4-SRC-CANDIDATES");
    run_compiler_on_str(source, |tcx| {
        let inferred = local_def_path("collision::inferred", tcx);
        let module: LocalDefId = tcx.parent_module_from_def_id(inferred).into();
        let left = local_def_path("left::Thing", tcx).to_def_id();
        let right = local_def_path("right::Thing", tcx).to_def_id();
        assert_eq!(resolve_one_segment_type(inferred, "Thing", tcx), right);
        assert_eq!(
            resolve_accessible_local_type_path("crate::left::Thing", module, tcx),
            Some(left)
        );
        assert_eq!(
            local_binding_ty(inferred, "value", tcx)
                .ty_adt_def()
                .unwrap()
                .did(),
            left
        );
    })
    .unwrap();
    let records = generate(source);
    let inferred = function(&records, "collision::inferred");
    assert!(
        inferred
            .annotated_skeleton
            .contains("let mut value: crate::left::Thing")
    );
    let inferred_ty = simple_local_types(source)
        .into_iter()
        .find(|(path, name, _)| path == "collision::inferred" && name == "value")
        .unwrap()
        .2;
    assert_eq!(inferred_ty, "crate::left::Thing");
    assert_ne!(inferred_ty, "Thing");
    assert_ne!(inferred_ty, "right::Thing");
    assert_ne!(inferred_ty, "left::Thing");
    assert!(
        function(&records, "collision::use_right")
            .target_signature
            .contains("value: Thing")
    );

    let local_prelude_shadow = r#"
        pub mod wrapped {
            pub struct Option;
            pub unsafe fn inferred() -> bool {
                let value = core::option::Option::<i32>::None;
                value.is_none()
            }
        }
    "#;
    let locals = simple_local_types(local_prelude_shadow);
    assert!(locals.contains(&(
        "wrapped::inferred".into(),
        "value".into(),
        "::core::option::Option<i32>".into()
    )));

    let extern_prelude_shadow = r#"
        extern crate core as Option;
        pub mod wrapped {
            pub unsafe fn inferred() -> bool {
                let value = core::option::Option::<i32>::None;
                value.is_none()
            }
        }
    "#;
    let locals = simple_local_types(extern_prelude_shadow);
    let (_, _, ty) = locals
        .iter()
        .find(|(path, name, _)| path == "wrapped::inferred" && name == "value")
        .unwrap();
    assert_ne!(ty, "Option<i32>");
    assert!(ty.starts_with("::"), "{ty}");
}

#[test]
fn local_visible_fallback_uses_public_reexport_not_private_definition_path() {
    let source = exact_a4_source("A4-SRC-REEXPORTS");
    run_compiler_on_str(source, |tcx| {
        let consumer: LocalDefId = tcx
            .parent_module_from_def_id(local_def_path("consumer::local", tcx))
            .into();
        let target = local_def_path("api::hidden::Public", tcx).to_def_id();
        assert_eq!(
            resolve_accessible_local_type_path("crate::api::Exposed", consumer, tcx),
            Some(target)
        );
        assert_eq!(
            resolve_accessible_local_type_path("crate::api::hidden::Public", consumer, tcx),
            None
        );
    })
    .unwrap();
    let records = generate(source);
    let local = &function(&records, "consumer::local").annotated_skeleton;
    assert!(local.contains("let mut value: crate::api::Exposed"));
    assert!(!local.contains("hidden::Public"));

    let source = exact_a4_source("A4-SRC-LOCAL-FALLBACK-ROUTES");
    run_compiler_on_str(source, |tcx| {
        let consumer: LocalDefId = tcx
            .parent_module_from_def_id(local_def_path("consumer::restricted", tcx))
            .into();
        let routes = [
            (
                "restricted_api::hidden::Restricted",
                "crate::restricted_api::Exposed",
                None,
            ),
            (
                "short::hidden::Short",
                "crate::short::S",
                Some("crate::longer::route::S"),
            ),
            (
                "alpha::hidden::Tie",
                "crate::alpha::T",
                Some("crate::beta::T"),
            ),
        ];
        for (target, winner, loser) in routes {
            let target = local_def_path(target, tcx).to_def_id();
            assert_eq!(
                resolve_accessible_local_type_path(winner, consumer, tcx),
                Some(target)
            );
            if let Some(loser) = loser {
                assert_eq!(
                    resolve_accessible_local_type_path(loser, consumer, tcx),
                    Some(target)
                );
                assert!(winner.split("::").count() < loser.split("::").count() || winner < loser);
            }
        }
    })
    .unwrap();
    let locals = simple_local_types(source);
    assert!(locals.contains(&(
        "consumer::restricted".into(),
        "value".into(),
        "crate::restricted_api::Exposed".into()
    )));
    assert!(locals.contains(&(
        "consumer::shortest".into(),
        "value".into(),
        "crate::short::S".into()
    )));
    assert!(locals.contains(&(
        "consumer::tie".into(),
        "value".into(),
        "crate::alpha::T".into()
    )));
}

#[test]
fn external_visible_fallback_is_absolute_and_uses_public_reexport() {
    let reexports = exact_a4_source("A4-SRC-REEXPORTS");
    run_compiler_on_str(reexports, |tcx| {
        let function_def_id = local_def_path("consumer::external", tcx);
        let target = local_binding_ty(function_def_id, "value", tcx)
            .ty_adt_def()
            .unwrap()
            .did();
        let mut surface = utils::ast::parse_crate(reexports.to_owned());
        let mut mapper = utils::ir::AstToHirMapper::new(tcx);
        mapper.map_crate_to_mod(&mut surface, tcx.hir_root_module(), false);
        let speller = TypeSpeller::new(function_def_id, &mapper.ast_to_hir, tcx);
        let roots = speller
            .external_roots
            .iter()
            .filter(|(_, root)| root.krate == target.krate)
            .map(|(name, _)| name.as_str())
            .collect::<Vec<_>>();
        assert_eq!(roots, ["std"]);
        let paths = speller.external_visible_paths(target);
        assert_eq!(
            paths.first().map(String::as_str),
            Some("::std::hash::DefaultHasher")
        );
        assert!(paths.iter().all(|path| !path.contains("hash::random")));
        assert_eq!(
            resolve_emitted_type_path("::std::hash::DefaultHasher", function_def_id, &speller, tcx),
            target
        );
    })
    .unwrap();
    let records = generate(reexports);
    let external = &function(&records, "consumer::external").annotated_skeleton;
    assert!(compact(external).contains(&compact(
        "let mut value: ::std::hash::DefaultHasher = ::std::hash::DefaultHasher::new();"
    )));
    assert!(!external.contains("hash::random"));

    let alias_source = exact_a4_source("A4-SRC-EXTERNAL-ROOT-ALIAS");
    run_compiler_on_str(alias_source, |tcx| {
        let function_def_id = local_def_path("consumer::external_alias", tcx);
        let target = local_binding_ty(function_def_id, "value", tcx)
            .ty_adt_def()
            .unwrap()
            .did();
        let mut surface = utils::ast::parse_crate(alias_source.to_owned());
        let mut mapper = utils::ir::AstToHirMapper::new(tcx);
        mapper.map_crate_to_mod(&mut surface, tcx.hir_root_module(), false);
        let speller = TypeSpeller::new(function_def_id, &mapper.ast_to_hir, tcx);
        let roots = speller
            .external_roots
            .iter()
            .filter(|(_, root)| root.krate == target.krate)
            .map(|(name, _)| name.as_str())
            .collect::<Vec<_>>();
        assert_eq!(roots, ["alt_std", "rust_std"]);
        let paths = speller.external_visible_paths(target);
        assert!(paths.contains(&"::alt_std::hash::DefaultHasher".to_owned()));
        assert!(paths.contains(&"::rust_std::hash::DefaultHasher".to_owned()));
        assert_eq!(
            paths.first().map(String::as_str),
            Some("::alt_std::hash::DefaultHasher")
        );
        assert_eq!(
            resolve_emitted_type_path(
                "::alt_std::hash::DefaultHasher",
                function_def_id,
                &speller,
                tcx
            ),
            target
        );
    })
    .unwrap();
    let locals = simple_local_types(alias_source);
    assert!(locals.contains(&(
        "consumer::external_alias".into(),
        "value".into(),
        "::alt_std::hash::DefaultHasher".into()
    )));
    let alias_records = generate(alias_source);
    assert!(compact(
        &function(&alias_records, "consumer::external_alias").annotated_skeleton
    )
    .contains(&compact(
        "let mut value: ::alt_std::hash::DefaultHasher = rust_std::hash::DefaultHasher::new();"
    )));

    let renamed_extern = r#"
        #![no_std]
        pub unsafe fn external_alias() -> usize {
            let value = aliased_std::hash::DefaultHasher::new();
            core::mem::size_of_val(&value)
        }
    "#;
    let mut config =
        utils::compilation::make_config(utils::compilation::str_to_input(renamed_extern));
    let mut externs = config
        .opts
        .externs
        .iter()
        .map(|(name, entry)| (name.clone(), entry.clone()))
        .collect::<std::collections::BTreeMap<_, _>>();
    let target_libdir = std::process::Command::new("rustc")
        .args(["--print", "target-libdir"])
        .output()
        .unwrap();
    let target_libdir =
        std::path::PathBuf::from(String::from_utf8(target_libdir.stdout).unwrap().trim());
    let std_rlib = std::fs::read_dir(target_libdir)
        .unwrap()
        .map(Result::unwrap)
        .map(|entry| entry.path())
        .find(|path| {
            path.file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| name.starts_with("libstd-") && name.ends_with(".rlib"))
        })
        .unwrap();
    let std_entry = rustc_session::config::ExternEntry {
        location: rustc_session::config::ExternLocation::ExactPaths(
            [rustc_session::utils::CanonicalizedPath::new(std_rlib)]
                .into_iter()
                .collect(),
        ),
        is_private_dep: false,
        add_prelude: true,
        nounused_dep: false,
        force: false,
    };
    externs.insert("aliased_std".to_owned(), std_entry);
    config.opts.externs = rustc_session::config::Externs::new(externs);
    let uses_alias = utils::compilation::run_compiler(config, |tcx| {
        let records = make_skeletons(renamed_extern, tcx).unwrap();
        function(&records, "external_alias")
            .annotated_skeleton
            .contains("let mut value: ::aliased_std::hash::DefaultHasher")
    })
    .unwrap();
    assert!(uses_alias);
}

#[test]
fn source_alias_and_relative_pointee_paths_are_reused() {
    let source = exact_a4_source("A4-SRC-SOURCE-PATHS");
    run_compiler_on_str(source, |tcx| {
        let decisions = tools_pointer_decisions(tcx);
        let point_alias = local_def_path("model::PointAlias", tcx).to_def_id();
        let alias = local_def_path("consumer::alias", tcx);
        let local_alias = local_def_path("consumer::local_alias", tcx);
        let alias_id = local_def_path("consumer::alias_id", tcx);
        for (function, spelling) in [
            (alias, "P"),
            (alias_id, "P"),
            (alias_id, "ReturnP"),
            (local_alias, "P"),
            (local_alias, "LocalP"),
        ] {
            assert_eq!(
                resolve_one_segment_type(function, spelling, tcx),
                point_alias,
                "`{spelling}` did not retain PointAlias resolver identity"
            );
        }
        assert_eq!(
            ["P", "ReturnP", "LocalP"]
                .into_iter()
                .collect::<std::collections::BTreeSet<_>>()
                .len(),
            3,
            "the three source-hint spellings must remain intentionally distinct"
        );
        let local_alias_signature = &decisions.signatures.data[&local_alias];
        assert_eq!(
            local_alias_signature.input_decs[0],
            Some(PtrKind::Ref(false))
        );
        assert_eq!(
            local_binding_decision(local_alias, "local", &decisions, tcx),
            PtrKind::Ref(false)
        );
        let alias_id_signature = &decisions.signatures.data[&alias_id];
        assert_eq!(alias_id_signature.input_decs[0], Some(PtrKind::Ref(false)));
        assert_eq!(alias_id_signature.output_dec, Some(PtrKind::Ref(false)));
        assert_eq!(
            alias_id_signature.input_lifetimes[0],
            alias_id_signature.output_lifetime
        );
        assert_eq!(
            alias_id_signature.input_lifetimes[0],
            Some(Symbol::intern("a"))
        );
    })
    .unwrap();
    let records = generate(source);
    let alias = &function(&records, "consumer::alias").target_signature;
    assert!(alias.contains("pointer: &P"), "{alias}");
    let local_alias = function(&records, "consumer::local_alias");
    assert!(local_alias.target_signature.contains("pointer: &P"));
    assert!(local_alias.statements_requiring_transformation.contains(&0));
    assert!(
        local_alias
            .annotated_skeleton
            .contains("let mut local: &LocalP")
    );
    let alias_id = function(&records, "consumer::alias_id");
    assert!(alias_id.target_signature.contains("pointer: &'a P"));
    assert!(alias_id.target_signature.contains("-> &'a ReturnP"));
    assert!(
        function(&records, "consumer::relative")
            .target_signature
            .contains("&super::model::Point")
    );

    let source = exact_a4_source("A4-SRC-SOURCE-HINT-EDGES");
    run_compiler_on_str(source, |tcx| {
        let decisions = tools_pointer_decisions(tcx);
        for (path, expected) in [
            ("consumer::qualified_alias", PtrKind::Ref(false)),
            ("consumer::optional_alias", PtrKind::OptRef(false)),
            ("consumer::hidden_pointer_alias", PtrKind::Ref(false)),
        ] {
            let def_id = local_def_path(path, tcx);
            assert_eq!(
                decisions.signatures.data[&def_id].input_decs[0],
                Some(expected)
            );
        }
    })
    .unwrap();
    let records = generate(source);
    assert!(
        function(&records, "consumer::qualified_alias")
            .target_signature
            .contains("pointer: &P")
    );
    assert!(
        function(&records, "consumer::optional_alias")
            .target_signature
            .contains("pointer: Option<&P>")
    );
    assert!(
        function(&records, "consumer::explicit_nominal")
            .annotated_skeleton
            .contains("let mut value: crate::model::PointAlias")
    );
    assert!(
        function(&records, "consumer::hidden_pointer_alias")
            .target_signature
            .contains("pointer: &crate::model::Point")
    );

    let qualified_generic = r#"
        pub struct Wrap<T>(pub T);
        pub mod consumer {
            use crate::Wrap as W;
            pub unsafe fn read(pointer: *const crate::Wrap<i32>) -> i32 {
                (*pointer).0
            }
        }
    "#;
    assert!(
        function(&generate(qualified_generic), "consumer::read")
            .target_signature
            .contains("pointer: &W<i32>")
    );
}

#[test]
fn same_module_parameter_return_local_and_lifetime_types_are_short() {
    let source = exact_a4_source("A4-SRC-POINTERS");
    run_compiler_on_str(source, |tcx| {
        let decisions = tools_pointer_decisions(tcx);
        let update = local_def_path("update_and_return", tcx);
        let signature = &decisions.signatures.data[&update];
        assert_eq!(signature.input_decs[0], Some(PtrKind::Ref(true)));
        assert_eq!(signature.output_dec, Some(PtrKind::Ref(true)));
        assert_eq!(signature.input_lifetimes[0], Some(Symbol::intern("a")));
        assert_eq!(signature.output_lifetime, Some(Symbol::intern("a")));
        assert_eq!(
            signature.input_lifetimes[0], signature.output_lifetime,
            "the returned mutable borrow must share the exact lifetime Symbol"
        );
        let local_pointer = local_def_path("local_pointer", tcx);
        assert_eq!(
            local_binding_decision(local_pointer, "pointer", &decisions, tcx),
            PtrKind::Ref(true)
        );
        let node = local_def_path("Node", tcx).to_def_id();
        assert_eq!(
            resolve_one_segment_type(update, "Node", tcx),
            node,
            "same-module target component must resolve to Node"
        );
        assert_eq!(
            resolve_one_segment_type(local_pointer, "Node", tcx),
            node,
            "both inferred local components must resolve to Node"
        );
    })
    .unwrap();
    let records = generate(source);
    let update = function(&records, "update_and_return");
    assert_eq!(
        update.source_signature,
        "pub unsafe fn update_and_return(mut pointer: *mut Node) -> *mut Node"
    );
    assert_eq!(
        compact(&update.target_signature),
        "pub unsafe fn update_and_return<'a>(mut pointer: &'a mut Node) -> &'a mut Node"
    );
    assert!(!update.target_signature.contains("crate::Node"));
    assert!(!update.annotated_skeleton.contains("crate::Node"));
    let local_pointer = function(&records, "local_pointer");
    assert!(
        local_pointer
            .annotated_source
            .contains("let mut node = Node")
    );
    assert!(
        local_pointer
            .annotated_source
            .contains("let mut pointer = &mut node as *mut Node")
    );
    assert!(
        local_pointer
            .annotated_skeleton
            .contains("let mut pointer: &mut Node")
    );
    assert!(!local_pointer.annotated_skeleton.contains("crate::Node"));
    assert!(!local_pointer.target_signature.contains("crate::Node"));
    let locals = simple_local_types(source);
    assert!(locals.contains(&("local_pointer".into(), "node".into(), "Node".into())));
    assert!(locals.contains(&("local_pointer".into(), "pointer".into(), "&mut Node".into())));
}

#[test]
fn raw_identifiers_remain_parseable_in_inferred_and_pointer_types() {
    let source = exact_a4_source("A4-SRC-RAW-IDENTIFIERS");
    run_compiler_on_str(source, |tcx| {
        let read = local_def_path("r#type::read", tcx);
        let inferred = local_def_path("r#type::inferred", tcx);
        let target = local_def_path("r#type::r#match", tcx).to_def_id();
        assert_eq!(resolve_one_segment_type(read, "r#match", tcx), target);
        assert_eq!(resolve_one_segment_type(inferred, "r#match", tcx), target);
        for record in make_skeletons(source, tcx).unwrap() {
            if let ItemRecord::Function(function) = record {
                utils::ast::parse_crate(function.annotated_skeleton);
            }
        }
    })
    .unwrap();
    let records = generate(source);
    assert!(
        function(&records, "r#type::read")
            .target_signature
            .contains("&r#match")
    );
    assert!(
        function(&records, "r#type::inferred")
            .annotated_skeleton
            .contains("let mut value: r#match")
    );
    let qualified = exact_a4_source("A4-SRC-QUALIFIED-RAW-FALLBACK");
    run_compiler_on_str(qualified, |tcx| {
        let function_def_id = local_def_path("consumer::inferred", tcx);
        let target = local_def_path("r#type::r#match", tcx).to_def_id();
        let mut surface = utils::ast::parse_crate(qualified.to_owned());
        let mut mapper = utils::ir::AstToHirMapper::new(tcx);
        mapper.map_crate_to_mod(&mut surface, tcx.hir_root_module(), false);
        let speller = TypeSpeller::new(function_def_id, &mapper.ast_to_hir, tcx);
        assert_eq!(
            resolve_emitted_type_path("crate::r#type::r#match", function_def_id, &speller, tcx),
            target
        );
        assert_eq!(
            local_binding_ty(function_def_id, "value", tcx)
                .ty_adt_def()
                .unwrap()
                .did(),
            target
        );
        for record in make_skeletons(qualified, tcx).unwrap() {
            if let ItemRecord::Function(function) = record {
                utils::ast::parse_crate(function.annotated_skeleton);
            }
        }
    })
    .unwrap();
    let records = generate(qualified);
    assert!(
        function(&records, "consumer::inferred")
            .annotated_skeleton
            .contains("let mut value: crate::r#type::r#match")
    );
}

#[test]
fn standard_constructors_require_exact_bare_prelude_resolution() {
    let table = [
        (PtrKind::Ref(false), false, false),
        (PtrKind::Ref(true), false, false),
        (PtrKind::Raw(false), false, false),
        (PtrKind::Raw(true), false, false),
        (PtrKind::Slice(false), false, false),
        (PtrKind::Slice(true), false, false),
        (PtrKind::SliceCursor(false), false, false),
        (PtrKind::SliceCursor(true), false, false),
        (PtrKind::OptRef(false), true, false),
        (PtrKind::OptRef(true), true, false),
        (PtrKind::Box, false, true),
        (PtrKind::BoxedSlice, false, true),
        (PtrKind::OptBox, true, true),
        (PtrKind::OptBoxedSlice, true, true),
    ];
    for (kind, option, boxed) in table {
        assert_eq!(
            constructor_requirements(kind),
            ConstructorRequirements { option, boxed }
        );
    }
    let source = exact_a4_source("A4-SRC-STANDARD-CONSTRUCTORS");
    run_compiler_on_str(source, |tcx| {
        let decisions = tools_pointer_decisions(tcx);
        let read = local_def_path("wrapped::read", tcx);
        assert_eq!(
            decisions.signatures.data[&read].input_decs[0],
            Some(PtrKind::OptRef(false))
        );
        let owned_id = local_def_path("wrapped::owned_id", tcx);
        assert_eq!(
            decisions.signatures.data[&owned_id].input_decs[0],
            Some(PtrKind::OptBox)
        );
        assert_eq!(
            decisions.signatures.data[&owned_id].output_dec,
            Some(PtrKind::OptBox)
        );
        let foo = local_def_path("wrapped::foo", tcx);
        assert_eq!(
            decisions.signatures.data[&foo].output_dec,
            Some(PtrKind::OptBox)
        );
        assert_eq!(
            local_binding_decision(foo, "p", &decisions, tcx),
            PtrKind::Box
        );
        assert_eq!(
            local_binding_decision(foo, "q", &decisions, tcx),
            PtrKind::OptBox
        );
        let allocate = local_def_path("wrapped::allocate", tcx);
        assert_eq!(
            decisions.signatures.data[&allocate].output_dec,
            Some(PtrKind::Box)
        );
        assert_eq!(
            local_binding_decision(allocate, "p", &decisions, tcx),
            PtrKind::Box
        );
        assert!(tcx.is_lang_item(
            resolved_bare_constructor(read, sym::Option, tcx),
            hir::LangItem::Option
        ));
        assert!(tcx.is_lang_item(
            resolved_bare_constructor(allocate, Symbol::intern("Box"), tcx),
            hir::LangItem::OwnedBox
        ));
    })
    .unwrap();
    let records = generate(source);
    assert!(
        function(&records, "wrapped::read")
            .target_signature
            .contains("Option<&i32>")
    );
    assert!(
        function(&records, "wrapped::allocate")
            .target_signature
            .contains("-> Box<i32>")
    );
    assert_eq!(
        function(&records, "wrapped::owned_id").target_signature,
        "pub unsafe fn owned_id(mut p: Option<Box<i32>>) -> Option<Box<i32>>"
    );
    assert_eq!(
        function(&records, "wrapped::foo").target_signature,
        "pub unsafe fn foo() -> Option<Box<i32>>"
    );
    assert!(
        function(&records, "wrapped::foo")
            .annotated_skeleton
            .contains("let mut p: Box<i32>")
    );
    assert!(
        function(&records, "wrapped::foo")
            .annotated_skeleton
            .contains("let mut q: Option<Box<i32>>")
    );

    let source = exact_a4_source("A4-SRC-STANDARD-BARE-IMPORTS");
    run_compiler_on_str(source, |tcx| {
        let decisions = tools_pointer_decisions(tcx);
        let read = local_def_path("imported::read", tcx);
        assert_eq!(
            decisions.signatures.data[&read].input_decs[0],
            Some(PtrKind::OptRef(false))
        );
        let allocate = local_def_path("imported::allocate", tcx);
        assert_eq!(
            decisions.signatures.data[&allocate].output_dec,
            Some(PtrKind::Box)
        );
        assert_eq!(
            local_binding_decision(allocate, "p", &decisions, tcx),
            PtrKind::Box
        );
        assert!(tcx.is_lang_item(
            resolved_bare_constructor(read, sym::Option, tcx),
            hir::LangItem::Option
        ));
        assert!(tcx.is_lang_item(
            resolved_bare_constructor(allocate, Symbol::intern("Box"), tcx),
            hir::LangItem::OwnedBox
        ));
    })
    .unwrap();
    let records = generate(source);
    assert!(
        function(&records, "imported::read")
            .target_signature
            .contains("p: Option<&i32>")
    );
    assert!(
        function(&records, "imported::allocate")
            .target_signature
            .contains("-> Box<i32>")
    );
    assert!(
        function(&records, "imported::allocate")
            .annotated_skeleton
            .contains("let mut p: Box<i32>")
    );

    let source = exact_a4_source("A4-SRC-NO-STD-OPTION-SUCCESS");
    run_compiler_on_str(source, |tcx| {
        let decisions = tools_pointer_decisions(tcx);
        let read = local_def_path("read", tcx);
        assert_eq!(
            decisions.signatures.data[&read].input_decs[0],
            Some(PtrKind::OptRef(false))
        );
        assert!(tcx.is_lang_item(
            resolved_bare_constructor(read, sym::Option, tcx),
            hir::LangItem::Option
        ));
    })
    .unwrap();
    let records = generate(source);
    assert_eq!(
        function(&records, "read").target_signature,
        "pub unsafe fn read(mut p: Option<&i32>) -> i32"
    );

    let source = exact_a4_source("A4-SRC-NAMED-OPTIONAL-BOX");
    run_compiler_on_str(source, |tcx| {
        let decisions = tools_pointer_decisions(tcx);
        let owned_id = local_def_path("consumer::owned_id", tcx);
        assert_eq!(
            decisions.signatures.data[&owned_id].input_decs[0],
            Some(PtrKind::OptBox)
        );
        assert_eq!(
            decisions.signatures.data[&owned_id].output_dec,
            Some(PtrKind::OptBox)
        );
        let foo = local_def_path("consumer::foo", tcx);
        assert_eq!(
            decisions.signatures.data[&foo].output_dec,
            Some(PtrKind::OptBox)
        );
        assert_eq!(
            local_binding_decision(foo, "p", &decisions, tcx),
            PtrKind::Box
        );
        assert_eq!(
            local_binding_decision(foo, "q", &decisions, tcx),
            PtrKind::OptBox
        );
        assert!(tcx.is_lang_item(
            resolved_bare_constructor(owned_id, sym::Option, tcx),
            hir::LangItem::Option
        ));
        assert!(tcx.is_lang_item(
            resolved_bare_constructor(owned_id, Symbol::intern("Box"), tcx),
            hir::LangItem::OwnedBox
        ));
    })
    .unwrap();
    let records = generate(source);
    assert_eq!(
        function(&records, "consumer::owned_id").target_signature,
        "pub unsafe fn owned_id(mut p: Option<Box<P>>) -> Option<Box<ReturnP>>"
    );
    assert_eq!(
        function(&records, "consumer::foo").target_signature,
        "pub unsafe fn foo() -> Option<Box<ReturnP>>"
    );
    let foo = &function(&records, "consumer::foo").annotated_skeleton;
    assert!(foo.contains("let mut p: Box<LocalP>"));
    assert!(foo.contains("let mut q: Option<Box<LocalQ>>"));

    let source = exact_a4_source("A4-SRC-IRRELEVANT-COLLISIONS");
    run_compiler_on_str(source, |tcx| {
        let decisions = tools_pointer_decisions(tcx);
        let allocate = local_def_path("box_only::allocate", tcx);
        assert_eq!(
            decisions.signatures.data[&allocate].output_dec,
            Some(PtrKind::Box)
        );
        assert_eq!(
            local_binding_decision(allocate, "p", &decisions, tcx),
            PtrKind::Box
        );
        let read = local_def_path("option_only::read", tcx);
        assert_eq!(
            decisions.signatures.data[&read].input_decs[0],
            Some(PtrKind::OptRef(false))
        );
        assert!(tcx.is_lang_item(
            resolved_bare_constructor(allocate, Symbol::intern("Box"), tcx),
            hir::LangItem::OwnedBox
        ));
        assert!(tcx.is_lang_item(
            resolved_bare_constructor(read, sym::Option, tcx),
            hir::LangItem::Option
        ));
    })
    .unwrap();
    let records = generate(source);
    assert!(
        function(&records, "box_only::allocate")
            .target_signature
            .contains("-> Box<i32>")
    );
    assert!(
        function(&records, "option_only::read")
            .target_signature
            .contains("p: Option<&i32>")
    );
}

#[test]
fn wholly_preserved_parent_does_not_materialize_nested_local() {
    let source = exact_a4_source("A4-SRC-PRESERVED-PARENT");
    let records = generate(source);
    let record = function(&records, "preserved");
    assert!(
        !record.statements_requiring_transformation.contains(&0),
        "the containing `if` label must remain wholly preserved"
    );
    let skeleton = &record.annotated_skeleton;
    assert!(skeleton.contains("let mut value = Local { value: 1 }"));
    assert!(!skeleton.contains("let mut value: Local"));
}

#[test]
fn type_spelling_failures_are_structured_and_atomic() {
    let option_collision = exact_a4_source("A4-SRC-OPTION-COLLISION");
    run_compiler_on_str(option_collision, |tcx| {
        assert_constructor_failure_pointer_prerequisites("A4-SRC-OPTION-COLLISION", tcx);
        let read = local_def_path("wrapped::read", tcx);
        assert_eq!(
            tcx.hir_body_owned_by(read)
                .params
                .iter()
                .map(|param| match param.pat.kind {
                    rustc_hir::PatKind::Binding(_, _, ident, None) => ident.to_string(),
                    _ => panic!("expected a simple parameter binding"),
                })
                .collect::<Vec<_>>(),
            ["first", "second"]
        );
        assert_eq!(
            resolve_one_segment_type(read, "Option", tcx),
            local_def_path("wrapped::Option", tcx).to_def_id()
        );
    })
    .unwrap();
    let error = generate_error(option_collision);
    assert_eq!(error.kind, GenerationErrorKind::TypeSpelling);
    assert_eq!(error.function_path, "wrapped::read");
    assert!(error.message.contains("parameter `first`"));
    assert!(error.message.contains("OptRef(false)"));
    assert!(error.message.contains("requires bare `Option`"));
    assert!(error.message.contains("wrapped::Option"));

    let constructor_failures = [
        (
            "A4-SRC-BOX-COLLISION",
            exact_a4_source("A4-SRC-BOX-COLLISION"),
            "wrapped::allocate",
            &["return", "Box", "wrapped::Box"][..],
        ),
        (
            "A4-SRC-RENAMED-CONSTRUCTOR-COLLISION",
            exact_a4_source("A4-SRC-RENAMED-CONSTRUCTOR-COLLISION"),
            "renamed::read",
            &["parameter `p`", "OptRef(false)", "fake::WrongOption"][..],
        ),
        (
            "A4-SRC-GLOB-CONSTRUCTOR-COLLISION",
            exact_a4_source("A4-SRC-GLOB-CONSTRUCTOR-COLLISION"),
            "globbed::allocate",
            &["return", "Box", "fake::glob::Box"][..],
        ),
        (
            "A4-SRC-OPTBOX-PARTIAL-CONSTRUCTOR-COLLISION",
            exact_a4_source("A4-SRC-OPTBOX-PARTIAL-CONSTRUCTOR-COLLISION"),
            "wrapped::owned_id",
            &["parameter `p`", "OptBox", "wrapped::Box"][..],
        ),
        (
            "A4-SRC-LOCAL-BOX-COLLISION",
            exact_a4_source("A4-SRC-LOCAL-BOX-COLLISION"),
            "consumer::local_only",
            &["local `first`", "Box", "consumer::Box"][..],
        ),
        (
            "A4-SRC-EXTERN-PRELUDE-CONSTRUCTOR-COLLISION",
            exact_a4_source("A4-SRC-EXTERN-PRELUDE-CONSTRUCTOR-COLLISION"),
            "wrapped::read",
            &["parameter `p`", "Option", "extern prelude"][..],
        ),
        (
            "A4-SRC-NO-IMPLICIT-PRELUDE-REJECTION",
            exact_a4_source("A4-SRC-NO-IMPLICIT-PRELUDE-REJECTION"),
            "wrapped::read",
            &["parameter `p`", "Option", "implicit prelude disabled"][..],
        ),
        (
            "A4-SRC-NO-STD-BOX-REJECTION",
            exact_a4_source("A4-SRC-NO-STD-BOX-REJECTION"),
            "allocate",
            &["return", "Box", "unresolved"][..],
        ),
        (
            "A4-SRC-BOX-NO-IMPLICIT-PRELUDE-REJECTION",
            exact_a4_source("A4-SRC-BOX-NO-IMPLICIT-PRELUDE-REJECTION"),
            "allocate",
            &["return", "Box", "implicit prelude disabled"][..],
        ),
        (
            "A4-SRC-MODULE-NO-IMPLICIT-PRELUDE-REJECTION",
            exact_a4_source("A4-SRC-MODULE-NO-IMPLICIT-PRELUDE-REJECTION"),
            "wrapped::read",
            &["parameter `p`", "Option", "implicit prelude disabled"][..],
        ),
        (
            "A4-SRC-ANCESTOR-NO-IMPLICIT-PRELUDE-REJECTION",
            exact_a4_source("A4-SRC-ANCESTOR-NO-IMPLICIT-PRELUDE-REJECTION"),
            "outer::middle::inner::read",
            &["parameter `p`", "Option", "implicit prelude disabled"][..],
        ),
    ];
    for (name, source, expected_path, message_parts) in constructor_failures {
        run_compiler_on_str(source, |tcx| {
            assert_constructor_failure_pointer_prerequisites(name, tcx);
            match name {
                "A4-SRC-OPTBOX-PARTIAL-CONSTRUCTOR-COLLISION" => {
                    let owned_id = local_def_path("wrapped::owned_id", tcx);
                    assert!(tcx.is_lang_item(
                        resolved_bare_constructor(owned_id, sym::Option, tcx),
                        hir::LangItem::Option
                    ));
                    assert_eq!(
                        resolve_one_segment_type(owned_id, "Box", tcx),
                        local_def_path("wrapped::Box", tcx).to_def_id()
                    );
                }
                "A4-SRC-NO-IMPLICIT-PRELUDE-REJECTION" => {
                    let read = local_def_path("wrapped::read", tcx);
                    assert!(tcx.is_lang_item(
                        resolved_bare_constructor(read, sym::Option, tcx),
                        hir::LangItem::Option
                    ));
                }
                "A4-SRC-LOCAL-BOX-COLLISION" => {
                    let local_only = local_def_path("consumer::local_only", tcx);
                    let order = local_binding_order(local_only, tcx);
                    assert_eq!(&order[..2], ["first", "second"]);
                    assert_eq!(
                        resolve_one_segment_type(local_only, "Box", tcx),
                        local_def_path("consumer::Box", tcx).to_def_id()
                    );
                }
                _ => {}
            }
        })
        .unwrap();
        let error = generate_error(source);
        assert_eq!(error.kind, GenerationErrorKind::TypeSpelling);
        assert_eq!(error.function_path, expected_path);
        for part in message_parts {
            assert!(
                error.message.contains(part),
                "{}: {}",
                expected_path,
                error.message
            );
        }
        if name == "A4-SRC-OPTBOX-PARTIAL-CONSTRUCTOR-COLLISION" {
            assert!(error.message.contains("requires bare `Box`"));
            assert!(!error.message.contains("requires bare `Option`"));
        }
    }

    let unnameable = exact_a4_source("A4-SRC-UNNAMEABLE");
    let error = generate_error(unnameable);
    assert_eq!(error.kind, GenerationErrorKind::TypeSpelling);
    assert_eq!(error.function_path, "consume");
    assert!(error.message.contains("local `iterator`"));
    assert!(
        error.message.contains("opaque")
            || error.message.contains("unnameable")
            || error.message.contains("alias")
    );
}

#[test]
fn scope_tables_and_serialized_output_are_deterministic() {
    for source in [
        exact_a4_source("A4-SRC-IMPORTS"),
        exact_a4_source("A4-SRC-CANDIDATES"),
        exact_a4_source("A4-SRC-CANDIDATE-PRECEDENCE"),
        exact_a4_source("A4-SRC-REEXPORTS"),
        exact_a4_source("A4-SRC-LOCAL-FALLBACK-ROUTES"),
        exact_a4_source("A4-SRC-EXTERNAL-ROOT-ALIAS"),
        exact_a4_source("A4-SRC-RAW-IDENTIFIERS"),
        exact_a4_source("A4-SRC-QUALIFIED-RAW-FALLBACK"),
    ] {
        let first = generate(source);
        let second = generate(source);
        assert_eq!(first, second);
        assert_eq!(
            skeletons_to_json(&first).unwrap(),
            skeletons_to_json(&second).unwrap()
        );
        run_compiler_on_str(source, |tcx| {
            for record in make_skeletons(source, tcx).unwrap() {
                if let ItemRecord::Function(function) = record {
                    utils::ast::parse_crate(function.annotated_source);
                    utils::ast::parse_crate(function.annotated_skeleton);
                }
            }
        })
        .unwrap();
    }

    let candidates = generate(exact_a4_source("A4-SRC-CANDIDATES"));
    assert!(
        function(&candidates, "aliases::inferred")
            .annotated_skeleton
            .contains("let mut value: Alpha")
    );
    assert!(
        function(&candidates, "aliases::source_hint")
            .target_signature
            .contains("&Zed")
    );
    assert!(
        function(&candidates, "collision::inferred")
            .annotated_skeleton
            .contains("crate::left::Thing")
    );
    let reexports = generate(exact_a4_source("A4-SRC-REEXPORTS"));
    assert!(
        function(&reexports, "consumer::local")
            .annotated_skeleton
            .contains("crate::api::Exposed")
    );
    assert!(
        function(&reexports, "consumer::external")
            .annotated_skeleton
            .contains("::std::hash::DefaultHasher")
    );
    let routes = generate(exact_a4_source("A4-SRC-LOCAL-FALLBACK-ROUTES"));
    for (path, ty) in [
        ("consumer::restricted", "crate::restricted_api::Exposed"),
        ("consumer::shortest", "crate::short::S"),
        ("consumer::tie", "crate::alpha::T"),
    ] {
        assert!(function(&routes, path).annotated_skeleton.contains(ty));
    }
    let aliases = generate(exact_a4_source("A4-SRC-EXTERNAL-ROOT-ALIAS"));
    assert!(
        function(&aliases, "consumer::external_alias")
            .annotated_skeleton
            .contains("::alt_std::hash::DefaultHasher")
    );

    let function_record = candidates
        .iter()
        .find(|record| record.path() == "aliases::inferred")
        .unwrap();
    assert_function_record_json_key_order(function_record);
}

fn comprehensive_fixture() -> &'static str {
    exact_a4_source("A4-SRC-COMPREHENSIVE")
}

#[test]
fn skeleton_json_is_a_top_level_array_with_pascal_case_kinds() {
    let records = generate(
        "pub unsafe fn f() {}\npub static S: i32 = 0;\npub const C: i32 = 0;\npub type A = i32;\npub enum E { V }\npub struct T { pub x: i32 }\npub union U { pub x: i32, pub y: u32 }",
    );
    assert_paths(
        &records,
        &[
            ("f", ItemKindName::Fn),
            ("S", ItemKindName::Static),
            ("C", ItemKindName::Const),
            ("A", ItemKindName::TyAlias),
            ("E", ItemKindName::Enum),
            ("T", ItemKindName::Struct),
            ("U", ItemKindName::Union),
        ],
    );
    assert!(
        serde_json::from_str::<serde_json::Value>(&skeletons_to_json(&records).unwrap())
            .unwrap()
            .is_array()
    );
}

#[test]
fn record_variants_serialize_only_their_defined_fields() {
    let records =
        generate("pub unsafe fn f() {}\npub static S: i32 = 0;\npub struct T { pub x: i32 }");
    let json: serde_json::Value =
        serde_json::from_str(&skeletons_to_json(&records).unwrap()).unwrap();
    let objects = json.as_array().unwrap();
    let keys = |index: usize| {
        objects[index]
            .as_object()
            .unwrap()
            .keys()
            .map(String::as_str)
            .collect::<std::collections::BTreeSet<_>>()
    };
    assert_eq!(
        keys(0),
        [
            "id",
            "path",
            "kind",
            "name",
            "annotated_source",
            "annotated_skeleton",
            "source_signature",
            "target_signature",
            "needs_transformation",
            "statements_requiring_transformation",
            "foreign_function_names",
            "signature_dependencies",
            "dependencies"
        ]
        .into_iter()
        .collect()
    );
    assert_eq!(
        keys(1),
        [
            "id",
            "path",
            "kind",
            "declaration",
            "signature_dependencies",
            "dependencies"
        ]
        .into_iter()
        .collect()
    );
    assert_eq!(
        keys(2),
        ["id", "path", "kind", "definition", "dependencies"]
            .into_iter()
            .collect()
    );
    assert!(!objects.iter().any(|value| {
        value
            .as_object()
            .unwrap()
            .values()
            .any(serde_json::Value::is_null)
    }));
}

#[test]
fn json_round_trip_preserves_embedded_rust_text() {
    let records = generate(
        r#"pub unsafe fn text() -> usize {
    let s = "quote:\" slash:\\ tab:\t line:\n";
    s.len()
}"#,
    );
    let before = function(&records, "text").clone();
    let round_trip: Vec<ItemRecord> =
        serde_json::from_str(&skeletons_to_json(&records).unwrap()).unwrap();
    assert_eq!(&before, function(&round_trip, "text"));
    assert_eq!(before.source_signature, "pub unsafe fn text() -> usize");
    assert!(
        before
            .annotated_skeleton
            .contains("let mut s: &str = \"quote:"),
        "{}",
        before.annotated_skeleton
    );
}

#[test]
fn json_serialization_is_byte_deterministic() {
    let source = comprehensive_fixture();
    assert_eq!(
        skeletons_to_json(&generate(source)).unwrap(),
        skeletons_to_json(&generate(source)).unwrap()
    );
}

#[test]
fn empty_crate_serializes_as_empty_array() {
    let records = generate("");
    assert!(records.is_empty());
    assert_eq!(skeletons_to_json(&records).unwrap(), "[]");
}

#[test]
fn includes_exactly_the_supported_item_kinds() {
    let records = generate(
        "pub unsafe fn f() {}\npub static S: i32 = 0;\npub static mut M: i32 = 0;\npub const C: i32 = 0;\npub type A = i32;\npub enum E { V }\npub struct Braced { pub x: i32 }\npub struct Tuple(pub i32);\npub struct Unit;\npub union U { pub x: i32, pub y: u32 }",
    );
    assert_paths(
        &records,
        &[
            ("f", ItemKindName::Fn),
            ("S", ItemKindName::Static),
            ("M", ItemKindName::Static),
            ("C", ItemKindName::Const),
            ("A", ItemKindName::TyAlias),
            ("E", ItemKindName::Enum),
            ("Braced", ItemKindName::Struct),
            ("Tuple", ItemKindName::Struct),
            ("Unit", ItemKindName::Struct),
            ("U", ItemKindName::Union),
        ],
    );
    assert_eq!(value(&records, "M").declaration, "pub static mut M: i32;");
}

#[test]
fn flattens_inline_modules_in_recursive_source_order() {
    let records = generate(
        "const A: usize = 1; mod outer { #[derive(Clone, Copy)] pub struct S { pub x: i32 } mod inner { pub unsafe fn f() {} } pub const B: usize = 2; } static Z: i32 = 0;",
    );
    assert_paths(
        &records,
        &[
            ("A", ItemKindName::Const),
            ("outer::S", ItemKindName::Struct),
            ("outer::inner::f", ItemKindName::Fn),
            ("outer::B", ItemKindName::Const),
            ("Z", ItemKindName::Static),
        ],
    );
    assert!(
        type_record(&records, "outer::S")
            .definition
            .contains("#[derive(Clone, Copy)]")
    );
}

#[test]
fn distinguishes_same_final_name_in_different_modules() {
    let records = generate(
        "mod a { pub struct T; pub unsafe fn f() {} } mod b { pub struct T; pub unsafe fn f() {} }",
    );
    assert_paths(
        &records,
        &[
            ("a::T", ItemKindName::Struct),
            ("a::f", ItemKindName::Fn),
            ("b::T", ItemKindName::Struct),
            ("b::f", ItemKindName::Fn),
        ],
    );
}

#[test]
fn preserves_raw_identifiers_in_paths_and_names() {
    let records = generate("mod r#type { pub unsafe fn r#match() {} }");
    assert_eq!(records[0].path(), "r#type::r#match");
    assert_eq!(function(&records, "r#type::r#match").name, "r#match");
}

#[test]
fn omits_modules_uses_and_extern_crates_as_records() {
    let records = generate(
        "extern crate core as rust_core; mod m { pub struct T; pub const C: i32 = 3; } use m::T as Alias; use m::*; pub unsafe fn f(_alias: Alias) -> i32 { let _ = rust_core::mem::size_of::<Alias>(); C }",
    );
    assert_paths(
        &records,
        &[
            ("m::T", ItemKindName::Struct),
            ("m::C", ItemKindName::Const),
            ("f", ItemKindName::Fn),
        ],
    );
    assert_eq!(function(&records, "f").signature_dependencies, [0]);
    assert_eq!(function(&records, "f").dependencies, [0, 1]);
}

#[test]
fn omits_foreign_modules_and_foreign_items() {
    let records = generate(
        "#![feature(extern_types)] unsafe extern \"C\" { static FOREIGN: i32; fn foreign_fn(x: i32) -> i32; type ForeignTy; } pub unsafe fn caller() -> i32 { foreign_fn(FOREIGN) }",
    );
    assert_paths(&records, &[("caller", ItemKindName::Fn)]);
    assert!(function(&records, "caller").dependencies.is_empty());
}

#[test]
fn filters_nonrecord_item_kinds_in_supported_input() {
    run_compiler_on_str("core::arch::global_asm!(\"\");", |tcx| {
        for source in [
            "extern crate core;",
            "use core::mem;",
            "mod m {}",
            "extern \"C\" {}",
        ] {
            let item = &utils::ast::parse_crate(source.to_owned()).items[0];
            assert_eq!(included_item_kind(item), None, "{source}");
        }
        let krate = utils::ast::expanded_ast(tcx);
        let global_asm = krate
            .items
            .iter()
            .find(|item| matches!(item.kind, rustc_ast::ItemKind::GlobalAsm(_)))
            .unwrap();
        assert_eq!(included_item_kind(global_asm), None);
    })
    .unwrap();
}

#[test]
fn does_not_emit_variant_field_or_constructor_records() {
    let records = generate(
        "pub struct S { pub x: i32, pub y: i32 } pub enum E { Unit, Tuple(i32), Struct { value: i32 } }",
    );
    assert_paths(
        &records,
        &[("S", ItemKindName::Struct), ("E", ItemKindName::Enum)],
    );
}

#[test]
fn type_records_preserve_complete_definitions() {
    let records = generate(
        "#[repr(C)] #[derive(Clone, Copy)] pub struct S { pub x: i32, y: u8 } #[repr(transparent)] pub struct W(pub i32); #[repr(i32)] pub enum E { A = -1, B = 4 } pub type Alias = (S, [W; 2]);",
    );
    assert!(
        type_record(&records, "S")
            .definition
            .contains("#[derive(Clone, Copy)]")
    );
    assert!(type_record(&records, "S").definition.contains("#[repr(C)]"));
    assert_eq!(type_record(&records, "Alias").dependencies, [0, 1]);
}

#[test]
fn value_records_render_declarations_without_initializers() {
    let records = generate(
        "#[no_mangle] pub static X: i32 = 1; pub static mut BUFFER: *mut u8 = core::ptr::null_mut(); pub const SIZE: usize = 4;",
    );
    assert_eq!(value(&records, "X").declaration, "pub static X: i32;");
    assert_eq!(
        value(&records, "BUFFER").declaration,
        "pub static mut BUFFER: *mut u8;"
    );
    assert_eq!(
        value(&records, "SIZE").declaration,
        "pub const SIZE: usize;"
    );
}

#[test]
fn function_records_sanitize_prompt_only_header_tokens_and_split_signatures() {
    let records = generate(
        "#[no_mangle] pub unsafe extern \"system\" fn add(x: i32, y: i32) -> i32 { x + y }",
    );
    let function = function(&records, "add");
    assert_eq!(
        function.source_signature,
        "pub unsafe fn add(mut x: i32, mut y: i32) -> i32"
    );
    assert_eq!(
        function.target_signature,
        "pub unsafe fn add(mut x: i32, mut y: i32) -> i32"
    );
    assert!(!function.annotated_source.contains("no_mangle"));
    assert!(!function.annotated_source.contains("extern"));
}

fn assert_fn_deps(source: &str, path: &str, signature: &[u64], all: &[u64]) {
    let records = generate(source);
    assert_eq!(function(&records, path).signature_dependencies, signature);
    assert_eq!(function(&records, path).dependencies, all);
}

#[test]
fn collects_direct_function_signature_type_dependencies() {
    assert_fn_deps(
        "struct In; struct Out; pub unsafe fn f(_input: In, _out: *const Out) -> Out { loop {} }",
        "f",
        &[0, 1],
        &[0, 1],
    );
}

#[test]
fn finds_types_nested_inside_signature_types() {
    assert_fn_deps(
        "struct A; struct B; struct C; struct D; struct E; struct F; pub unsafe fn nested(_a: &A, _b: *mut B, _c: [C; 2], _d: &[D], _e: (E, Option<F>)) {}",
        "nested",
        &[0, 1, 2, 3, 4, 5],
        &[0, 1, 2, 3, 4, 5],
    );
}

#[test]
fn collects_const_dependencies_from_array_lengths() {
    assert_fn_deps(
        "const N: usize = 4; struct T; pub unsafe fn f(x: [T; N]) -> [u8; N] { let _x = x; loop {} }",
        "f",
        &[0, 1],
        &[0, 1],
    );
}

#[test]
fn collects_static_and_const_signature_dependencies() {
    let records = generate(
        "#[derive(Clone, Copy)] struct T; const N: usize = 2; static mut X: *const T = core::ptr::null(); const VALUES: [T; N] = [T; N];",
    );
    assert_eq!(value(&records, "X").signature_dependencies, [0]);
    assert_eq!(value(&records, "VALUES").signature_dependencies, [0, 1]);
}

#[test]
fn collects_direct_function_calls_from_bodies() {
    assert_fn_deps(
        "pub unsafe fn callee(_x: i32) {} pub unsafe fn caller() { callee(1); callee(2); }",
        "caller",
        &[],
        &[0],
    );
}

#[test]
fn includes_direct_self_recursion() {
    assert_fn_deps(
        "pub unsafe fn recur(n: u32) -> u32 { if n == 0 { 0 } else { recur(n - 1) } }",
        "recur",
        &[],
        &[0],
    );
}

#[test]
fn collects_body_local_type_annotations_and_cast_types() {
    assert_fn_deps(
        "struct A; struct B; pub unsafe fn f() { let x: A = A; let p: *const A = &x; let _ = p as *const B; }",
        "f",
        &[],
        &[0, 1],
    );
}

#[test]
fn collects_static_and_const_uses_from_function_bodies() {
    assert_fn_deps(
        "static mut S: i32 = 1; const C: i32 = 2; pub unsafe fn f() -> i32 { S + C }",
        "f",
        &[],
        &[0, 1],
    );
}

#[test]
fn resolves_use_aliases_and_globs_to_item_ids() {
    assert_fn_deps(
        "mod m { pub struct T; pub const C: i32 = 3; } use m::T as Alias; use m::*; pub unsafe fn f(_alias: Alias) -> i32 { C }",
        "f",
        &[0],
        &[0, 1],
    );
}

#[test]
fn does_not_confuse_shadowing_locals_with_items() {
    assert_fn_deps(
        "unsafe fn value() -> i32 { 5 } pub unsafe fn f() -> i32 { let value = 1; value + crate::value() }",
        "f",
        &[],
        &[0],
    );
}

#[test]
fn ignores_foreign_and_external_dependencies() {
    assert_fn_deps(
        "unsafe extern \"C\" { fn foreign(x: i32) -> i32; static FOREIGN: i32; } pub unsafe fn f() -> usize { let x: Option<i32> = Some(foreign(FOREIGN)); core::mem::size_of_val(&x) }",
        "f",
        &[],
        &[],
    );
}

#[test]
fn dependency_lists_are_direct_not_transitive() {
    let records = generate(
        "struct A; struct B(A); pub unsafe fn callee(_b: B) {} pub unsafe fn caller(b: B) { callee(b); }",
    );
    assert_eq!(type_record(&records, "B").dependencies, [0]);
    assert_eq!(function(&records, "callee").dependencies, [1]);
    assert_eq!(function(&records, "caller").dependencies, [1, 2]);
}

#[test]
fn canonicalizes_struct_constructors_to_struct_records() {
    assert_fn_deps(
        "struct A { x: i32 } struct B(i32); struct C; pub unsafe fn f() { let _ = A { x: 1 }; let _ = B(2); let _ = C; let _ = A { x: 3 }; }",
        "f",
        &[],
        &[0, 1, 2],
    );
}

#[test]
fn canonicalizes_enum_variants_in_expressions_and_patterns() {
    assert_fn_deps(
        "enum E { Unit, Tuple(i32), Struct { x: i32 } } pub unsafe fn f(tag: i32) -> i32 { let e = if tag == 0 { E::Unit } else { E::Tuple(tag) }; let _ = E::Struct { x: tag }; match e { E::Unit => { 0 } E::Tuple(x) => { x } E::Struct { x } => { x } } }",
        "f",
        &[],
        &[0],
    );
}

#[test]
fn canonicalizes_field_accesses_to_containing_types() {
    assert_fn_deps(
        "struct S { x: i32, y: i32 } struct T(i32); unsafe fn make_s() -> S { S { x: 1, y: 2 } } unsafe fn make_t() -> T { T(3) } pub unsafe fn f() -> i32 { let mut s = make_s(); let t = make_t(); s.x = s.y; s.x + t.0 }",
        "f",
        &[],
        &[0, 1, 2, 3],
    );
}

#[test]
fn collects_initializer_dependencies_for_statics_and_consts() {
    let records = generate(
        "struct Marker; const BASE: i32 = 1; static X: i32 = BASE; const Y: Marker = Marker;",
    );
    assert!(value(&records, "X").signature_dependencies.is_empty());
    assert_eq!(value(&records, "X").dependencies, [1]);
    assert_eq!(value(&records, "Y").signature_dependencies, [0]);
    assert_eq!(value(&records, "Y").dependencies, [0]);
}

#[test]
fn collects_type_alias_dependencies() {
    let records =
        generate("const N: usize = 4; struct S; type A = S; type B = Option<(*mut A, [S; N])>;");
    assert_eq!(type_record(&records, "A").dependencies, [1]);
    assert_eq!(type_record(&records, "B").dependencies, [0, 1, 2]);
}

#[test]
fn collects_struct_and_union_field_dependencies() {
    let records = generate(
        "struct A; type I = i32; struct Braced { a: *const A, i: I } struct Tuple(*mut A, I); union U { a: *const A, i: I }",
    );
    for path in ["Braced", "Tuple", "U"] {
        assert_eq!(type_record(&records, path).dependencies, [0, 1]);
    }
}

#[test]
fn collects_enum_payload_and_discriminant_dependencies() {
    let records = generate(
        "const D: isize = 1; struct A; struct B; #[repr(isize)] enum E { One(A) = D, Two { b: B } = 2 }",
    );
    assert_eq!(type_record(&records, "E").dependencies, [0, 1, 2]);
}

#[test]
fn handles_self_recursive_and_mutually_recursive_types() {
    let records =
        generate("struct Node { next: *mut Node } struct A { b: *mut B } struct B { a: *mut A }");
    assert_eq!(type_record(&records, "Node").dependencies, [0]);
    assert_eq!(type_record(&records, "A").dependencies, [2]);
    assert_eq!(type_record(&records, "B").dependencies, [1]);
}

#[test]
fn resolves_same_spelling_in_value_and_type_namespaces() {
    let records =
        generate("type X = i32; const X: i32 = 7; pub unsafe fn f(x: X) -> i32 { X + x }");
    assert_eq!(function(&records, "f").signature_dependencies, [0]);
    assert_eq!(function(&records, "f").dependencies, [0, 1]);
}

#[test]
fn dependency_lists_are_deduplicated_sorted_and_subset_consistent() {
    assert_fn_deps(
        "struct A; struct B; struct C; pub unsafe fn f(_c: C, _a: *const A) -> A { let _: B = B; let _: B = B; loop {} }",
        "f",
        &[0, 2],
        &[0, 1, 2],
    );
}

fn labels(text: &str) -> Vec<u32> {
    let mut rest = text;
    let mut labels = vec![];
    while let Some(start) = rest.find("#[proctor(") {
        rest = &rest[start + "#[proctor(".len()..];
        let end = rest.find(')').unwrap();
        labels.push(rest[..end].parse().unwrap());
        rest = &rest[end + 1..];
    }
    labels
}

#[test]
fn labels_let_semi_and_tail_statements() {
    let records = generate(
        "unsafe extern \"C\" { fn consume(x: i32); } pub unsafe fn f() -> i32 { let x = 1; consume(x); x }",
    );
    let f = function(&records, "f");
    assert_eq!(labels(&f.annotated_source), [0, 1, 2]);
    assert_eq!(labels(&f.annotated_skeleton), [0, 1, 2]);
}

#[test]
fn labels_reset_for_each_function() {
    let records = generate(
        "pub unsafe fn a() -> i32 { let x = 1; x } pub unsafe fn b() -> i32 { let y = 2; y + 1 }",
    );
    for path in ["a", "b"] {
        assert_eq!(labels(&function(&records, path).annotated_source), [0, 1]);
        assert_eq!(labels(&function(&records, path).annotated_skeleton), [0, 1]);
    }
}

#[test]
fn nested_labels_follow_depth_first_preorder() {
    let records = generate(
        "unsafe fn hit(_x: i32) {} pub unsafe fn f(flag: bool) { if flag { hit(1); loop { hit(2); break; } } else { hit(3); } hit(4); }",
    );
    assert_eq!(
        labels(&function(&records, "f").annotated_source),
        [0, 1, 2, 3, 4, 5, 6]
    );
}

#[test]
fn source_and_skeleton_have_identical_label_trees() {
    let records = generate(comprehensive_control_fixture());
    let f = function(&records, "comprehensive");
    assert_eq!(labels(&f.annotated_source), (0..=11).collect::<Vec<_>>());
    assert_eq!(labels(&f.annotated_source), labels(&f.annotated_skeleton));
}

#[test]
fn rejects_top_level_empty_statement_in_function() {
    let error = generate_error("pub unsafe fn f() { ; }");
    assert_eq!(error.kind, GenerationErrorKind::EmptyStatement);
    assert_eq!(error.function_path, "f");
    assert!(
        error
            .message
            .contains("empty statement cannot be annotated")
    );
}

#[test]
fn rejects_nested_empty_statement() {
    let error = generate_error("pub unsafe fn f(flag: bool) { if flag { loop { ; } } }");
    assert_eq!(error.kind, GenerationErrorKind::EmptyStatement);
    assert_eq!(error.function_path, "f");
}

#[test]
fn phase_1_rejects_local_const_and_static_recursively() {
    for (source, kind) in [
        (
            r#"pub unsafe fn f() -> i32 {
                const LOCAL: i32 = { let inner = 1; inner };
                LOCAL
            }"#,
            "const",
        ),
        (
            r#"pub unsafe fn f(flag: bool) -> i32 {
                if flag {
                    static mut STATE: i32 = { let inner = 1; inner };
                    STATE
                } else {
                    0
                }
            }"#,
            "static",
        ),
    ] {
        let error = generate_error(source);
        assert_eq!(error.kind, GenerationErrorKind::FunctionLocalItem);
        assert_eq!(error.function_path, "f");
        assert!(error.message.contains(kind));
    }
}

#[test]
fn phase_1_rejects_representative_other_local_items() {
    for (source, kind) in [
        ("pub unsafe fn f() { fn local() {} }", "function"),
        ("pub unsafe fn f() { type Local = i32; }", "type alias"),
        ("pub unsafe fn f() { struct Local; }", "struct"),
        ("pub unsafe fn f() { enum Local { Variant } }", "enum"),
        ("pub unsafe fn f() { union Local { field: i32 } }", "union"),
        ("pub unsafe fn f() { mod local {} }", "module"),
        ("pub unsafe fn f() { use core::mem; }", "use"),
        (
            "pub unsafe fn f() { unsafe extern \"C\" { fn local(); } }",
            "foreign",
        ),
        ("pub unsafe fn f() { trait Local {} }", "trait"),
        ("struct Local; pub unsafe fn f() { impl Local {} }", "impl"),
        (
            "pub unsafe fn f() { macro_rules! local { () => {} } }",
            "macro definition",
        ),
    ] {
        let error = generate_error(source);
        assert_eq!(error.kind, GenerationErrorKind::FunctionLocalItem);
        assert_eq!(error.function_path, "f");
        assert!(error.message.contains(kind), "{source}: {}", error.message);
    }
}

#[test]
fn replaces_leaf_expression_payloads_with_todo() {
    let source = "unsafe fn callee(_x: i32) {} pub unsafe fn f() -> i32 { let x = 1; callee(x); println!(\"{x}\"); -x + 2 }";
    let records = generate(source);
    let skeleton = &function(&records, "f").annotated_skeleton;
    assert!(skeleton.contains("let mut x: i32 = 1;"));
    assert_eq!(skeleton.matches("todo!()").count(), 1);
    assert_eq!(labels(skeleton), [0, 1, 2, 3]);
    assert_skeleton(
        source,
        "f",
        "pub unsafe fn f() -> i32 { let x: i32 = 1; callee(x); todo!(); -x + 2 }",
    );
}

#[test]
fn materializes_inferred_types_for_simple_bindings() {
    let source = "struct Local; pub unsafe fn f() { let b = true; let i = -1i32; let u = 1u64; let n = 1.5f32; let c = 'x'; let t = (1i32, 2u8); let a = [1u16; 3]; let r = &i; let l = Local; }";
    let records = generate(source);
    let skeleton = compact(&function(&records, "f").annotated_skeleton);
    for declaration in [
        "let mut b: bool = true;",
        "let mut i: i32 = -1i32;",
        "let mut u: u64 = 1u64;",
        "let mut n: f32 = 1.5f32;",
        "let mut c: char = 'x';",
        "let mut t: (i32, u8) = (1i32, 2u8);",
        "let mut a: [u16; 3] = [1u16; 3];",
        "let mut r: &i32 = &i;",
        "let mut l: Local = Local;",
    ] {
        assert!(
            skeleton.contains(declaration),
            "missing {declaration} in {skeleton}"
        );
    }
    assert_skeleton(
        source,
        "f",
        "pub unsafe fn f() { let b: bool = true; let i: i32 = -1i32; let u: u64 = 1u64; let n: f32 = 1.5f32; let c: char = 'x'; let t: (i32, u8) = (1i32, 2u8); let a: [u16; 3] = [1u16; 3]; let r: &i32 = &i; let l: Local = Local; }",
    );
}

#[test]
fn preserves_mutability_declarations_and_existing_types() {
    let source = "struct T; type Count = i32; pub unsafe fn f() { let mut a = 1; let x: T; let y: Count = 2; x = T; let _ = (a, x, y); }";
    let records = generate(source);
    let skeleton = compact(&function(&records, "f").annotated_skeleton);
    assert!(skeleton.contains("let mut a: i32 = 1;"));
    assert!(skeleton.contains("let mut x: T;"));
    assert!(skeleton.contains("let mut y: Count = 2;"));
    assert_eq!(skeleton.matches("todo!()").count(), 0);
    assert_skeleton(
        source,
        "f",
        "pub unsafe fn f() { let mut a: i32 = 1; let x: T; let y: Count = 2; x = T; let _ = (a, x, y); }",
    );
}

#[test]
fn holes_assignments_and_preserves_return_and_break_roles() {
    let source = "pub unsafe fn f(mut x: i32) -> i32 { x = 1; x += 2; let y = loop { break x; }; return y; }";
    let records = generate(source);
    let skeleton = compact(&function(&records, "f").annotated_skeleton);
    assert!(skeleton.contains("let mut y: i32 = loop"));
    assert!(skeleton.contains("break x;"));
    assert!(skeleton.contains("return y;"));
    assert_skeleton(
        source,
        "f",
        "pub unsafe fn f(mut x: i32) -> i32 { x = 1; x += 2; let y: i32 = loop { break x; }; return y; }",
    );
}

#[test]
fn preserves_if_and_else_structure() {
    let source = "unsafe fn sink(_x: i32) {} pub unsafe fn f(flag: bool) { if flag { sink(1); } else { sink(2); } }";
    let records = generate(source);
    let skeleton = compact(&function(&records, "f").annotated_skeleton);
    assert!(skeleton.contains("if flag"));
    assert!(skeleton.contains("} else {"));
    assert_eq!(
        labels(&function(&records, "f").annotated_skeleton),
        [0, 1, 2]
    );
    assert_skeleton(
        source,
        "f",
        "pub unsafe fn f(flag: bool) { if flag { sink(1); } else { sink(2); } }",
    );
}

#[test]
fn preserves_nested_if_and_else_if_structure() {
    let source = "pub unsafe fn f(a: bool, b: bool, c: bool) -> i32 { let x = if a { 1 } else { 2 }; if b { if c { x } else { 3 } } else if a { 4 } else { 5 } }";
    let records = generate(source);
    let f = function(&records, "f");
    assert_eq!(labels(&f.annotated_skeleton), (0..=8).collect::<Vec<_>>());
    assert_eq!(f.annotated_skeleton.matches("if ").count(), 4);
    assert_skeleton(
        source,
        "f",
        "pub unsafe fn f(a: bool, b: bool, c: bool) -> i32 { let x: i32 = if a { 1 } else { 2 }; if b { if c { x } else { 3 } } else if a { 4 } else { 5 } }",
    );
}

#[test]
fn preserves_if_let_and_while_let_patterns() {
    let source = "unsafe fn sink(_x: i32) {} pub unsafe fn f(mut value: Option<i32>) { if let Some(x) = value { sink(x); } while let Some(x) = value { sink(x); value = None; } }";
    let records = generate(source);
    let skeleton = compact(&function(&records, "f").annotated_skeleton);
    assert!(skeleton.contains("if let Some(mut x) = value"));
    assert!(skeleton.contains("while let Some(mut x) = value"));
    assert_skeleton(
        source,
        "f",
        "pub unsafe fn f(mut value: Option<i32>) { if let Some(x) = value { sink(x); } while let Some(x) = value { sink(x); value = None; } }",
    );
}

#[test]
fn preserves_while_for_and_loop_constructs() {
    let source = "unsafe fn sink(_x: i32) {} pub unsafe fn f(mut n: i32, pairs: [(i32, i32); 2]) { 'w: while n > 0 { n -= 1; } for (x, y) in pairs { sink(x + y); } 'l: loop { break 'l; } }";
    let records = generate(source);
    let skeleton = compact(&function(&records, "f").annotated_skeleton);
    assert!(skeleton.contains("'w: while n > 0"));
    assert!(skeleton.contains("for (mut x, mut y) in todo!()"));
    assert!(skeleton.contains("'l: loop"));
    assert_skeleton(
        source,
        "f",
        "pub unsafe fn f(mut n: i32, pairs: [(i32, i32); 2]) { 'w: while n > 0 { n -= 1; } for (x, y) in todo!() { sink(x + y); } 'l: loop { break 'l; } }",
    );
}

#[test]
fn preserves_match_arms_patterns_guards_and_order() {
    let source = "enum E { Unit, Tuple(i32), Struct { x: i32 } } unsafe fn sink(_x: i32) {} pub unsafe fn f(e: E, n: i32, pair: (i32, i32)) -> i32 { let a = match e { E::Unit => { 0 } E::Tuple(x) if x > 0 => { x } E::Tuple(_) => { -1 } E::Struct { x } => { sink(x); x }, }; let b = match n { 0 => { 0 } 1..=3 => { 1 } _ => { 2 } }; match pair { (x, y) => { a + b + x + y } } }";
    let records = generate(source);
    let f = function(&records, "f");
    assert_eq!(labels(&f.annotated_skeleton), (0..=11).collect::<Vec<_>>());
    let skeleton = compact(&f.annotated_skeleton);
    assert!(skeleton.contains("E::Tuple(mut x) if x > 0"));
    assert!(skeleton.contains("1..=3 =>"));
    assert_skeleton(
        source,
        "f",
        "pub unsafe fn f(e: E, n: i32, pair: (i32, i32)) -> i32 { let a: i32 = match e { E::Unit => { 0 } E::Tuple(x) if x > 0 => { x } E::Tuple(_) => { -1 } E::Struct { x } => { sink(x); x }, }; let b: i32 = match todo!() { 0 => { 0 } 1..=3 => { 1 } _ => { 2 } }; match pair { (x, y) => { a + b + x + y } } }",
    );
}

#[test]
fn preserves_let_else_and_plain_nested_blocks() {
    let source = "unsafe fn sink(_x: i32) {} pub unsafe fn f(value: Option<i32>) -> i32 { let Some(x): Option<i32> = value else { return 0; }; let y = { sink(x); x + 1 }; y }";
    let records = generate(source);
    let f = function(&records, "f");
    assert_eq!(labels(&f.annotated_skeleton), [0, 1, 2, 3, 4, 5]);
    let skeleton = compact(&f.annotated_skeleton);
    assert!(skeleton.contains("let Some(mut x): Option<i32> = value else"));
    assert!(skeleton.contains("return 0;"));
    assert_skeleton(
        source,
        "f",
        "pub unsafe fn f(value: Option<i32>) -> i32 { let Some(x): Option<i32> = value else { return 0; }; let y: i32 = { sink(x); x + 1 }; y }",
    );
}

#[test]
fn preserves_existing_identifiers_paths_and_patterns() {
    let source = "mod m { pub struct Pair { pub left: i32, pub right: i32 } } pub unsafe fn keep_names(mut input_value: m::Pair) -> i32 { let mut local_total = input_value.left; 'outer: loop { let m::Pair { left: bound_left, right: bound_right } = input_value; local_total += bound_left + bound_right; break 'outer; } local_total }";
    let records = generate(source);
    let skeleton = &function(&records, "keep_names").annotated_skeleton;
    for name in ["input_value", "local_total", "bound_left", "bound_right"] {
        assert!(skeleton.contains(name));
    }
    for forbidden in ["__crat", "proctor_tmp"] {
        assert!(!skeleton.contains(forbidden));
    }
    assert_skeleton(
        source,
        "keep_names",
        "pub unsafe fn keep_names(mut input_value: m::Pair) -> i32 { let mut local_total: i32 = input_value.left; 'outer: loop { let m::Pair { left: bound_left, right: bound_right } = input_value; local_total += bound_left + bound_right; break 'outer; } local_total }",
    );
}

fn comprehensive_control_fixture() -> &'static str {
    "unsafe fn sink(_x: i32) {} pub unsafe fn comprehensive(mut n: i32) -> i32 { if n > 0 { sink(n); } while n > 1 { n -= 1; } for i in 0..n { sink(i); } loop { break; } match n { 0 => { sink(0); } _ => { sink(n); } } n }"
}

#[test]
fn annotated_source_and_skeleton_snippets_parse_independently() {
    let records = generate(comprehensive_control_fixture());
    let f = function(&records, "comprehensive");
    assert_eq!(labels(&f.annotated_source), (0..=11).collect::<Vec<_>>());
    run_compiler_on_str(&f.annotated_source, |_| ()).unwrap();
    run_compiler_on_str(&f.annotated_skeleton, |_| ()).unwrap();
}

#[test]
fn preserves_payloadless_control_expressions_without_holes() {
    let source =
        "pub unsafe fn f(flag: bool) { if flag { return; } loop { if flag { continue; } break; } }";
    let records = generate(source);
    let skeleton = &function(&records, "f").annotated_skeleton;
    for expression in ["return;", "continue;", "break;"] {
        assert_eq!(skeleton.matches(expression).count(), 1);
    }
    assert_eq!(labels(skeleton), [0, 1, 2, 3, 4, 5]);
    assert_skeleton(
        source,
        "f",
        "pub unsafe fn f(flag: bool) { if flag { return; } loop { if flag { continue; } break; } }",
    );
}

#[test]
fn rejects_non_block_match_arm() {
    let error = generate_error("pub unsafe fn f(n: i32) -> i32 { match n { 0 => 1, _ => { 2 } } }");
    assert_eq!(error.kind, GenerationErrorKind::NonBlockMatchArm);
    assert_eq!(error.function_path, "f");
    assert!(
        error
            .message
            .contains("match arm body must be a block expression")
    );
}

#[test]
fn allows_restricted_conditionals_beneath_non_control_payloads() {
    let source = "
        pub unsafe fn assign(mut value: i32, flag: bool) {
            value = 1 + if flag { 2 } else { 3 };
        }
        pub unsafe fn wrapped_return(flag: bool) -> Option<i32> {
            return Some(if flag { 1 } else { 2 });
        }
        pub unsafe fn wrapped_let(flag: bool) -> i32 {
            let value = Some(if flag { 1 } else { 2 });
            value.unwrap()
        }
    ";
    let records = generate(source);
    for path in ["assign", "wrapped_return"] {
        let function = function(&records, path);
        assert_eq!(labels(&function.annotated_source), [0]);
        assert_eq!(labels(&function.annotated_skeleton), [0]);
        assert!(function.annotated_skeleton.contains("if "));
    }
    let wrapped_let = function(&records, "wrapped_let");
    assert_eq!(labels(&wrapped_let.annotated_source), [0, 1]);
    assert_eq!(labels(&wrapped_let.annotated_skeleton), [0, 1]);
    assert_skeleton(
        source,
        "assign",
        "pub unsafe fn assign(mut value: i32, flag: bool) { value = 1 + if flag { 2 } else { 3 }; }",
    );
    assert_skeleton(
        source,
        "wrapped_return",
        "pub unsafe fn wrapped_return(flag: bool) -> Option<i32> { return Some(if flag { 1 } else { 2 }); }",
    );
    assert_skeleton(
        source,
        "wrapped_let",
        "pub unsafe fn wrapped_let(flag: bool) -> i32 { let value: ::core::option::Option<i32> = Some(if flag { 1 } else { 2 }); value.unwrap() }",
    );
}

#[test]
fn allows_else_if_chains_and_recursive_branch_tail_conditionals() {
    let source = "
        pub unsafe fn chained(c1: bool, c2: bool) -> i32 {
            let value = Some(if c1 { 1 } else if c2 { 2 } else { 3 });
            value.unwrap()
        }
        pub unsafe fn nested(c1: bool, c2: bool) -> i32 {
            let value = Some(if c1 {
                1
            } else {
                if c2 { 2 } else { 3 }
            });
            value.unwrap()
        }
    ";
    let records = generate(source);
    for path in ["chained", "nested"] {
        let function = function(&records, path);
        assert_eq!(labels(&function.annotated_source), [0, 1]);
        assert_eq!(labels(&function.annotated_skeleton), [0, 1]);
        assert_eq!(function.annotated_source.matches("if ").count(), 2);
        assert!(function.annotated_skeleton.contains("if "));
        assert_skeleton(
            source,
            path,
            &format!(
                "pub unsafe fn {path}(c1: bool, c2: bool) -> i32 {{ let value: ::core::option::Option<i32> = {}; value.unwrap() }}",
                if path == "chained" {
                    "Some(if c1 { 1 } else if c2 { 2 } else { 3 })"
                } else {
                    "Some(if c1 { 1 } else { if c2 { 2 } else { 3 } })"
                }
            ),
        );
    }
}

#[test]
fn opaque_restricted_conditionals_keep_original_dependencies() {
    let source = "
        unsafe fn branch_value() -> i32 { 1 }
        pub unsafe fn f(flag: bool) -> i32 {
            let value = Some(if flag { branch_value() } else { 0 });
            value.unwrap()
        }
    ";
    let records = generate(source);
    let branch_id = record(&records, "branch_value").id();
    assert!(function(&records, "f").dependencies.contains(&branch_id));
}

#[test]
fn opaque_conditional_label_suppression_does_not_skip_body_validation() {
    let local_item = generate_error(
        "pub unsafe fn f(flag: bool) { let value = Some(if flag { { const LOCAL: i32 = 1; LOCAL } } else { 0 }); let _ = value; }",
    );
    assert_eq!(local_item.kind, GenerationErrorKind::FunctionLocalItem);
    assert!(local_item.message.contains("const"));

    let non_block_arm = generate_error(
        "pub unsafe fn f(flag: bool) { let value = Some(if flag { match 0 { 0 => 1, _ => { 2 } } } else { 3 }); let _ = value; }",
    );
    assert_eq!(non_block_arm.kind, GenerationErrorKind::NonBlockMatchArm);
}

#[test]
fn rejects_non_restricted_control_beneath_non_control_payloads() {
    for source in [
        "pub unsafe fn f(mut value: i32, flag: bool) { value = 1 + if flag { value += 1; 2 } else { 3 }; }",
        "pub unsafe fn f(mut value: i32, c1: bool, c2: bool) { value = 1 + if c1 { if c2 { value += 1; 2 } else { 3 } } else { 4 }; }",
        "pub unsafe fn f(flag: bool) { let value = Some(if flag { () }); let _ = value; }",
        "pub unsafe fn f(value: Option<i32>) { let result = Some(if let Some(value) = value { value } else { 0 }); let _ = result; }",
        "#![feature(let_chains)] pub unsafe fn f(value: Option<i32>) { let result = Some(if let Some(value) = value && value > 0 { value } else { 0 }); let _ = result; }",
        "pub unsafe fn f() { let value = Some(loop { break 1; }); let _ = value; }",
        "pub unsafe fn f(c1: bool, c2: bool) { let value = Some(if c1 { 1 + if c2 { 2 } else { 3 } } else { 4 }); let _ = value; }",
        "pub unsafe fn f(flag: bool) { let value = Some(if flag { 1; } else { 2; }); let _ = value; }",
    ] {
        let error = generate_error(source);
        assert_eq!(error.kind, GenerationErrorKind::NestedControlPayload);
        assert_eq!(error.function_path, "f");
        assert!(
            error
                .message
                .contains("control expression nested beneath a non-control payload")
        );
    }
}

#[test]
fn keeps_non_pointer_signature_types_unchanged() {
    let records = generate(
        "struct S { x: i32 } pub unsafe fn f(a: i32, b: (u8, bool), c: [i16; 2], s: S) -> (S, usize) { (s, a as usize + b.0 as usize + c[0] as usize) }",
    );
    let f = function(&records, "f");
    assert_eq!(
        f.source_signature,
        "pub unsafe fn f(mut a: i32, mut b: (u8, bool), mut c: [i16; 2], mut s: S)\n-> (S, usize)"
    );
    assert_eq!(
        f.target_signature,
        "pub unsafe fn f(mut a: i32, mut b: (u8, bool), mut c: [i16; 2], mut s: S)\n-> (S, usize)"
    );
}

fn scalar_reference_fixture() -> &'static str {
    "pub unsafe fn read_param(p: *const i32) -> i32 { *p } pub unsafe fn write_local() -> i32 { let mut x = 0i32; let p: *mut i32 = &mut x; *p = 7; x } pub unsafe fn read_local() -> i32 { let x = 7i32; let p: *const i32 = &x; *p }"
}

#[test]
fn selects_shared_and_mutable_scalar_references() {
    let records = generate(scalar_reference_fixture());
    assert!(
        function(&records, "read_param")
            .target_signature
            .contains("mut p: &i32")
    );
    assert!(
        function(&records, "write_local")
            .annotated_skeleton
            .contains("let mut p: &mut i32")
    );
    assert!(
        function(&records, "read_local")
            .annotated_skeleton
            .contains("let mut p: &i32")
    );
}

fn optional_reference_fixture() -> &'static str {
    "pub unsafe fn read(p: *const i32) -> i32 { if p.is_null() { 0 } else { *p } } pub unsafe fn write(p: *mut i32) { if !p.is_null() { *p = 1; } }"
}

#[test]
fn selects_optional_references_when_null_is_observable() {
    let records = generate(optional_reference_fixture());
    assert_eq!(
        function(&records, "read").target_signature,
        "pub unsafe fn read(mut p: Option<&i32>) -> i32"
    );
    assert_eq!(
        function(&records, "write").target_signature,
        "pub unsafe fn write(mut p: Option<&mut i32>)"
    );
}

fn array_pointer_fixture() -> &'static str {
    "pub unsafe fn read_array(a: [i32; 4]) -> i32 { let p: *const i32 = a.as_ptr(); *p.offset(1) } pub unsafe fn write_array(mut a: [i32; 4]) -> i32 { let p: *mut i32 = a.as_mut_ptr(); *p.offset(1) = 9; a[1] }"
}

#[test]
fn selects_shared_and_mutable_slices_for_array_borrows() {
    let records = generate(array_pointer_fixture());
    assert!(
        function(&records, "read_array")
            .annotated_skeleton
            .contains("let mut p: &[i32]")
    );
    assert!(
        function(&records, "write_array")
            .annotated_skeleton
            .contains("let mut p: &mut [i32]")
    );
    assert!(!skeletons_to_json(&records).unwrap().contains("SliceCursor"));
}

#[test]
fn promotes_array_derived_locals_to_explicit_slices() {
    let records = generate(array_pointer_fixture());
    assert!(
        function(&records, "read_array")
            .annotated_skeleton
            .contains("let mut p: &[i32] = todo!();")
    );
    assert!(
        function(&records, "write_array")
            .annotated_skeleton
            .contains("let mut p: &mut [i32] = todo!();")
    );
}

fn scalar_box_fixture() -> &'static str {
    "unsafe extern \"C\" { fn malloc(size: usize) -> *mut i32; } pub unsafe fn alloc() -> *mut i32 { let p: *mut i32 = malloc(core::mem::size_of::<i32>()); *p = 7; p }"
}

#[test]
fn selects_scalar_box_types_from_ownership_analysis() {
    let records = generate(scalar_box_fixture());
    let alloc = function(&records, "alloc");
    assert_eq!(alloc.target_signature, "pub unsafe fn alloc() -> Box<i32>");
    assert!(
        alloc
            .annotated_skeleton
            .contains("let mut p: Box<i32> = todo!();")
    );
}

fn boxed_slice_fixture() -> &'static str {
    "unsafe extern \"C\" { fn calloc(count: usize, size: usize) -> *mut i32; } pub unsafe fn alloc_array() -> *mut i32 { let p: *mut i32 = calloc(4, core::mem::size_of::<i32>()); *p.offset(1) = 7; p }"
}

#[test]
fn selects_boxed_slice_types_from_ownership_and_fatness() {
    let records = generate(boxed_slice_fixture());
    let alloc = function(&records, "alloc_array");
    assert_eq!(
        alloc.target_signature,
        "pub unsafe fn alloc_array() -> Box<[i32]>"
    );
    assert!(
        alloc
            .annotated_skeleton
            .contains("let mut p: Box<[i32]> = todo!();")
    );
}

#[test]
fn adds_named_lifetimes_for_returned_borrows() {
    let records = generate(
        "pub unsafe fn id(x: *mut i32) -> *mut i32 { x } pub unsafe fn wrap(y: *mut i32) -> *mut i32 { id(y) }",
    );
    assert_eq!(
        function(&records, "id").target_signature,
        "pub unsafe fn id<'a>(mut x: &'a mut i32) -> &'a mut i32"
    );
    assert_eq!(
        function(&records, "wrap").target_signature,
        "pub unsafe fn wrap<'a>(mut y: &'a mut i32) -> &'a mut i32"
    );
}

#[test]
fn preserves_nullable_returned_borrow_relationships() {
    let records = generate(
        "pub unsafe fn maybe(flag: bool, x: *mut i32) -> *mut i32 { if flag { x } else { core::ptr::null_mut() } } pub unsafe fn maybe_local(flag: bool, x: *mut i32) -> *mut i32 { let r = if flag { x } else { core::ptr::null_mut() }; r }",
    );
    for path in ["maybe", "maybe_local"] {
        let signature = &function(&records, path).target_signature;
        assert!(
            signature.contains("mut x: Option<&'a mut i32>"),
            "{signature}"
        );
        assert!(signature.contains("-> Option<&'a mut i32>"), "{signature}");
    }
    assert!(
        function(&records, "maybe_local")
            .annotated_skeleton
            .contains("let mut r: Option<&mut i32>")
    );
}

fn raw_pointer_fixture() -> &'static str {
    "unsafe extern \"C\" { fn malloc(size: usize) -> *mut core::ffi::c_void; } static mut SLOT: *mut *mut i32 = core::ptr::null_mut(); pub unsafe fn void_address(out: *mut core::ffi::c_void) -> usize { out as usize } pub unsafe fn keep_alias_raw(a: *mut i32, b: *mut i32) -> *mut i32 { *a = 1; *b = 2; a } pub unsafe fn drive_alias(p: *mut i32) -> *mut i32 { keep_alias_raw(p, p) } pub unsafe fn main_0() { let _ = drive_alias(malloc(core::mem::size_of::<i32>()) as *mut i32); } pub unsafe fn alias_caller() -> i32 { let mut x = 7i32; let p: *mut i32 = &mut x; *p = 8; *p } pub unsafe fn global_escape() { let p: *mut *mut i32 = malloc(core::mem::size_of::<*mut i32>()) as *mut *mut i32; *p = core::ptr::null_mut(); SLOT = p; }"
}

#[test]
fn keeps_required_raw_pointers_raw() {
    let records = generate(raw_pointer_fixture());
    assert!(
        function(&records, "void_address")
            .target_signature
            .contains("*mut core::ffi::c_void"),
        "{}",
        function(&records, "void_address").target_signature
    );
    assert!(
        function(&records, "keep_alias_raw")
            .target_signature
            .contains("mut a: *mut i32, mut b: *mut i32"),
        "{}",
        function(&records, "keep_alias_raw").target_signature
    );
    assert!(
        function(&records, "global_escape")
            .annotated_skeleton
            .contains("let mut p: *mut *mut i32")
    );
}

fn named_types_fixture() -> &'static str {
    "pub struct S { pub p: *mut i32 } pub union U { pub p: *const i32, pub bits: usize } pub enum E { Ptr(*mut i32), Empty } pub type Alias = *const i32; pub static mut GLOBAL: *mut i32 = core::ptr::null_mut(); pub const NIL: *const i32 = core::ptr::null(); pub unsafe fn use_all(s: S, u: U, e: E, a: Alias) -> usize { let _ = (s, u, e, a, GLOBAL, NIL); 0 }"
}

#[test]
fn does_not_change_named_type_or_global_declarations() {
    let records = generate(named_types_fixture());
    assert!(type_record(&records, "S").definition.contains("*mut i32"));
    assert!(
        type_record(&records, "Alias")
            .definition
            .contains("*const i32")
    );
    assert_eq!(
        function(&records, "use_all").signature_dependencies,
        [0, 1, 2, 3]
    );
    assert_eq!(
        function(&records, "use_all").dependencies,
        [0, 1, 2, 3, 4, 5]
    );
}

fn local_struct_demotion_fixture() -> &'static str {
    exact_a4_source("A4-SRC-TREE")
}

#[test]
fn uses_initial_decisions_before_rewriter_fallback_demotion() {
    let source = local_struct_demotion_fixture();
    let records = generate(source);
    assert_eq!(
        function(&records, "tree_print_helper").target_signature,
        "pub unsafe fn tree_print_helper(mut tree: &mut Tree, mut root_id: i32)"
    );
    let rewritten = run_compiler_on_str(source, |tcx| {
        pointer_replacer::replace_local_borrows(&pointer_replacer::Config::default(), tcx).0
    })
    .unwrap();
    assert!(rewritten.contains("fn tree_print_helper(mut tree: *mut crate::Tree, root_id: i32)"));
}

#[test]
fn all_simple_locals_receive_final_explicit_target_types() {
    type ExpectedLocal<'a> = (&'a str, &'a str, &'a str);
    type Fixture<'a> = (&'a str, &'a [ExpectedLocal<'a>]);

    let fixtures: [Fixture<'_>; 7] = [
        (
            scalar_reference_fixture(),
            &[
                ("write_local", "x", "i32"),
                ("write_local", "p", "&mut i32"),
                ("read_local", "x", "i32"),
                ("read_local", "p", "&i32"),
            ],
        ),
        (optional_reference_fixture(), &[]),
        (
            array_pointer_fixture(),
            &[
                ("read_array", "p", "&[i32]"),
                ("write_array", "p", "&mut [i32]"),
            ],
        ),
        (scalar_box_fixture(), &[("alloc", "p", "Box<i32>")]),
        (boxed_slice_fixture(), &[("alloc_array", "p", "Box<[i32]>")]),
        (
            raw_pointer_fixture(),
            &[
                ("alias_caller", "x", "i32"),
                ("alias_caller", "p", "&mut i32"),
                ("global_escape", "p", "*mut *mut i32"),
            ],
        ),
        (
            optional_box_fixture(),
            &[("foo", "p", "Box<i32>"), ("foo", "q", "Option<Box<i32>>")],
        ),
    ];
    for (source, expected) in fixtures {
        let actual = simple_local_types(source);
        let expected = expected
            .iter()
            .map(|(path, name, ty)| ((*path).to_owned(), (*name).to_owned(), (*ty).to_owned()))
            .collect::<Vec<_>>();
        assert_eq!(actual, expected, "source: {source}");
    }
}

#[test]
fn skeleton_pointer_result_contains_no_cursor_variant() {
    for source in [
        scalar_reference_fixture(),
        array_pointer_fixture(),
        raw_pointer_fixture(),
        named_types_fixture(),
        tools_cursor_fixture(),
    ] {
        run_compiler_on_str(source, |tcx| {
            let decisions = initial_pointer_decisions(
                &pointer_replacer::Config::default(),
                PointerDecisionOptions {
                    assume_nonnegative_offsets: true,
                },
                tcx,
            );
            assert!(
                decisions
                    .signatures
                    .data
                    .values()
                    .flat_map(|decision| {
                        decision
                            .input_decs
                            .iter()
                            .copied()
                            .chain(std::iter::once(decision.output_dec))
                    })
                    .flatten()
                    .all(|kind| !matches!(kind, PtrKind::SliceCursor(_)))
            );
            assert!(
                decisions
                    .bindings
                    .values()
                    .all(|kind| !matches!(kind, PtrKind::SliceCursor(_)))
            );
        })
        .unwrap();
        let json = skeletons_to_json(&generate(source)).unwrap();
        assert!(!json.contains("SliceCursor"));
        assert!(!json.contains("slice_cursor"));
    }
}

fn optional_box_fixture() -> &'static str {
    "unsafe extern \"C\" { fn malloc(size: usize) -> *mut i32; } pub unsafe fn owned_id(mut p: *mut i32) -> *mut i32 { p } pub unsafe fn foo() -> *mut i32 { let p: *mut i32 = malloc(core::mem::size_of::<i32>()); *p = 7; let q: *mut i32 = owned_id(p); q }"
}

#[test]
fn selects_optional_boxes_at_local_call_boundaries() {
    let records = generate(optional_box_fixture());
    assert_eq!(
        function(&records, "owned_id").target_signature,
        "pub unsafe fn owned_id(mut p: Option<Box<i32>>) -> Option<Box<i32>>"
    );
    assert!(
        function(&records, "foo")
            .target_signature
            .ends_with("-> Option<Box<i32>>")
    );
    let skeleton = &function(&records, "foo").annotated_skeleton;
    assert!(skeleton.contains("let mut p: Box<i32>"));
    assert!(skeleton.contains("let mut q: Option<Box<i32>>"));
}

fn tools_cursor_fixture() -> &'static str {
    "pub unsafe fn read_at(p: *const i32, offset: isize) -> i32 { let nonnegative = offset.max(0); *p.offset(nonnegative) } pub unsafe fn caller(offset: isize) -> i32 { let values = [10i32, 20, 30, 40]; read_at(values.as_ptr(), offset) }"
}

#[test]
fn tools_mode_disables_conservative_slice_cursors_without_changing_crat_default() {
    let source = tools_cursor_fixture();
    let default_kind = run_compiler_on_str(source, |tcx| {
        let result = initial_pointer_decisions(
            &pointer_replacer::Config::default(),
            PointerDecisionOptions::default(),
            tcx,
        );
        let did = result
            .signatures
            .data
            .keys()
            .copied()
            .find(|did| tcx.item_name(did.to_def_id()) == Symbol::intern("read_at"))
            .unwrap();
        result.signatures.data[&did].input_decs[0].unwrap()
    })
    .unwrap();
    assert_eq!(default_kind, PtrKind::SliceCursor(false));
    let tools_kind = run_compiler_on_str(source, |tcx| {
        let result = initial_pointer_decisions(
            &pointer_replacer::Config::default(),
            PointerDecisionOptions {
                assume_nonnegative_offsets: true,
            },
            tcx,
        );
        assert!(
            result
                .bindings
                .values()
                .all(|kind| !matches!(kind, PtrKind::SliceCursor(_)))
        );
        let did = result
            .signatures
            .data
            .keys()
            .copied()
            .find(|did| tcx.item_name(did.to_def_id()) == Symbol::intern("read_at"))
            .unwrap();
        result.signatures.data[&did].input_decs[0].unwrap()
    })
    .unwrap();
    assert_eq!(tools_kind, PtrKind::Slice(false));
    let records = generate(source);
    assert_eq!(
        function(&records, "read_at").target_signature,
        "pub unsafe fn read_at(mut p: &[i32], mut offset: isize) -> i32"
    );
    assert!(
        function(&records, "read_at")
            .annotated_skeleton
            .contains("let mut nonnegative: isize")
    );
    assert!(
        function(&records, "caller")
            .annotated_skeleton
            .contains("let mut values: [i32; 4]")
    );
}

#[test]
fn comprehensive_fixture_emits_consistent_records() {
    let records = generate(comprehensive_fixture());
    assert_paths(
        &records,
        &[
            ("N", ItemKindName::Const),
            ("model::Point", ItemKindName::Struct),
            ("model::Bits", ItemKindName::Union),
            ("model::Mode", ItemKindName::Enum),
            ("model::PointPtr", ItemKindName::TyAlias),
            ("model::ORIGIN", ItemKindName::Static),
            ("model::read", ItemKindName::Fn),
            ("helper", ItemKindName::Fn),
        ],
    );
    assert_eq!(type_record(&records, "model::Mode").dependencies, [0]);
    assert_eq!(function(&records, "model::read").dependencies, [1, 7]);
    assert_eq!(function(&records, "helper").dependencies, [7]);
    assert!(
        function(&records, "model::read")
            .target_signature
            .contains("p: &Point")
    );
    assert_eq!(
        labels(&function(&records, "model::read").annotated_skeleton),
        [0, 1, 2, 3]
    );
    assert_eq!(
        labels(&function(&records, "helper").annotated_skeleton),
        [0, 1, 2, 3, 4, 5]
    );
}

#[test]
fn same_module_pointer_targets_supersede_crate_qualified_skeleton_oracles() {
    let records = generate(local_struct_demotion_fixture());
    assert_eq!(
        function(&records, "tree_print_helper").target_signature,
        "pub unsafe fn tree_print_helper(mut tree: &mut Tree, mut root_id: i32)"
    );
    let records = generate(comprehensive_fixture());
    assert!(
        function(&records, "model::read")
            .target_signature
            .contains("p: &Point")
    );
}

#[test]
fn existing_pointer_and_protocol_regressions_change_only_rendered_tools_types() {
    use crate::{
        ExpectedFunction, ReplacementItem, ReplacementRequest, ValidationRequest, replace_items,
        validate,
    };

    let tree = exact_a4_source("A4-SRC-TREE");
    let comprehensive = exact_a4_source("A4-SRC-COMPREHENSIVE");
    for source in [tree, comprehensive] {
        let direct = run_compiler_on_str(source, tools_pointer_decisions).unwrap();
        let through_generation = run_compiler_on_str(source, |tcx| {
            let decisions = tools_pointer_decisions(tcx);
            make_skeletons(source, tcx).unwrap();
            decisions
        })
        .unwrap();
        assert_eq!(direct, through_generation);
    }

    let tree_records = generate(tree);
    assert_paths(
        &tree_records,
        &[
            ("Tree", ItemKindName::Struct),
            ("tree_print_helper", ItemKindName::Fn),
            ("caller", ItemKindName::Fn),
        ],
    );
    let tree_function_record = tree_records
        .iter()
        .find(|record| record.path() == "tree_print_helper")
        .unwrap();
    let tree_function = function(&tree_records, "tree_print_helper");
    assert_eq!(
        tree_function.target_signature,
        "pub unsafe fn tree_print_helper(mut tree: &mut Tree, mut root_id: i32)"
    );
    assert_function_record_json_key_order(tree_function_record);
    let tree_json = skeletons_to_json(&tree_records).unwrap();
    assert!(tree_json.contains("&mut Tree"));
    assert!(!tree_json.contains("&mut crate::Tree"));

    let comprehensive_records = generate(comprehensive);
    assert_paths(
        &comprehensive_records,
        &[
            ("N", ItemKindName::Const),
            ("model::Point", ItemKindName::Struct),
            ("model::Bits", ItemKindName::Union),
            ("model::Mode", ItemKindName::Enum),
            ("model::PointPtr", ItemKindName::TyAlias),
            ("model::ORIGIN", ItemKindName::Static),
            ("model::read", ItemKindName::Fn),
            ("helper", ItemKindName::Fn),
        ],
    );
    let read_record = comprehensive_records
        .iter()
        .find(|record| record.path() == "model::read")
        .unwrap();
    assert_function_record_json_key_order(read_record);
    let read = function(&comprehensive_records, "model::read");
    assert!(read.target_signature.contains("p: &Point"));
    assert!(!read.target_signature.contains("crate::model::Point"));

    let rewritten_tree = run_compiler_on_str(tree, |tcx| {
        pointer_replacer::replace_local_borrows(&pointer_replacer::Config::default(), tcx).0
    })
    .unwrap();
    assert!(compact(&rewritten_tree).contains(&compact(
        "pub unsafe fn tree_print_helper(mut tree: *mut crate::Tree, root_id: i32)"
    )));
    let rewritten_comprehensive = run_compiler_on_str(comprehensive, |tcx| {
        pointer_replacer::replace_local_borrows(&pointer_replacer::Config::default(), tcx).0
    })
    .unwrap();
    assert!(
        rewritten_comprehensive.contains("crate::model::Point"),
        "ordinary rewriter unexpectedly adopted the tools-local Point spelling"
    );

    let expected = ExpectedFunction {
        id: tree_function.id,
        name: tree_function.name.clone(),
        skeleton: tree_function.annotated_skeleton.clone(),
        needs_transformation: tree_function.needs_transformation,
        statements_requiring_transformation: tree_function
            .statements_requiring_transformation
            .clone(),
    };
    let validation_request = ValidationRequest {
        schema_version: 1,
        expected_functions: vec![expected],
        transformation: tree_function.annotated_skeleton.clone(),
    };
    let validation_json = serde_json::to_string(&validation_request).unwrap();
    assert_eq!(
        serde_json::from_str::<serde_json::Value>(&validation_json).unwrap()["schema_version"],
        1
    );
    let validation = validate(&validation_request);
    assert!(validation.is_valid(), "{validation:?}");
    assert_eq!(
        serde_json::from_str::<serde_json::Value>(
            &crate::validation_response_to_json(&validation).unwrap()
        )
        .unwrap()["schema_version"],
        1
    );

    let replacement_request = ReplacementRequest {
        schema_version: 1,
        items: vec![ReplacementItem {
            id: tree_function.id,
            path: tree_function.path.clone(),
            name: tree_function.name.clone(),
            skeleton: tree_function.annotated_skeleton.clone(),
            needs_transformation: tree_function.needs_transformation,
            statements_requiring_transformation: tree_function
                .statements_requiring_transformation
                .clone(),
        }],
        transformation: tree_function.annotated_skeleton.clone(),
    };
    let replacement_json = serde_json::to_string(&replacement_request).unwrap();
    assert_eq!(
        crate::replacement_request_from_json(&replacement_json).unwrap(),
        replacement_request
    );
    assert_eq!(
        serde_json::from_str::<serde_json::Value>(&replacement_json).unwrap()["schema_version"],
        1
    );
    run_compiler_on_str(tree, |tcx| {
        replace_items(tree, &replacement_request, tcx).unwrap()
    })
    .unwrap();
}

#[test]
fn compound_pointees_and_inferred_pointer_locals_recurse() {
    fn assert_path<'a>(ty: &'a Ty, expected: &str) -> &'a rustc_ast::PathSegment {
        let TyKind::Path(None, path) = &ty.kind else {
            panic!(
                "expected path `{expected}`, got {}",
                pprust::ty_to_string(ty)
            )
        };
        let [segment] = &path.segments[..] else {
            panic!("expected one-segment path `{expected}`")
        };
        assert_eq!(segment.ident.to_string(), expected);
        segment
    }

    fn only_type_argument(segment: &rustc_ast::PathSegment) -> &Ty {
        let Some(GenericArgs::AngleBracketed(arguments)) = segment.args.as_deref() else {
            panic!("expected angle-bracketed arguments")
        };
        let [AngleBracketedArg::Arg(GenericArg::Type(ty))] = &arguments.args[..] else {
            panic!("expected exactly one type argument")
        };
        ty
    }

    fn assert_i32(ty: &Ty) {
        let segment = assert_path(ty, "i32");
        assert!(segment.args.is_none());
    }

    fn assert_const_i32_pointer(ty: &Ty) {
        let TyKind::Ptr(mut_ty) = &ty.kind else {
            panic!("expected raw pointer, got {}", pprust::ty_to_string(ty))
        };
        assert_eq!(mut_ty.mutbl, Mutability::Not);
        assert_i32(&mut_ty.ty);
    }

    fn assert_wrap_i32(ty: &Ty, wrap_name: &str) {
        let segment = assert_path(ty, wrap_name);
        assert_i32(only_type_argument(segment));
    }

    fn assert_callback_ast(ty: &Ty, expected_c_abi: bool) {
        let TyKind::BareFn(bare) = &ty.kind else {
            panic!(
                "expected bare function pointer, got {}",
                pprust::ty_to_string(ty)
            )
        };
        assert!(matches!(bare.safety, Safety::Unsafe(_)));
        match (expected_c_abi, bare.ext) {
            (false, Extern::None) => {}
            (true, Extern::Explicit(abi, _)) => {
                assert_eq!(abi.symbol_unescaped.as_str(), "C")
            }
            _ => panic!("unexpected function-pointer ABI: {:?}", bare.ext),
        }
        assert!(bare.generic_params.is_empty());
        let [input] = &bare.decl.inputs[..] else { panic!("expected exactly one callback input") };
        assert_const_i32_pointer(&input.ty);
        let FnRetTy::Ty(output) = &bare.decl.output else {
            panic!("expected explicit callback output")
        };
        assert_const_i32_pointer(output);
    }

    let compound = exact_a4_source("A4-SRC-COMPOUND");
    let records = generate(compound);
    assert!(
        function(&records, "consumer::mutate")
            .target_signature
            .contains("&mut (Alpha, [B; 2])")
    );
    let locals = simple_local_types(compound);
    assert!(locals.contains(&(
        "consumer::local".into(),
        "value".into(),
        "(Alpha, [B; 2])".into()
    )));
    assert!(locals.contains(&(
        "consumer::local".into(),
        "pointer".into(),
        "&mut (Alpha, [B; 2])".into()
    )));

    let direct = exact_a4_source("A4-SRC-DIRECT-HINTS");
    run_compiler_on_str(direct, |tcx| {
        let mut surface = utils::ast::parse_crate(direct.to_owned());
        let mut mapper = utils::ir::AstToHirMapper::new(tcx);
        mapper.map_crate_to_mod(&mut surface, tcx.hir_root_module(), false);
        let ast_to_hir = mapper.ast_to_hir;
        let item = surface
            .items
            .iter()
            .find(|item| {
                item.kind
                    .ident()
                    .is_some_and(|ident| ident.name.as_str() == "hint")
            })
            .unwrap();
        let def_id = ast_to_hir.global_map[&item.id];
        let ItemKind::Fn(box function) = &item.kind else { unreachable!() };
        let hint = function.sig.decl.inputs[0].ty.as_ref();
        let body = tcx.mir_drops_elaborated_and_const_checked(def_id).borrow();
        let original = body.local_decls[rustc_middle::mir::Local::from_usize(1)].ty;
        let speller = TypeSpeller::new(def_id, &ast_to_hir, tcx);
        assert_eq!(
            resolve_one_segment_type(def_id, "P", tcx),
            local_def_path("P", tcx).to_def_id()
        );
        let cases = [
            (PtrKind::Ref(false), "&P"),
            (PtrKind::Ref(true), "&mut P"),
            (PtrKind::OptRef(false), "Option<&P>"),
            (PtrKind::OptRef(true), "Option<&mut P>"),
            (PtrKind::Box, "Box<P>"),
            (PtrKind::OptBox, "Option<Box<P>>"),
            (PtrKind::Raw(false), "*const P"),
            (PtrKind::Raw(true), "*mut P"),
            (PtrKind::BoxedSlice, "Box<[P]>"),
            (PtrKind::OptBoxedSlice, "Option<Box<[P]>>"),
            (PtrKind::Slice(false), "&[P]"),
            (PtrKind::Slice(true), "&mut [P]"),
            (
                PtrKind::SliceCursor(false),
                "crate::slice_cursor::SliceCursor<'_, P>",
            ),
            (
                PtrKind::SliceCursor(true),
                "crate::slice_cursor::SliceCursorMut<'_, P>",
            ),
        ];
        for (kind, expected) in cases {
            let actual = target_type(
                original,
                kind,
                None,
                Some(hint),
                &speller,
                "hint",
                "parameter `pointer`",
            )
            .unwrap();
            assert_eq!(pprust::ty_to_string(&actual), expected);
            struct PFinder {
                count: usize,
            }
            impl<'ast> rustc_ast::visit::Visitor<'ast> for PFinder {
                fn visit_ty(&mut self, ty: &'ast Ty) {
                    if let TyKind::Path(None, path) = &ty.kind
                        && let [segment] = &path.segments[..]
                        && segment.ident.to_string() == "P"
                    {
                        self.count += 1;
                    }
                    rustc_ast::visit::walk_ty(self, ty);
                }
            }
            let mut finder = PFinder { count: 0 };
            finder.visit_ty(&actual);
            assert_eq!(
                finder.count, 1,
                "{kind:?} did not retain exactly one cloned nominal P node"
            );
        }
    })
    .unwrap();

    let recursive = exact_a4_source("A4-SRC-RECURSIVE-TYPES");
    run_compiler_on_str(recursive, |tcx| {
        let grammar = local_def("grammar", tcx);
        let signature = tcx.fn_sig(grammar).instantiate_identity().skip_binder();
        let inputs = signature.inputs();
        let mut surface = utils::ast::parse_crate(recursive.to_owned());
        let mut mapper = utils::ir::AstToHirMapper::new(tcx);
        mapper.map_crate_to_mod(&mut surface, tcx.hir_root_module(), false);
        let ast_to_hir = mapper.ast_to_hir;
        let speller = TypeSpeller::new(grammar, &ast_to_hir, tcx);
        let grammar_item = surface
            .items
            .iter()
            .find(|item| {
                item.kind
                    .ident()
                    .is_some_and(|ident| ident.name.as_str() == "grammar")
            })
            .unwrap();
        let ItemKind::Fn(box grammar_function) = &grammar_item.kind else { unreachable!() };
        let mut source_array = (*grammar_function.sig.decl.inputs[1].ty).clone();
        speller.shorten_source_type(&mut source_array);
        assert_eq!(pprust::ty_to_string(&source_array), "[Wrap<i32>; WIDTH]");
        let TyKind::Array(source_element, source_length) = &source_array.kind else {
            panic!("source array syntax was not retained")
        };
        assert_wrap_i32(source_element, "Wrap");
        let ExprKind::Path(None, source_length_path) = &source_length.value.kind else {
            panic!("source array length is not the named path WIDTH")
        };
        assert_eq!(
            source_length_path
                .segments
                .last()
                .unwrap()
                .ident
                .to_string(),
            "WIDTH"
        );

        let singleton = speller.render_semantic_type(inputs[0]).unwrap();
        let TyKind::Tup(singleton_elements) = &singleton.kind else {
            panic!("singleton did not render as a tuple")
        };
        let [wrapped_pair] = &singleton_elements[..] else {
            panic!("singleton tuple did not retain exactly one component")
        };
        let wrap_segment = assert_path(wrapped_pair, "Wrap");
        let TyKind::Tup(pair) = &only_type_argument(wrap_segment).kind else {
            panic!("Wrap argument did not retain the nested tuple")
        };
        let [raw, reference] = &pair[..] else {
            panic!("nested tuple did not retain its two components")
        };
        assert_const_i32_pointer(raw);
        let TyKind::Ref(Some(lifetime), referenced) = &reference.kind else {
            panic!("nested reference did not retain its explicit lifetime")
        };
        assert_eq!(lifetime.ident.name.as_str(), "'static");
        assert_eq!(referenced.mutbl, Mutability::Not);
        let TyKind::Slice(slice_element) = &referenced.ty.kind else {
            panic!("nested reference did not retain its slice")
        };
        assert_i32(slice_element);
        assert_eq!(
            pprust::ty_to_string(&singleton),
            "(Wrap<(*const i32, &'static [i32])>,)",
            "the structurally singleton tuple must retain its required comma"
        );

        let array = speller.render_semantic_type(inputs[1]).unwrap();
        let TyKind::Array(array_element, array_length) = &array.kind else {
            panic!("semantic array did not retain array structure")
        };
        assert_wrap_i32(array_element, "Wrap");
        assert_eq!(pprust::expr_to_string(&array_length.value), "2");

        let callback = speller.render_semantic_type(inputs[2]).unwrap();
        assert_callback_ast(&callback, false);
        let c_callback = speller.render_semantic_type(inputs[3]).unwrap();
        assert_callback_ast(&c_callback, true);

        let wrap = local_def("Wrap", tcx).to_def_id();
        let mut selected = vec![];
        let mut rendered_with_hook = String::new();
        let mut nominal_hook = |def_id| {
            selected.push(def_id);
            Ok(if def_id == wrap {
                "HookWrap".to_owned()
            } else {
                tcx.def_path_str(def_id)
            })
        };
        utils::ir::format_mir_ty_with_policy(
            &mut rendered_with_hook,
            inputs[1],
            tcx,
            &mut nominal_hook,
            utils::ir::MirTypeFormatPolicy::SourceValid,
        )
        .unwrap();
        assert_eq!(rendered_with_hook, "[HookWrap<i32>; 2]");
        assert_eq!(selected, [wrap]);
        let hooked = utils::ast::try_parse_ty(rendered_with_hook).unwrap();
        let TyKind::Array(hooked_element, _) = &hooked.kind else {
            panic!("nominal-hook result lost array structure")
        };
        assert_wrap_i32(hooked_element, "HookWrap");

        let higher = local_def("higher_ranked", tcx);
        let higher_sig = tcx.fn_sig(higher).instantiate_identity().skip_binder();
        let higher_error = target_type(
            higher_sig.inputs()[0],
            PtrKind::Raw(false),
            None,
            None,
            &speller,
            "higher_ranked",
            "parameter `callback`",
        )
        .unwrap_err();
        assert_eq!(higher_error.kind, GenerationErrorKind::TypeSpelling);
        assert_eq!(higher_error.function_path, "higher_ranked");
        assert!(higher_error.message.contains("parameter `callback`"));
        assert!(
            higher_error
                .message
                .contains("higher-ranked function pointer binder")
        );

        assert_eq!(
            utils::ir::mir_ty_to_string(inputs[0], tcx),
            "(crate::Wrap<(*const i32, &[i32])>)"
        );
        assert_eq!(
            utils::ir::mir_ty_to_string(inputs[1], tcx),
            "[crate::Wrap<i32>; 2]"
        );
        assert_eq!(
            utils::ir::mir_ty_to_string(inputs[2], tcx),
            "unsafe fn(*const i32) -> *const i32"
        );
        assert_eq!(
            utils::ir::mir_ty_to_string(inputs[3], tcx),
            "unsafe extern \"C\" fn(*const i32) -> *const i32"
        );

        assert_unsupported_semantic_type(
            tcx.type_of(grammar).instantiate_identity(),
            "function item type",
            tcx,
        );
        let wrap_field = tcx
            .adt_def(local_def("Wrap", tcx))
            .non_enum_variant()
            .fields
            .iter()
            .next()
            .unwrap()
            .did;
        assert_unsupported_semantic_type(
            tcx.type_of(wrap_field).instantiate_identity(),
            "type parameter",
            tcx,
        );
        assert_unsupported_semantic_type(
            higher_sig.inputs()[0],
            "higher-ranked function pointer binder",
            tcx,
        );

        let mut invalid = String::new();
        let mut invalid_nominal = |_| Ok("crate::<".to_owned());
        utils::ir::format_mir_ty_with_policy(
            &mut invalid,
            inputs[1],
            tcx,
            &mut invalid_nominal,
            utils::ir::MirTypeFormatPolicy::SourceValid,
        )
        .unwrap();
        assert!(utils::ast::try_parse_ty(invalid).is_err());
    })
    .unwrap();

    let erased_generic_region = r#"
        pub struct Borrowed<'a>(pub &'a i32);
        pub unsafe fn inferred(input: &i32) -> i32 {
            let value = Borrowed(input);
            *value.0
        }
    "#;
    let locals = simple_local_types(erased_generic_region);
    assert!(locals.contains(&("inferred".into(), "value".into(), "Borrowed<'_>".into())));
}

#[test]
fn ordinary_pointer_rewriter_and_decisions_are_unchanged() {
    for source in [
        exact_a4_source("A4-SRC-TREE"),
        exact_a4_source("A4-SRC-POINTERS"),
        exact_a4_source("A4-SRC-COMPOUND"),
    ] {
        let direct = run_compiler_on_str(source, tools_pointer_decisions).unwrap();
        let through_generation = run_compiler_on_str(source, |tcx| {
            let decisions = tools_pointer_decisions(tcx);
            make_skeletons(source, tcx).unwrap();
            decisions
        })
        .unwrap();
        assert_eq!(direct, through_generation);
    }

    let tree = exact_a4_source("A4-SRC-TREE");
    let records = generate(tree);
    assert_eq!(
        function(&records, "tree_print_helper").target_signature,
        "pub unsafe fn tree_print_helper(mut tree: &mut Tree, mut root_id: i32)"
    );
    let rewritten = run_compiler_on_str(tree, |tcx| {
        pointer_replacer::replace_local_borrows(&pointer_replacer::Config::default(), tcx).0
    })
    .unwrap();
    assert!(compact(&rewritten).contains(&compact(
        "pub unsafe fn tree_print_helper(mut tree: *mut crate::Tree, root_id: i32)"
    )));
}

#[test]
fn generated_local_name_validates_replaces_and_compiles_in_original_module() {
    use crate::{
        ExpectedFunction, ReplacementItem, ReplacementRequest, ValidationRequest,
        normalize_target_safety, replace_items, validate,
    };

    let normalized = normalize_target_safety(exact_a4_source("A4-SRC-MOTIVATING")).unwrap();
    let replaced = run_compiler_on_str(&normalized, |tcx| {
        let records = make_skeletons(&normalized, tcx).unwrap();
        let record = function(&records, "src::lib::cb_remove_gamma_rgb");
        assert_eq!(record.path, "src::lib::cb_remove_gamma_rgb");
        assert_eq!(
            record.target_signature,
            "pub unsafe fn cb_remove_gamma_rgb(mut rgb: cb_rgb) -> cb_rgb"
        );
        assert_eq!(record.statements_requiring_transformation, [0, 1]);
        let generated_labels = labels(&record.annotated_skeleton);
        assert_eq!(generated_labels, [0, 1, 2, 3]);
        let [result_label, init_label, init_tail_label, result_tail_label] = generated_labels[..]
        else {
            unreachable!()
        };
        let transformation = r#"
            __SIGNATURE__ {
                #[proctor(__RESULT_LABEL__)]
                let mut result: cb_rgb = {
                    #[proctor(__INIT_LABEL__)]
                    let mut init: cb_rgb = cb_rgb {
                        r: crate::transform(rgb.r as f64) as f32,
                        g: crate::transform(rgb.g as f64) as f32,
                        b: crate::transform(rgb.b as f64) as f32,
                    };
                    #[proctor(__INIT_TAIL_LABEL__)]
                    init
                };
                #[proctor(__RESULT_TAIL_LABEL__)]
                result
            }
        "#
        .replace("__SIGNATURE__", &record.target_signature)
        .replace("__RESULT_LABEL__", &result_label.to_string())
        .replace("__INIT_LABEL__", &init_label.to_string())
        .replace("__INIT_TAIL_LABEL__", &init_tail_label.to_string())
        .replace("__RESULT_TAIL_LABEL__", &result_tail_label.to_string());
        let validation = validate(&ValidationRequest {
            schema_version: 1,
            expected_functions: vec![ExpectedFunction {
                id: record.id,
                name: record.name.clone(),
                skeleton: record.annotated_skeleton.clone(),
                needs_transformation: record.needs_transformation,
                statements_requiring_transformation: record
                    .statements_requiring_transformation
                    .clone(),
            }],
            transformation: transformation.clone(),
        });
        assert!(validation.is_valid(), "{validation:?}");
        assert!(
            crate::validation_response_to_json(&validation)
                .unwrap()
                .starts_with("{\n  \"schema_version\": 1,\n  \"status\": \"valid\"")
        );
        let contrast = transformation.replace(
            "let mut init: cb_rgb",
            "let mut init: crate::src::lib::cb_rgb",
        );
        let contrast = validate(&ValidationRequest {
            schema_version: 1,
            expected_functions: vec![ExpectedFunction {
                id: record.id,
                name: record.name.clone(),
                skeleton: record.annotated_skeleton.clone(),
                needs_transformation: record.needs_transformation,
                statements_requiring_transformation: record
                    .statements_requiring_transformation
                    .clone(),
            }],
            transformation: contrast,
        });
        assert!(
            crate::validation_response_to_json(&contrast)
                .unwrap()
                .contains("\"code\": \"local_type_mismatch\""),
            "{contrast:?}"
        );
        replace_items(
            &normalized,
            &ReplacementRequest {
                schema_version: 1,
                items: vec![ReplacementItem {
                    id: record.id,
                    path: record.path.clone(),
                    name: record.name.clone(),
                    skeleton: record.annotated_skeleton.clone(),
                    needs_transformation: record.needs_transformation,
                    statements_requiring_transformation: record
                        .statements_requiring_transformation
                        .clone(),
                }],
                transformation,
            },
            tcx,
        )
        .unwrap()
    })
    .unwrap();
    assert!(replaced.contains("let mut init: cb_rgb"));
    assert!(replaced.contains("pub unsafe fn cb_remove_gamma_rgb"));
    assert!(!replaced.contains("#[proctor("));
    assert!(!replaced.contains("__proctor_wrapper"));
    struct ReplacementFinder {
        public_unsafe_target_count: usize,
    }
    impl<'ast> rustc_ast::visit::Visitor<'ast> for ReplacementFinder {
        fn visit_item(&mut self, item: &'ast Item) {
            if item
                .kind
                .ident()
                .is_some_and(|ident| ident.to_string() == "cb_remove_gamma_rgb")
            {
                assert!(matches!(item.vis.kind, rustc_ast::VisibilityKind::Public));
                let ItemKind::Fn(box function) = &item.kind else {
                    panic!("replacement target is not a function")
                };
                assert!(matches!(function.sig.header.safety, Safety::Unsafe(_)));
                self.public_unsafe_target_count += 1;
            }
            rustc_ast::visit::walk_item(self, item);
        }
    }
    run_compiler_on_str(&replaced, |_| {
        let mut replacement_finder = ReplacementFinder {
            public_unsafe_target_count: 0,
        };
        replacement_finder.visit_crate(&utils::ast::parse_crate(replaced.clone()));
        assert_eq!(replacement_finder.public_unsafe_target_count, 1);
    })
    .unwrap();
}

#[test]
fn source_and_target_parameters_and_simple_locals_are_mutable() {
    let source = r#"pub unsafe fn f(input: i32, mut existing: i32) -> i32 {
    let value = input;
    let mut total: i32 = existing;
    total += value;
    total
}"#;
    let record = function(&generate(source), "f").clone();
    assert_skeleton(
        source,
        "f",
        r#"pub unsafe fn f(mut input: i32, mut existing: i32) -> i32 {
    let mut value: i32 = input;
    let mut total: i32 = existing;
    total += value;
    total
}"#,
    );
    assert_eq!(
        record.source_signature,
        "pub unsafe fn f(mut input: i32, mut existing: i32) -> i32"
    );
    assert_eq!(record.source_signature, record.target_signature);
    assert!(record.annotated_source.contains("let mut value = input;"));
    assert!(
        record
            .annotated_source
            .contains("let mut total: i32 = existing;")
    );
}

#[test]
fn wildcards_remain_wildcards() {
    let source = r#"pub unsafe fn f(pair: (i32, i32)) {
    let (_, value) = pair;
    let _ = value;
}"#;
    let record = function(&generate(source), "f").clone();
    assert_skeleton(
        source,
        "f",
        r#"pub unsafe fn f(mut pair: (i32, i32)) {
    let (_, mut value) = pair;
    let _ = value;
}"#,
    );
    assert_eq!(
        record.source_signature,
        "pub unsafe fn f(mut pair: (i32, i32))"
    );
    assert_eq!(record.source_signature, record.target_signature);
    assert!(
        record
            .annotated_source
            .contains("let (_, mut value) = pair;")
    );
    assert!(record.annotated_source.contains("let _ = value;"));
}

#[test]
fn non_ref_bindings_are_normalized_and_reference_modes_are_preserved() {
    let source = r#"enum E { Pair(i32, i32), Struct { x: i32 }, Unit }
enum Choice { Left(i32), Right(i32) }
pub unsafe fn f(
    pair: (i32, i32),
    mut opt: Option<(i32, i32)>,
    values: [(i32, i32); 1],
    value: E,
    choice: Choice,
) {
    let ref borrowed = pair;
    let _ = borrowed;
    let whole @ (a, b) = pair;
    let Some((c, d)): Option<(i32, i32)> = opt else { return; };
    if let Some((e, f)) = opt { let _ = e + f; }
    while let Some((g, h)) = opt { opt = None; let _ = g + h; }
    for (i, j) in values { let _ = i + j; }
    match value {
        E::Pair(k, l) => { let _ = k + l; }
        E::Struct { x: m } => { let _ = m; }
        E::Unit => {}
    }
    match choice {
        Choice::Left(n) | Choice::Right(n) => { let _ = n; }
    }
    let _ = (whole, a, b, c, d);
}"#;
    let records = generate(source);
    let record = function(&records, "f");
    for rendering in [&record.annotated_source, &record.annotated_skeleton] {
        for fragment in [
            "mut pair: (i32, i32)",
            "mut opt: Option<(i32, i32)>",
            "mut values: [(i32, i32); 1]",
            "mut value: E",
            "mut choice: Choice",
            "let ref borrowed",
            "let mut whole @ (mut a, mut b)",
            "Some((mut c, mut d))",
            "Some((mut e, mut f))",
            "Some((mut g, mut h))",
            "for (mut i, mut j)",
            "E::Pair(mut k, mut l)",
            "x: mut m",
            "Choice::Left(mut n) | Choice::Right(mut n)",
        ] {
            assert!(
                rendering.contains(fragment),
                "missing `{fragment}` in {rendering}"
            );
        }
        assert!(!rendering.contains("let ref mut borrowed"));
    }

    let ref_mut = generate(
        "pub unsafe fn ref_mut_source(mut value: i32) { let ref mut borrowed = value; let _ = borrowed; }",
    );
    let ref_mut = function(&ref_mut, "ref_mut_source");
    assert!(ref_mut.annotated_source.contains("let ref mut borrowed"));
    assert!(ref_mut.annotated_skeleton.contains("let ref mut borrowed"));
}

#[test]
fn safe_source_functions_get_unsafe_target_headers() {
    let records = generate(
        "pub fn safe(input: i32) -> i32 { let value = input; value } pub unsafe fn already_unsafe(input: i32) -> i32 { input }",
    );
    let safe = function(&records, "safe");
    assert_eq!(safe.source_signature, "pub fn safe(mut input: i32) -> i32");
    assert_eq!(
        safe.target_signature,
        "pub unsafe fn safe(mut input: i32) -> i32"
    );
    assert!(safe.annotated_source.starts_with("pub fn safe"));
    assert!(safe.annotated_source.contains("let mut value = input;"));
    assert!(safe.annotated_skeleton.starts_with("pub unsafe fn safe"));
    assert!(
        safe.annotated_skeleton
            .contains("let mut value: i32 = input;")
    );
    assert_eq!(
        function(&records, "already_unsafe").source_signature,
        "pub unsafe fn already_unsafe(mut input: i32) -> i32"
    );
    assert_eq!(
        function(&records, "already_unsafe").target_signature,
        "pub unsafe fn already_unsafe(mut input: i32) -> i32"
    );
}

#[test]
fn every_free_function_named_main_is_omitted_without_body_inspection() {
    let records = generate(
        r#"pub fn main() { let ignored = 1; core::mem::drop(ignored); }
unsafe fn main_0() -> core::ffi::c_int { 0 }
mod nested {
    pub fn main() { panic!("also omitted"); }
    pub unsafe fn helper() -> i32 { 1 }
}
mod raw {
    pub fn r#main() {}
    pub unsafe fn helper() -> i32 { 2 }
}"#,
    );
    assert_paths(
        &records,
        &[
            ("main_0", ItemKindName::Fn),
            ("nested::helper", ItemKindName::Fn),
            ("raw::helper", ItemKindName::Fn),
        ],
    );
}

#[test]
fn supported_main_0_forms_are_generated_with_the_fixed_argv_override() {
    let zero = generate(
        "unsafe fn main_0() -> core::ffi::c_int { 0 } pub fn main() { unsafe { ::std::process::exit(main_0() as i32) } }",
    );
    assert_eq!(zero.len(), 1);
    assert_eq!(
        function(&zero, "main_0").target_signature,
        "unsafe fn main_0() -> core::ffi::c_int"
    );

    let source = r#"unsafe fn main_0(
    mut argc: core::ffi::c_int,
    mut argv: *mut *mut core::ffi::c_char,
) -> core::ffi::c_int {
    if argc > 0 { **argv as core::ffi::c_int } else { 0 }
}
pub fn main() {
    let mut command_line_args: Vec<*mut core::ffi::c_char> = Vec::new();
    for arg in ::std::env::args() {
        command_line_args.push(::std::ffi::CString::new(arg).unwrap().into_raw());
    }
    command_line_args.push(::core::ptr::null_mut());
    unsafe {
        ::std::process::exit(main_0(
            (command_line_args.len() - 1) as core::ffi::c_int,
            command_line_args.as_mut_ptr() as *mut *mut core::ffi::c_char,
        ) as i32)
    }
}"#;
    let records = generate(source);
    assert_eq!(records.len(), 1);
    let main_0 = function(&records, "main_0");
    assert_eq!(
        main_0.source_signature,
        "unsafe fn main_0(mut argc: core::ffi::c_int,\nmut argv: *mut *mut core::ffi::c_char) -> core::ffi::c_int"
    );
    assert_eq!(
        main_0.target_signature,
        "unsafe fn main_0(mut argc: core::ffi::c_int, mut argv: &mut [&mut [i8]])\n-> core::ffi::c_int"
    );

    let parenthesized = generate(
        r#"unsafe fn main_0(
    argc: (core::ffi::c_int),
    argv: (*mut *mut core::ffi::c_char),
) -> (core::ffi::c_int) {
    0
}"#,
    );
    assert!(
        function(&parenthesized, "main_0")
            .target_signature
            .contains("mut argv: &mut [&mut [i8]]")
    );

    let arity_only = generate(
        r#"unsafe fn main_0(first: usize, second: *const u8) -> bool {
            let _ = (first, second);
            false
        }"#,
    );
    let target = &function(&arity_only, "main_0").target_signature;
    assert!(target.contains("mut first: usize"));
    assert!(target.contains("mut second: &mut [&mut [i8]]"));
    assert!(target.contains("-> bool"));
}

#[test]
fn generation_is_deterministic_across_compiler_runs() {
    let first = generate(comprehensive_fixture());
    let second = generate(comprehensive_fixture());
    assert_eq!(first, second);
    assert_eq!(
        skeletons_to_json(&first).unwrap(),
        skeletons_to_json(&second).unwrap()
    );
}

#[test]
fn record_paths_and_dependency_ids_are_self_consistent() {
    let records = generate(
        "mod a { pub struct T; pub const C: i32 = 1; pub unsafe fn make(_value: T) -> i32 { C } } mod b { pub struct T; pub unsafe fn call(x: crate::a::T) -> i32 { crate::a::make(x) } } pub unsafe fn root(x: a::T, _other: b::T) -> i32 { b::call(x) }",
    );
    assert_paths(
        &records,
        &[
            ("a::T", ItemKindName::Struct),
            ("a::C", ItemKindName::Const),
            ("a::make", ItemKindName::Fn),
            ("b::T", ItemKindName::Struct),
            ("b::call", ItemKindName::Fn),
            ("root", ItemKindName::Fn),
        ],
    );
    assert_eq!(function(&records, "a::make").dependencies, [0, 1]);
    assert_eq!(function(&records, "b::call").dependencies, [0, 2]);
    assert_eq!(function(&records, "root").dependencies, [0, 3, 4]);
    assert!(
        records
            .iter()
            .flat_map(ItemRecord::dependencies)
            .all(|id| *id < records.len() as u64)
    );
}

#[test]
fn empty_statement_error_prevents_partial_output() {
    let error = generate_error(
        "pub unsafe fn valid() -> i32 { 1 } pub unsafe fn invalid(flag: bool) { if flag { ; } }",
    );
    assert_eq!(error.kind, GenerationErrorKind::EmptyStatement);
    assert_eq!(error.function_path, "invalid");
}

#[test]
fn existing_function_records_and_helpers_adopt_the_final_shape() {
    let source = r#"pub unsafe fn scalar(value: i32) -> i32 {
    value + 1
}"#;
    let records = generate(source);
    assert_eq!(
        skeletons_to_json(&records).unwrap(),
        r#"[
  {
    "id": 0,
    "path": "scalar",
    "kind": "Fn",
    "name": "scalar",
    "annotated_source": "pub unsafe fn scalar(mut value: i32) -> i32 {\n    #[proctor(0)]\n    (value + 1)\n}",
    "annotated_skeleton": "pub unsafe fn scalar(mut value: i32) -> i32 {\n    #[proctor(0)]\n    (value + 1)\n}",
    "source_signature": "pub unsafe fn scalar(mut value: i32) -> i32",
    "target_signature": "pub unsafe fn scalar(mut value: i32) -> i32",
    "needs_transformation": false,
    "statements_requiring_transformation": [],
    "foreign_function_names": [],
    "signature_dependencies": [],
    "dependencies": []
  }
]"#
    );
}

#[test]
fn collects_per_function_names_sorted_deduplicated_and_resolved() {
    let records = generate(
        r#"#![feature(extern_types)]

unsafe extern "C" {
    fn strlen(text: *const core::ffi::c_char) -> usize;
    fn free(pointer: *mut core::ffi::c_void);
    fn transitive_foreign(value: i32) -> i32;
    fn unused_foreign(value: i32) -> i32;
    static FOREIGN_COUNTER: i32;
    type ForeignOpaque;
}

use strlen as c_strlen;

pub unsafe extern "C" fn local_abi(value: i32) -> i32 {
    transitive_foreign(value)
}

pub mod parser {
    pub unsafe fn scan(
        pointer: *mut core::ffi::c_void,
        text: *const core::ffi::c_char,
    ) -> usize {
        crate::free(pointer);
        let first = crate::c_strlen(text);
        let second = crate::strlen(text);
        let _ = crate::FOREIGN_COUNTER;
        let _: Option<*mut crate::ForeignOpaque> = None;
        let _ = crate::local_abi(first as i32);
        first + second + core::mem::size_of::<usize>()
    }

    pub unsafe fn release(pointer: *mut core::ffi::c_void) {
        crate::free(pointer);
        crate::free(pointer);
    }

    pub unsafe fn scalar(value: i32) -> i32 {
        crate::local_abi(value)
    }
}"#,
    );

    assert_eq!(
        function(&records, "local_abi").foreign_function_names,
        ["transitive_foreign"]
    );
    assert_eq!(
        function(&records, "parser::scan").foreign_function_names,
        ["free", "strlen"]
    );
    assert_eq!(
        function(&records, "parser::release").foreign_function_names,
        ["free"]
    );
    assert!(
        function(&records, "parser::scalar")
            .foreign_function_names
            .is_empty()
    );

    assert!(function(&records, "local_abi").dependencies.is_empty());
    assert_eq!(function(&records, "parser::scan").dependencies, [0]);
    assert!(
        function(&records, "parser::release")
            .dependencies
            .is_empty()
    );
    assert_eq!(function(&records, "parser::scalar").dependencies, [0]);
}

#[test]
fn handles_link_name_callable_reference_and_dependency_metadata() {
    let records = generate(
        r#"unsafe extern "C" {
    #[link_name = "strlen"]
    fn c_strlen(text: *const core::ffi::c_char) -> usize;
}

pub unsafe fn length(text: *const core::ffi::c_char) -> usize {
    c_strlen(text)
}

pub unsafe fn hold_callable() {
    let callable = c_strlen;
    let _ = callable;
}"#,
    );
    assert_eq!(
        function(&records, "length").foreign_function_names,
        ["c_strlen"]
    );
    assert_eq!(
        function(&records, "hold_callable").foreign_function_names,
        ["c_strlen"]
    );

    let dependency_records = generate(
        r#"extern crate libc;

pub unsafe fn dependency_free(pointer: *mut libc::c_void) {
    libc::free(pointer);
}"#,
    );
    assert_eq!(
        function(&dependency_records, "dependency_free").foreign_function_names,
        ["free"]
    );
}

#[test]
fn amendment_2_preserves_scalar_statements_and_metadata() {
    let source = r#"
pub unsafe fn scalar(mut x: i32, y: i32, z: i32) -> i32 {
    let sum = y + z;
    x = sum * 2;
    return x;
}
"#;
    let records = generate(source);
    let function = function(&records, "scalar");
    assert!(!function.needs_transformation);
    assert!(function.statements_requiring_transformation.is_empty());
    let skeleton = compact(&function.annotated_skeleton);
    assert!(skeleton.contains("y + z"));
    assert!(skeleton.contains("sum * 2"));
    assert!(skeleton.contains("return x"));
    assert!(!skeleton.contains("todo!"));
}

#[test]
fn amendment_2_mixed_control_has_recursive_parent_disposition() {
    let source = r#"
pub unsafe fn mixed(mut p: *mut i32, flag: bool, y: i32, z: i32) -> i32 {
    if flag {
        let sum = y + z;
        *p = sum;
    } else {
        let difference = y - z;
        return difference;
    }
    return y + z;
}
"#;
    let records = generate(source);
    let function = function(&records, "mixed");
    assert!(function.needs_transformation);
    assert_eq!(function.statements_requiring_transformation, [0, 2]);
    let skeleton = compact(&function.annotated_skeleton);
    assert!(skeleton.contains("if todo!()"));
    assert!(skeleton.contains("y + z"));
    assert!(skeleton.contains("y - z"));
    assert!(skeleton.contains("return difference"));
}

#[test]
fn amendment_2_callable_policy_is_conservative() {
    let source = r#"
pub fn local(value: i32) -> i32 { value + 1 }
pub unsafe fn caller(values: &[i32], left: i32, right: i32) -> i32 {
    let a = local(left);
    let b = std::cmp::max(a, right);
    let d = values.len() as i32;
    let e = values[0];
    b + d + e
}
"#;
    let records = generate(source);
    let caller = function(&records, "caller");
    assert_eq!(
        caller.statements_requiring_transformation,
        Vec::<u32>::new()
    );
}

#[test]
fn amendment_2_unsafe_nonlocal_calls_macros_and_raw_pointers_transform() {
    let source = r#"
pub unsafe fn cases(values: &[i32], pointer: *mut i32, value: i32) -> i32 {
    let unchecked = *values.get_unchecked(0);
    println!("{value}");
    let is_null = pointer.is_null();
    let scalar = value + 1;
    scalar + unchecked + is_null as i32
}
"#;
    let records = generate(source);
    let function = function(&records, "cases");
    assert_eq!(function.statements_requiring_transformation, [0, 1, 2]);
}

#[test]
fn amendment_2_opens_local_adts_but_not_external_representation() {
    let source = r#"
pub struct Leaf { pub pointer: *mut i32 }
pub struct Middle { pub leaf: Leaf }
pub unsafe fn values(
    mut local: Middle,
    other_local: Middle,
    mut integers: Vec<i32>,
    other_integers: Vec<i32>,
    mut pointers: Vec<*mut i32>,
    other_pointers: Vec<*mut i32>,
) {
    local = other_local;
    integers = other_integers;
    pointers = other_pointers;
}
"#;
    let records = generate(source);
    let function = function(&records, "values");
    assert_eq!(function.statements_requiring_transformation, [0, 2]);
    assert!(compact(&function.annotated_skeleton).contains("other_integers"));
}

#[test]
fn amendment_2_restricted_conditionals_preserve_or_stay_opaque() {
    let source = r#"
pub unsafe fn conditional(mut x: i32, flag: bool, pointer: *mut i32) -> i32 {
    x = 1 + if flag { 2 } else { 3 };
    x = 1 + if flag { *pointer } else { 3 };
    x
}
"#;
    let records = generate(source);
    let function = function(&records, "conditional");
    assert_eq!(function.statements_requiring_transformation, [1]);
    let skeleton = compact(&function.annotated_skeleton);
    assert!(skeleton.contains("1 + if flag"));
    assert_eq!(skeleton.matches("todo!()").count(), 1);
}

#[test]
fn amendment_2_future_field_change_marks_containing_values_sensitive() {
    let source = r#"
#[derive(Clone, Copy)]
pub struct FutureField { pub value: i32 }
pub unsafe fn move_future(mut left: FutureField, right: FutureField) -> i32 {
    left = right;
    left.value + right.value
}
"#;
    let ordinary = generate(source);
    assert!(
        function(&ordinary, "move_future")
            .statements_requiring_transformation
            .is_empty()
    );
    let changed = run_compiler_on_str(source, |tcx| {
        let item = tcx
            .hir_node_by_def_id(local_def("FutureField", tcx))
            .expect_item();
        let hir::ItemKind::Struct(_, _, variant) = item.kind else { unreachable!() };
        let mut overrides = PreservationDecisionOverrides::default();
        overrides
            .changed_fields
            .insert(variant.fields()[0].def_id.to_def_id());
        make_skeletons_with_preservation_overrides(source, tcx, &overrides).unwrap()
    })
    .unwrap();
    assert_eq!(
        function(&changed, "move_future").statements_requiring_transformation,
        [0, 1]
    );
}

#[test]
fn amendment_2_changed_local_signature_forces_call_transformation() {
    let source = r#"
pub unsafe fn scalar_callee(value: i32) -> i32 { value + 1 }
pub unsafe fn scalar_caller(value: i32) -> i32 { scalar_callee(value) }
"#;
    assert!(
        function(&generate(source), "scalar_caller")
            .statements_requiring_transformation
            .is_empty()
    );
    let changed = run_compiler_on_str(source, |tcx| {
        let mut overrides = PreservationDecisionOverrides::default();
        overrides
            .changed_local_signatures
            .insert(local_def("scalar_callee", tcx));
        make_skeletons_with_preservation_overrides(source, tcx, &overrides).unwrap()
    })
    .unwrap();
    assert_eq!(
        function(&changed, "scalar_caller").statements_requiring_transformation,
        [0]
    );
}

#[test]
fn amendment_2_missing_ast_mapping_and_changed_binding_decision_are_conservative() {
    let scalar_source = r#"
pub unsafe fn scalar(y: i32, z: i32) -> i32 {
    let sum = y + z;
    sum
}
"#;
    run_compiler_on_str(scalar_source, |tcx| {
        struct YExpression {
            id: Option<NodeId>,
        }

        impl<'ast> rustc_ast::visit::Visitor<'ast> for YExpression {
            fn visit_expr(&mut self, expression: &'ast Expr) {
                if let ExprKind::Path(None, path) = &expression.kind
                    && path
                        .segments
                        .last()
                        .is_some_and(|segment| segment.ident.name.as_str() == "y")
                {
                    self.id = Some(expression.id);
                }
                rustc_ast::visit::walk_expr(self, expression);
            }
        }

        let mut surface = utils::ast::parse_crate(scalar_source.to_owned());
        let mut mapper = utils::ir::AstToHirMapper::new(tcx);
        mapper.map_crate_to_mod(&mut surface, tcx.hir_root_module(), false);
        let mut ast_to_hir = mapper.ast_to_hir;
        let mut finder = YExpression { id: None };
        finder.visit_crate(&surface);
        ast_to_hir.local_map.remove(&finder.id.unwrap());
        let ItemKind::Fn(box function) = &surface.items[0].kind else { unreachable!() };
        let decisions = initial_pointer_decisions(
            &pointer_replacer::Config::default(),
            PointerDecisionOptions {
                assume_nonnegative_offsets: true,
            },
            tcx,
        );
        assert!(!statement_is_preservable(
            &function.body.as_ref().unwrap().stmts[0],
            &ast_to_hir,
            &decisions,
            &PreservationDecisionOverrides::default(),
            tcx,
        ));
    })
    .unwrap();

    let pointer_source = r#"
pub unsafe fn observe(pointer: *mut i32) -> bool {
    let is_null = pointer.is_null();
    is_null
}
"#;
    run_compiler_on_str(pointer_source, |tcx| {
        let mut surface = utils::ast::parse_crate(pointer_source.to_owned());
        let mut mapper = utils::ir::AstToHirMapper::new(tcx);
        mapper.map_crate_to_mod(&mut surface, tcx.hir_root_module(), false);
        let ast_to_hir = mapper.ast_to_hir;
        let ItemKind::Fn(box function) = &surface.items[0].kind else { unreachable!() };
        let parameter_hir = ast_to_hir.local_map[&function.sig.decl.inputs[0].pat.id];
        let mut decisions = initial_pointer_decisions(
            &pointer_replacer::Config::default(),
            PointerDecisionOptions {
                assume_nonnegative_offsets: true,
            },
            tcx,
        );
        decisions.bindings.insert(parameter_hir, PtrKind::Ref(true));
        let overrides = PreservationDecisionOverrides::default();
        let checker = HirPreservationCheck {
            tcx,
            decisions: &decisions,
            preservation_overrides: &overrides,
            owner: parameter_hir.owner,
            direct_callee: None,
            preservable: true,
            sensitive_types: FxHashMap::default(),
            visiting_types: FxHashSet::default(),
        };
        assert!(checker.binding_changes(parameter_hir));
        assert!(!statement_is_preservable(
            &function.body.as_ref().unwrap().stmts[0],
            &ast_to_hir,
            &decisions,
            &overrides,
            tcx,
        ));
    })
    .unwrap();
}

#[test]
fn amendment_2_type_sensitivity_substitutes_generic_local_adts_and_terminates() {
    let source = r#"
pub struct Wrap<T> { pub value: T }
pub struct Recursive<T> {
    pub next: Option<Box<Recursive<T>>>,
    pub value: T,
}
pub unsafe fn generic_values(
    scalar: Wrap<i32>,
    pointer: Wrap<*mut i32>,
    recursive_scalar: Recursive<i32>,
    recursive_pointer: Recursive<*mut i32>,
) {}
"#;
    run_compiler_on_str(source, |tcx| {
        let owner = local_def("generic_values", tcx);
        let decisions = initial_pointer_decisions(
            &pointer_replacer::Config::default(),
            PointerDecisionOptions {
                assume_nonnegative_offsets: true,
            },
            tcx,
        );
        let overrides = PreservationDecisionOverrides::default();
        let mut checker = HirPreservationCheck {
            tcx,
            decisions: &decisions,
            preservation_overrides: &overrides,
            owner: hir::OwnerId { def_id: owner },
            direct_callee: None,
            preservable: true,
            sensitive_types: FxHashMap::default(),
            visiting_types: FxHashSet::default(),
        };
        let signature = tcx.fn_sig(owner).instantiate_identity().skip_binder();
        assert_eq!(
            signature
                .inputs()
                .iter()
                .map(|ty| checker.type_is_sensitive(*ty))
                .collect::<Vec<_>>(),
            [false, true, false, true]
        );
    })
    .unwrap();
}

#[test]
fn amendment_2_unresolved_projection_is_transformation_sensitive() {
    let source = r#"
pub trait HasItem { type Item; }
pub unsafe fn projection<T: HasItem>(value: T::Item) { let _ = value; }
"#;
    run_compiler_on_str(source, |tcx| {
        let owner = local_def("projection", tcx);
        let decisions = initial_pointer_decisions(
            &pointer_replacer::Config::default(),
            PointerDecisionOptions {
                assume_nonnegative_offsets: true,
            },
            tcx,
        );
        let overrides = PreservationDecisionOverrides::default();
        let mut checker = HirPreservationCheck {
            tcx,
            decisions: &decisions,
            preservation_overrides: &overrides,
            owner: hir::OwnerId { def_id: owner },
            direct_callee: None,
            preservable: true,
            sensitive_types: FxHashMap::default(),
            visiting_types: FxHashSet::default(),
        };
        let signature = tcx.fn_sig(owner).instantiate_identity().skip_binder();
        assert!(checker.type_is_sensitive(signature.inputs()[0]));
    })
    .unwrap();
}

#[test]
fn amendment_2_exact_scalar_call_and_pointer_matrix() {
    let scalar = generate(
        r#"pub unsafe fn arithmetic(mut x: i32, y: i32, z: i32) -> (i64, [i32; 2]) {
            x = y + z;
            x += 1;
            let wide = x as i64;
            let pair = (wide, [y, z]);
            return pair;
        }"#,
    );
    assert!(
        function(&scalar, "arithmetic")
            .statements_requiring_transformation
            .is_empty()
    );

    let calls = generate(
        r#"unsafe extern "C" { fn foreign_abs(value: i32) -> i32; }
        pub fn local(value: i32) -> i32 { value + 1 }
        pub unsafe fn local_unsafe(value: i32) -> i32 { value + 1 }
        pub unsafe fn safe_calls(values: &[i32], left: i32, right: i32) -> i32 {
            let a = local(left);
            let b = std::cmp::max(a, right);
            let c = values.len() as i32;
            let d = values[0];
            b + c + d
        }
        pub unsafe fn local_call(value: i32) -> i32 { local_unsafe(value) }
        pub unsafe fn foreign_call(value: i32) -> i32 { foreign_abs(value) }
        pub unsafe fn unsafe_calls(values: &[i32]) -> (i32, char) {
            let value = *values.get_unchecked(0);
            let character = char::from_u32_unchecked(65);
            (value, character)
        }"#,
    );
    for path in ["safe_calls", "local_call"] {
        assert!(
            function(&calls, path)
                .statements_requiring_transformation
                .is_empty(),
            "{path}"
        );
    }
    assert_eq!(
        function(&calls, "foreign_call").statements_requiring_transformation,
        [0]
    );
    assert_eq!(
        function(&calls, "unsafe_calls").statements_requiring_transformation,
        [0, 1]
    );

    let pointers = generate(
        r#"pub unsafe fn pointer_uses(mut left: *mut i32, right: *const i32) -> i32 {
            *left = *right;
            let alias: *const i32 = left;
            let value = *alias;
            value
        }"#,
    );
    assert_eq!(
        function(&pointers, "pointer_uses").statements_requiring_transformation,
        [0, 1, 2]
    );
}

#[test]
fn amendment_2_exact_declaration_generic_and_macro_matrix() {
    let declarations = generate(
        r#"pub unsafe fn declarations() {
            let scalar: i32;
            let pointer: *mut i32;
            scalar = 1;
            pointer = core::ptr::null_mut();
            let _ = scalar;
            let _ = pointer;
        }"#,
    );
    assert_eq!(
        function(&declarations, "declarations").statements_requiring_transformation,
        [1, 3, 5]
    );
    let nested = generate(
        r#"pub unsafe fn nested(
            mut a: Option<Box<(*mut i32, [usize; 2])>>,
            b: Option<Box<(*mut i32, [usize; 2])>>,
        ) { a = b; }
        pub unsafe fn type_arguments() -> usize {
            let marker = core::marker::PhantomData::<*mut i32>;
            let size = core::mem::size_of::<*mut i32>();
            let _ = marker;
            size
        }"#,
    );
    assert_eq!(
        function(&nested, "nested").statements_requiring_transformation,
        [0]
    );
    assert_eq!(
        function(&nested, "type_arguments").statements_requiring_transformation,
        [0, 1, 2]
    );
    let macros = generate(
        r#"pub unsafe fn macros(value: i32) {
            println!("{value}");
            assert!(value > 0);
            let nested = 1 + dbg!(value);
            let _ = nested;
        }"#,
    );
    assert_eq!(
        function(&macros, "macros").statements_requiring_transformation,
        [0, 1, 2]
    );
}

#[test]
fn amendment_2_exact_local_adt_matrix_opens_alias_union_and_recursive_fields() {
    let records = generate(
        r#"pub struct Leaf { pub pointer: *mut i32 }
        pub struct Middle { pub leaf: Leaf }
        pub enum Choice { Empty, Value(Middle) }
        pub union Storage {
            pub leaf: core::mem::ManuallyDrop<Leaf>,
            pub integer: i64,
        }
        pub struct Link {
            pub next: Option<Box<Link>>,
            pub leaf: Leaf,
        }
        pub type Alias = Choice;
        pub unsafe fn move_values(
            mut a: Middle,
            b: Middle,
            mut c: Alias,
            d: Alias,
            mut s: Storage,
            t: Storage,
            mut link: Link,
            other: Link,
        ) {
            a = b;
            c = d;
            s = t;
            link = other;
        }"#,
    );
    assert_eq!(
        function(&records, "move_values").statements_requiring_transformation,
        [0, 1, 2, 3]
    );
}

#[test]
fn amendment_2_exact_patterns_control_and_unsafe_storage_matrix() {
    let patterns = generate(
        r#"pub unsafe fn patterns(
            pair: (i32, i32),
            pointer_pair: Option<(*mut i32, i32)>,
        ) -> i32 {
            let (left, right) = pair;
            let Some((pointer, value)) = pointer_pair else {
                return left + right;
            };
            match value {
                n if n > 0 => { let copy = n; copy }
                _ => { let _ = pointer; 0 }
            }
        }"#,
    );
    assert_eq!(
        function(&patterns, "patterns").statements_requiring_transformation,
        [1, 3, 6]
    );

    let safe_control = generate(
        r#"pub unsafe fn control(flag: bool, left: i32, right: i32) -> i32 {
            if flag {
                let value = left + right;
                return value;
            } else {
                return left - right;
            }
        }"#,
    );
    assert!(
        function(&safe_control, "control")
            .statements_requiring_transformation
            .is_empty()
    );

    let storage = generate(
        r#"pub static mut GLOBAL: i32 = 0;
        pub union Scalar { pub signed: i32, pub unsigned: u32 }
        pub unsafe fn storage(value: Scalar) -> i32 {
            GLOBAL = 1;
            let local = value.signed;
            local + GLOBAL
        }"#,
    );
    assert_eq!(
        function(&storage, "storage").statements_requiring_transformation,
        [0, 1, 2]
    );

    let control_patterns = generate(
        r#"pub unsafe fn control_patterns(
            mut current: Option<*mut i32>,
            values: [*mut i32; 1],
        ) {
            if let Some(pointer) = current {
                let _ = pointer;
            }
            while let Some(pointer) = current.take() {
                let _ = pointer;
            }
            for pointer in values {
                let _ = pointer;
            }
        }"#,
    );
    assert_eq!(
        function(&control_patterns, "control_patterns").statements_requiring_transformation,
        [0, 1, 2, 3, 4, 5]
    );

    let mixed_storage = generate(
        r#"pub union Mixed {
            pub pointer: *mut i32,
            pub integer: i32,
        }
        pub unsafe fn mixed_storage(value: Mixed) -> i32 {
            value.integer
        }"#,
    );
    assert_eq!(
        function(&mixed_storage, "mixed_storage").statements_requiring_transformation,
        [0]
    );
}

#[test]
fn amendment_2_exact_validator_fixture_has_recursive_parent_disposition() {
    let records = generate(
        r#"pub unsafe fn validate_me(flag: bool, mut pointer: *mut i32) -> i32 {
            let scalar = 1 + 2;
            if flag {
                let nested = 3 + 4;
                *pointer = nested;
            } else {
                return scalar;
            }
            scalar
        }"#,
    );
    assert_eq!(
        function(&records, "validate_me").statements_requiring_transformation,
        [1, 3]
    );
}

#[test]
fn amendment_2_exact_unsupported_callable_and_desugar_matrix() {
    let functions = generate(
        r#"pub unsafe fn local(value: i32) -> i32 { value + 1 }
        pub unsafe fn invoke(callback: unsafe fn(i32) -> i32, value: i32) -> i32 {
            callback(value)
        }
        pub unsafe fn hold_callable() {
            let callable = local;
            let _ = callable;
        }
        pub unsafe fn closure(value: i32) -> i32 {
            let add = |other: i32| value + other;
            add(1)
        }
        pub unsafe fn question(value: Option<i32>) -> Option<i32> {
            let inner = value?;
            Some(inner + 1)
        }"#,
    );
    assert_eq!(
        function(&functions, "invoke").statements_requiring_transformation,
        [0]
    );
    assert_eq!(
        function(&functions, "hold_callable").statements_requiring_transformation,
        [0, 1]
    );
    assert_eq!(
        function(&functions, "closure").statements_requiring_transformation,
        [0, 1]
    );
    assert_eq!(
        function(&functions, "question").statements_requiring_transformation,
        [0]
    );

    let assembly = generate(
        r#"pub unsafe fn assembly(mut value: u64) -> u64 {
            core::arch::asm!("/* {0} */", inout(reg) value);
            value
        }"#,
    );
    assert_eq!(
        function(&assembly, "assembly").statements_requiring_transformation,
        [0]
    );
}
