use rustc_ast::{AngleBracketedArg, GenericArg, GenericArgs, visit::Visitor as _};
use utils::compilation::run_compiler_on_str;

use super::*;

#[path = "type_spelling_sources.rs"]
mod type_spelling_sources;

fn type_spelling_source(name: &str) -> &'static str {
    let delimited = match name {
        "motivating" => type_spelling_sources::MOTIVATING,
        "imports" => type_spelling_sources::IMPORTS,
        "candidates" => type_spelling_sources::CANDIDATES,
        "candidate-precedence" => type_spelling_sources::CANDIDATE_PRECEDENCE,
        "reexports" => type_spelling_sources::REEXPORTS,
        "local-fallback-routes" => type_spelling_sources::LOCAL_FALLBACK_ROUTES,
        "external-root-alias" => type_spelling_sources::EXTERNAL_ROOT_ALIAS,
        "source-paths" => type_spelling_sources::SOURCE_PATHS,
        "source-hint-edges" => type_spelling_sources::SOURCE_HINT_EDGES,
        "direct-hints" => type_spelling_sources::DIRECT_HINTS,
        "recursive-types" => type_spelling_sources::RECURSIVE_TYPES,
        "pointers" => type_spelling_sources::POINTERS,
        "compound" => type_spelling_sources::COMPOUND,
        "raw-identifiers" => type_spelling_sources::RAW_IDENTIFIERS,
        "qualified-raw-fallback" => type_spelling_sources::QUALIFIED_RAW_FALLBACK,
        "standard-constructors" => type_spelling_sources::STANDARD_CONSTRUCTORS,
        "standard-bare-imports" => type_spelling_sources::STANDARD_BARE_IMPORTS,
        "no-std-option-success" => type_spelling_sources::NO_STD_OPTION_SUCCESS,
        "named-optional-box" => type_spelling_sources::NAMED_OPTIONAL_BOX,
        "option-collision" => type_spelling_sources::OPTION_COLLISION,
        "box-collision" => type_spelling_sources::BOX_COLLISION,
        "renamed-constructor-collision" => type_spelling_sources::RENAMED_CONSTRUCTOR_COLLISION,
        "glob-constructor-collision" => type_spelling_sources::GLOB_CONSTRUCTOR_COLLISION,
        "optional-box-partial-constructor-collision" => {
            type_spelling_sources::OPTIONAL_BOX_PARTIAL_CONSTRUCTOR_COLLISION
        }
        "local-box-collision" => type_spelling_sources::LOCAL_BOX_COLLISION,
        "extern-prelude-constructor-collision" => {
            type_spelling_sources::EXTERN_PRELUDE_CONSTRUCTOR_COLLISION
        }
        "irrelevant-collisions" => type_spelling_sources::IRRELEVANT_COLLISIONS,
        "no-implicit-prelude-rejection" => type_spelling_sources::NO_IMPLICIT_PRELUDE_REJECTION,
        "no-std-box-rejection" => type_spelling_sources::NO_STD_BOX_REJECTION,
        "box-no-implicit-prelude-rejection" => {
            type_spelling_sources::BOX_NO_IMPLICIT_PRELUDE_REJECTION
        }
        "module-no-implicit-prelude-rejection" => {
            type_spelling_sources::MODULE_NO_IMPLICIT_PRELUDE_REJECTION
        }
        "ancestor-no-implicit-prelude-rejection" => {
            type_spelling_sources::ANCESTOR_NO_IMPLICIT_PRELUDE_REJECTION
        }
        "preserved-parent" => type_spelling_sources::PRESERVED_PARENT,
        "unnameable" => type_spelling_sources::UNNAMEABLE,
        "tree" => type_spelling_sources::TREE,
        "comprehensive" => type_spelling_sources::COMPREHENSIVE,
        _ => panic!("missing type-spelling source fixture {name}"),
    };
    delimited
        .strip_prefix('\n')
        .and_then(|source| source.strip_suffix('\n'))
        .unwrap_or_else(|| panic!("invalid literal boundaries for {name}"))
}

fn generate(source: &str) -> Vec<ItemRecord> {
    run_compiler_on_str(source, |tcx| make_skeletons(source, tcx).unwrap()).unwrap()
}

fn synthesized_printf_rules(
    format_specifier: &str,
    source_expression: crate::Expression,
    target_expression: crate::Expression,
    pointer_anchors: Vec<crate::PointerAnchor>,
    source_type: crate::TypeTree,
) -> crate::RuleDocument {
    let observation = crate::PrintfObservation {
        format_specifier: format_specifier.to_owned(),
        source_expression,
        target_expression,
        pointer_anchors,
        source_adjusted_type: source_type.clone(),
        source_type,
    };
    let document = crate::ObservationDocument {
        schema_version: crate::OBSERVATION_SCHEMA_VERSION,
        observations: vec![],
        printf_observations: vec![observation],
    };
    crate::synthesize_rules(&[document.clone(), document]).unwrap()
}

fn apply_printf_rules_to_third(
    source: &str,
    target: &str,
    rules: &crate::RuleDocument,
    target_binding_type: Option<(&str, crate::TypeTree)>,
) -> String {
    crate::LoadedRuleSet::new(rules).expect("synthesized printf rules must validate");
    run_compiler_on_str(source, |tcx| {
        let mut surface = utils::ast::parse_crate(source.to_owned());
        let mut mapper = utils::ir::AstToHirMapper::new(tcx);
        mapper.map_crate_to_mod(&mut surface, tcx.hir_root_module(), false);
        let function = local_def("third", tcx);
        let decisions = tools_pointer_decisions(tcx);
        let mut source_item = surface
            .items
            .iter()
            .find(|item| {
                item.kind
                    .ident()
                    .is_some_and(|ident| ident.name.as_str() == "third")
            })
            .unwrap()
            .clone();
        annotate_function(&mut source_item, &FxHashSet::default());

        let mut target_item = utils::ast::parse_crate(target.to_owned())
            .items
            .into_iter()
            .next()
            .unwrap();
        let type_speller = TypeSpeller::new(function, &mapper.ast_to_hir, tcx);
        let applied = if let Some((name, target_type)) = target_binding_type {
            apply_rule_set_with_test_binding_catalog(
                &source_item,
                &mut target_item,
                &BTreeSet::from([0]),
                rules,
                function,
                &decisions,
                &mapper.ast_to_hir,
                &type_speller,
                HashMap::from([(local_binding_hir_id(function, name, tcx), target_type)]),
                tcx,
            )
        } else {
            apply_rule_set(
                &source_item,
                &mut target_item,
                &BTreeSet::from([0]),
                rules,
                function,
                &decisions,
                &mapper.ast_to_hir,
                &type_speller,
                tcx,
            )
        }
        .unwrap();
        assert_eq!(applied, BTreeSet::from([0]));
        pprust::item_to_string(&target_item)
    })
    .unwrap()
}

fn installed_candidate_type_checks(candidate: &str) -> bool {
    let candidate = candidate.replace("#[proctor(0)]\n", "");
    run_compiler_on_str(&candidate, utils::type_check).is_ok()
}

#[test]
fn supported_printf_builds_mechanical_and_rule_complete_views() {
    let no_arguments = r#"
unsafe extern "C" { fn printf(format: *const i8, ...) -> i32; }
pub unsafe fn message() { printf(b"hello %%\n\0" as *const u8 as *const i8); }
"#;
    let records = generate(no_arguments);
    let record = function(&records, "message");
    assert_eq!(record.baseline.skeleton, record.applied.skeleton);
    assert!(
        record
            .baseline
            .skeleton
            .contains("::std::print!(\"hello %\\n\");")
    );
    assert!(!record.baseline.needs_transformation);
    assert_eq!(
        record.baseline.statement_dispositions[0].disposition,
        crate::StatementDispositionKind::Mechanical
    );
    assert_eq!(record.baseline.statement_pair_metadata[0].label, 0);
    assert_eq!(
        record.baseline.statement_pair_metadata[0].printf_template,
        Some(crate::PrintfTemplateMetadata {
            rust_format: "hello %\n".into(),
            argument_count: 0,
        })
    );
    assert_eq!(
        record.applied.statement_pair_metadata[0].printf_template,
        record.baseline.statement_pair_metadata[0].printf_template
    );

    let one_argument = r#"
unsafe extern "C" { fn printf(format: *const i8, ...) -> i32; }
pub unsafe fn value(x: i32) { printf(b"%d\0" as *const u8 as *const i8, x); }
"#;
    let binding = crate::RuleExpression::Path {
        value: crate::RuleValueIdentity::Variable {
            sort: crate::VariableSort::Binding,
            index: 0,
        },
    };
    let i32_type = crate::TypeTree::Primitive { name: "i32".into() };
    let rules = crate::RuleDocument {
        schema_version: crate::RULE_SCHEMA_VERSION,
        rules: vec![],
        printf_rules: vec![crate::PrintfRule {
            format_specifier: "%d".into(),
            source_pattern: binding.clone(),
            target_pattern: binding,
            pointer_anchors: vec![],
            source_type: i32_type.clone(),
            source_adjusted_type: i32_type,
        }],
    };
    run_compiler_on_str(one_argument, |tcx| {
        let records = make_skeletons_with_rules(one_argument, Some(&rules), tcx).unwrap();
        let record = function(&records, "value");
        assert!(
            record
                .baseline
                .skeleton
                .contains("::std::print!(\"{}\", todo!());")
        );
        assert!(
            record
                .applied
                .skeleton
                .contains("::std::print!(\"{}\", x);")
        );
        assert_eq!(
            record.baseline.statement_dispositions[0].disposition,
            crate::StatementDispositionKind::Transform
        );
        assert_eq!(
            record.baseline.statement_pair_metadata[0].printf_template,
            Some(crate::PrintfTemplateMetadata {
                rust_format: "{}".into(),
                argument_count: 1,
            })
        );
        assert_eq!(
            record.applied.statement_dispositions[0].disposition,
            crate::StatementDispositionKind::RuleApplied
        );
        assert_eq!(
            record.baseline.statement_pair_metadata[0].printf_template,
            Some(crate::PrintfTemplateMetadata {
                rust_format: "{}".into(),
                argument_count: 1,
            })
        );
    })
    .unwrap();
}

#[test]
fn printf_identity_literal_and_statement_eligibility_is_conservative() {
    let source = r#"
unsafe extern "C" {
    #[link_name = "printf"] fn c_print(format: *const i8, ...) -> i32;
    #[link_name = "different"] fn printf(format: *const i8, ...) -> i32;
}

static FORMAT: &[u8] = b"%d\0";
pub unsafe fn canonical(x: i32) { c_print(b"%d\0" as *const u8 as *const i8, x); }
pub unsafe fn parenthesized(x: i32) { ((c_print((b"%d\0" as *const u8 as *const i8), x))); }
pub unsafe fn wrong_symbol(x: i32) { printf(b"%d\0" as *const u8 as *const i8, x); }
pub unsafe fn missing_nul(x: i32) { c_print(b"%d" as *const u8 as *const i8, x); }
pub unsafe fn interior_nul(x: i32) { c_print(b"%d\0\0" as *const u8 as *const i8, x); }
pub unsafe fn mutable_cast(x: i32) { c_print(b"%d\0" as *const u8 as *mut u8 as *const i8, x); }
pub unsafe fn wrong_cast(x: i32) { c_print(b"%d\0" as *const u8 as *const u16 as *const i8, x); }
pub unsafe fn nonliteral(x: i32) { c_print(FORMAT.as_ptr() as *const i8, x); }
pub unsafe fn count_mismatch(x: i32) { c_print(b"%d %i\0" as *const u8 as *const i8, x); }
pub unsafe fn unsupported(x: i32) { c_print(b"%*d\0" as *const u8 as *const i8, 4, x); }
pub unsafe fn return_used(x: i32) -> i32 { return c_print(b"%d\0" as *const u8 as *const i8, x); }
"#;
    let records = generate(source);
    for name in ["canonical", "parenthesized"] {
        let record = function(&records, name);
        assert!(record.baseline.skeleton.contains("::std::print!"), "{name}");
        assert_eq!(
            record.baseline.statement_dispositions[0].disposition,
            crate::StatementDispositionKind::Transform
        );
    }
    for name in [
        "wrong_symbol",
        "missing_nul",
        "interior_nul",
        "mutable_cast",
        "wrong_cast",
        "nonliteral",
        "count_mismatch",
        "unsupported",
        "return_used",
    ] {
        let record = function(&records, name);
        assert!(
            !record.baseline.skeleton.contains("::std::print!"),
            "{name}"
        );
        assert!(record.baseline.skeleton.contains("todo!()"), "{name}");
        assert_eq!(
            record.baseline.statement_pair_metadata[0].printf_template,
            None
        );
    }
}

#[test]
fn printf_statement_literal_cast_count_and_family_boundaries_are_exhaustive() {
    let source = r#"
unsafe extern "C" {
    fn printf(format: *const i8, ...) -> i32;
    fn fprintf(stream: *mut u8, format: *const i8, ...) -> i32;
    fn sprintf(dst: *mut i8, format: *const i8, ...) -> i32;
    fn snprintf(dst: *mut i8, size: usize, format: *const i8, ...) -> i32;
    fn vprintf(format: *const i8, args: *mut u8) -> i32;
    fn wprintf(format: *const u16, ...) -> i32;
}
static FORMAT: &[u8] = b"%d\0";
unsafe fn format_result() -> *const i8 { b"%d\0".as_ptr() as *const i8 }
unsafe fn sink(_: i32) {}
pub unsafe fn qualified(x: i32) { self::printf(b"%d\0" as *const u8 as *const i8, x); }
pub unsafe fn typical(x: ::core::ffi::c_int) {
    printf(
        b"%d!\n\0" as *const u8 as *const ::core::ffi::c_char,
        x as ::core::ffi::c_int,
    );
}
pub unsafe fn redundant(x: i32) { printf(((b"%d!\n\0" as *const u8) as *const i8) as *const i8, x as i32); }
pub unsafe fn empty() { printf(b"\0" as *const u8 as *const i8); }
pub unsafe fn percent() { printf(b"%%\0" as *const u8 as *const i8); }
pub unsafe fn exact_count(x: i32, p: *const i8) { printf(b"%d %% %s\0" as *const u8 as *const i8, x, p); }
pub unsafe fn let_use(x: i32) { let _n: i32 = printf(b"%d\0" as *const u8 as *const i8, x); }
pub unsafe fn return_use(x: i32) -> i32 { printf(b"%d\0" as *const u8 as *const i8, x) }
pub unsafe fn nested_use(x: i32) { sink(printf(b"%d\0" as *const u8 as *const i8, x)); }
pub unsafe fn arithmetic_use(x: i32) { let _n: i32 = printf(b"%d\0" as *const u8 as *const i8, x) + 1; }
pub unsafe fn interior_before(x: i32) { printf(b"a\0%d\0" as *const u8 as *const i8, x); }
pub unsafe fn integer_cast(x: i32) { printf(b"%d\0".as_ptr() as usize as *const i8, x); }
pub unsafe fn address_deref(x: i32) { printf(&*b"%d\0".as_ptr() as *const u8 as *const i8, x); }
pub unsafe fn method(x: i32) { printf(b"%d\0".as_ptr() as *const i8, x); }
pub unsafe fn transmute(x: i32) { printf(core::mem::transmute::<_, *const i8>(b"%d\0".as_ptr()), x); }
pub unsafe fn identifier(x: i32) { printf(FORMAT.as_ptr() as *const i8, x); }
pub unsafe fn concatenated(x: i32) { printf(concat!("%d", "\0").as_ptr() as *const i8, x); }
pub unsafe fn included(x: i32) { printf(include_bytes!("/dev/null").as_ptr() as *const i8, x); }
pub unsafe fn block(x: i32) { printf(({ b"%d\0" }) as *const u8 as *const i8, x); }
pub unsafe fn conditional(x: i32) { printf((if true { b"%d\0" } else { b"%i\0" }) as *const u8 as *const i8, x); }
pub unsafe fn arithmetic(x: i32) { printf(((b"%d\0".as_ptr() as usize) + 0) as *const i8, x); }
pub unsafe fn result(x: i32) { printf(format_result(), x); }
pub unsafe fn count_zero() { printf(b"%d %% %s\0" as *const u8 as *const i8); }
pub unsafe fn count_one(x: i32) { printf(b"%d %% %s\0" as *const u8 as *const i8, x); }
pub unsafe fn count_three(x: i32, p: *const i8) { printf(b"%d %% %s\0" as *const u8 as *const i8, x, p, x); }
pub unsafe fn percent_extra(x: i32) { printf(b"%%\0" as *const u8 as *const i8, x); }
pub unsafe fn other_prints(p: *mut i8, w: *const u16, x: i32) {
    fprintf(p as *mut u8, b"%d\0".as_ptr() as *const i8, x);
    sprintf(p, b"%d\0".as_ptr() as *const i8, x);
    snprintf(p, 1, b"%d\0".as_ptr() as *const i8, x);
    vprintf(b"%d\0".as_ptr() as *const i8, p as *mut u8);
    wprintf(w, x);
}
mod ordinary { pub unsafe fn printf(_: *const i8, _: i32) {} }
pub unsafe fn rust_function(x: i32) { ordinary::printf(b"%d\0".as_ptr() as *const i8, x); }
"#;
    let records = generate(source);
    for name in [
        "qualified",
        "typical",
        "redundant",
        "empty",
        "percent",
        "exact_count",
    ] {
        let record = function(&records, name);
        assert!(record.baseline.skeleton.contains("::std::print!"), "{name}");
        assert!(
            record.baseline.statement_pair_metadata[0]
                .printf_template
                .is_some()
        );
    }
    for name in [
        "let_use",
        "return_use",
        "nested_use",
        "arithmetic_use",
        "interior_before",
        "integer_cast",
        "address_deref",
        "method",
        "transmute",
        "identifier",
        "concatenated",
        "included",
        "block",
        "conditional",
        "arithmetic",
        "result",
        "count_zero",
        "count_one",
        "count_three",
        "percent_extra",
        "rust_function",
    ] {
        let record = function(&records, name);
        assert!(
            !record.baseline.skeleton.contains("::std::print!"),
            "{name}"
        );
        assert!(
            record
                .baseline
                .statement_pair_metadata
                .iter()
                .all(|metadata| metadata.printf_template.is_none()),
            "{name}"
        );
    }
    let other = function(&records, "other_prints");
    assert!(!other.baseline.skeleton.contains("::std::print!"));
    assert!(
        other
            .baseline
            .statement_pair_metadata
            .iter()
            .all(|metadata| metadata.printf_template.is_none())
    );
}

#[test]
fn printf_prototype_and_abi_must_be_exact() {
    let cases = [
        r#"unsafe extern "C" { fn printf(format: *const i8) -> i32; }
pub unsafe fn f() { printf(b"fixed\0" as *const u8 as *const i8); }"#,
        r#"unsafe extern "C" { fn printf(format: *const i8, tag: i32, ...) -> i32; }
pub unsafe fn f() { printf(b"fixed\0" as *const u8 as *const i8, 0); }"#,
        r#"unsafe extern "C" { fn printf(format: *mut i8, ...) -> i32; }
pub unsafe fn f() { printf(b"fixed\0" as *const u8 as *mut i8); }"#,
        r#"unsafe extern "C" { fn printf(format: *const u16, ...) -> i32; }
pub unsafe fn f() { printf(b"fixed\0" as *const u8 as *const u16); }"#,
        r#"unsafe extern "C" { fn printf(format: *const i8, ...) -> i64; }
pub unsafe fn f() { printf(b"fixed\0" as *const u8 as *const i8); }"#,
        r#"unsafe extern "C-unwind" { fn printf(format: *const i8, ...) -> i32; }
pub unsafe fn f() { printf(b"fixed\0" as *const u8 as *const i8); }"#,
        r#"unsafe extern "system" { fn printf(format: *const i8, ...) -> i32; }
pub unsafe fn f() { printf(b"fixed\0" as *const u8 as *const i8); }"#,
        r#"pub unsafe extern "C" fn printf(_format: *const i8) -> i32 { 0 }
pub unsafe fn f() { printf(b"fixed\0" as *const u8 as *const i8); }"#,
    ];
    for source in cases {
        let records = generate(source);
        let record = function(&records, "f");
        assert!(
            !record.baseline.skeleton.contains("::std::print!"),
            "{source}"
        );
        assert!(record.baseline.skeleton.contains("todo!()"), "{source}");
    }

    let dependency_owned = r#"
extern crate libc;
pub unsafe fn f(x: i32) {
    libc::printf(b"%d\0" as *const u8 as *const libc::c_char, x);
}
"#;
    let records = generate(dependency_owned);
    let record = function(&records, "f");
    assert!(!record.baseline.skeleton.contains("::std::print!"));
    assert!(record.baseline.skeleton.contains("todo!()"));
    assert!(
        record
            .baseline
            .statement_pair_metadata
            .iter()
            .all(|metadata| metadata.printf_template.is_none())
    );
}

#[test]
fn multiple_printf_arguments_apply_only_as_one_complete_statement() {
    let source = r#"
unsafe extern "C" { fn printf(format: *const i8, ...) -> i32; }
pub unsafe fn values(a: i32, b: i32, c: i32) {
    printf(b"%d/%i/%d\0" as *const u8 as *const i8, a, b, c);
}
"#;
    let binding = crate::RuleExpression::Path {
        value: crate::RuleValueIdentity::Variable {
            sort: crate::VariableSort::Binding,
            index: 0,
        },
    };
    let i32_type = crate::TypeTree::Primitive { name: "i32".into() };
    let make_rule = |specifier: &str| {
        let target_pattern = if specifier == "%d" {
            crate::RuleExpression::Cast {
                expression: Box::new(binding.clone()),
                ty: crate::RuleTypeTree::Primitive { name: "i64".into() },
            }
        } else {
            crate::RuleExpression::Unary {
                operator: crate::UnaryOperator::Negate,
                operand: Box::new(binding.clone()),
            }
        };
        crate::PrintfRule {
            format_specifier: specifier.to_owned(),
            source_pattern: binding.clone(),
            target_pattern,
            pointer_anchors: vec![],
            source_type: i32_type.clone(),
            source_adjusted_type: i32_type.clone(),
        }
    };
    let complete = crate::RuleDocument {
        schema_version: crate::RULE_SCHEMA_VERSION,
        rules: vec![],
        printf_rules: vec![make_rule("%d"), make_rule("%i")],
    };
    run_compiler_on_str(source, |tcx| {
        let records = make_skeletons_with_rules(source, Some(&complete), tcx).unwrap();
        let record = function(&records, "values");
        assert!(
            record
                .applied
                .skeleton
                .contains("::std::print!(\"{}/{}/{}\", (a as i64), (-b), (c as i64));"),
            "{}",
            record.applied.skeleton
        );
        assert_eq!(
            record.applied.statement_dispositions[0].disposition,
            crate::StatementDispositionKind::RuleApplied
        );
    })
    .unwrap();

    let partial = crate::RuleDocument {
        schema_version: crate::RULE_SCHEMA_VERSION,
        rules: vec![],
        printf_rules: vec![make_rule("%d")],
    };
    run_compiler_on_str(source, |tcx| {
        let records = make_skeletons_with_rules(source, Some(&partial), tcx).unwrap();
        let record = function(&records, "values");
        assert_eq!(record.applied.skeleton, record.baseline.skeleton);
        assert_eq!(
            record.applied.statement_dispositions[0].disposition,
            crate::StatementDispositionKind::Transform
        );
        assert_eq!(record.applied.skeleton.matches("todo!()").count(), 3);
    })
    .unwrap();
}

#[test]
fn printf_unmaterializable_winner_uses_ranked_fallback_or_rolls_back_atomically() {
    let source = r#"
unsafe extern "C" { fn printf(format: *const i8, ...) -> i32; }
pub unsafe fn value(x: i32) { printf(b"%d\0" as *const u8 as *const i8, x); }
"#;
    let binding = crate::RuleExpression::Path {
        value: crate::RuleValueIdentity::Variable {
            sort: crate::VariableSort::Binding,
            index: 0,
        },
    };
    let i32_type = crate::TypeTree::Primitive { name: "i32".into() };
    let rule = |target_pattern| crate::PrintfRule {
        format_specifier: "%d".into(),
        source_pattern: binding.clone(),
        target_pattern,
        pointer_anchors: vec![],
        source_type: i32_type.clone(),
        source_adjusted_type: i32_type.clone(),
    };
    let unavailable = rule(crate::RuleExpression::Call {
        callee: Box::new(crate::RuleExpression::Path {
            value: crate::RuleValueIdentity::ForeignFunction {
                symbol: "missing_printf_helper".into(),
            },
        }),
        arguments: vec![binding.clone()],
    });
    let fallback = rule(crate::RuleExpression::Cast {
        expression: Box::new(binding.clone()),
        ty: crate::RuleTypeTree::Primitive { name: "i64".into() },
    });
    for printf_rules in [
        vec![unavailable.clone(), fallback.clone()],
        vec![fallback.clone(), unavailable.clone()],
    ] {
        let rules = crate::RuleDocument {
            schema_version: crate::RULE_SCHEMA_VERSION,
            rules: vec![],
            printf_rules,
        };
        run_compiler_on_str(source, |tcx| {
            let records = make_skeletons_with_rules(source, Some(&rules), tcx).unwrap();
            let record = function(&records, "value");
            assert!(
                record
                    .applied
                    .skeleton
                    .contains("::std::print!(\"{}\", (x as i64));"),
                "{}",
                record.applied.skeleton
            );
        })
        .unwrap();
    }

    let only_unavailable = crate::RuleDocument {
        schema_version: crate::RULE_SCHEMA_VERSION,
        rules: vec![],
        printf_rules: vec![unavailable],
    };
    run_compiler_on_str(source, |tcx| {
        let records = make_skeletons_with_rules(source, Some(&only_unavailable), tcx).unwrap();
        let record = function(&records, "value");
        assert_eq!(record.applied, record.baseline);
        assert_eq!(record.applied.skeleton.matches("todo!()").count(), 1);
    })
    .unwrap();
}

#[test]
fn promoted_narrow_printf_rule_installs_without_target_root_context() {
    let source = r#"
unsafe extern "C" { fn printf(format: *const i8, ...) -> i32; }
pub unsafe fn narrow(small: i8) {
    printf(b"%hhd\0" as *const u8 as *const i8, small as i32);
}
"#;
    let binding = crate::RuleExpression::Path {
        value: crate::RuleValueIdentity::Variable {
            sort: crate::VariableSort::Binding,
            index: 0,
        },
    };
    let rules = crate::RuleDocument {
        schema_version: crate::RULE_SCHEMA_VERSION,
        rules: vec![],
        printf_rules: vec![crate::PrintfRule {
            format_specifier: "%hhd".into(),
            source_pattern: crate::RuleExpression::Cast {
                expression: Box::new(binding.clone()),
                ty: crate::RuleTypeTree::Primitive { name: "i32".into() },
            },
            target_pattern: crate::RuleExpression::Cast {
                expression: Box::new(binding),
                ty: crate::RuleTypeTree::Primitive { name: "i8".into() },
            },
            pointer_anchors: vec![],
            source_type: crate::TypeTree::Primitive { name: "i32".into() },
            source_adjusted_type: crate::TypeTree::Primitive { name: "i32".into() },
        }],
    };
    run_compiler_on_str(source, |tcx| {
        let records = make_skeletons_with_rules(source, Some(&rules), tcx).unwrap();
        let record = function(&records, "narrow");
        assert!(
            record
                .applied
                .skeleton
                .contains("::std::print!(\"{}\", (small as i8));"),
            "{}",
            record.applied.skeleton
        );
        assert_eq!(
            record.applied.statement_dispositions[0].disposition,
            crate::StatementDispositionKind::RuleApplied
        );
    })
    .unwrap();
}

#[test]
fn synthesized_string_pointer_rule_installs_into_third_and_type_checks() {
    let source_pointer = crate::TypeTree::RawPointer {
        mutability: crate::RawMutability::Const,
        pointee: Box::new(crate::TypeTree::Primitive { name: "i8".into() }),
    };
    let target_string = crate::TypeTree::Reference {
        mutability: crate::RefMutability::Shared,
        pointee: Box::new(crate::TypeTree::Primitive { name: "str".into() }),
    };
    let binding = crate::Expression::Path {
        value: crate::ValueIdentity::Binding { id: "<id0>".into() },
    };
    let rules = synthesized_printf_rules(
        "%s",
        binding.clone(),
        binding,
        vec![crate::PointerAnchor {
            id: "<id0>".into(),
            source_type: source_pointer.clone(),
            target_type: target_string,
        }],
        source_pointer,
    );
    assert_eq!(rules.printf_rules.len(), 1);

    let candidate = apply_printf_rules_to_third(
        r#"
unsafe extern "C" { fn printf(format: *const i8, ...) -> i32; }
pub unsafe fn third(q: *const i8) {
    printf(b"%s\0" as *const u8 as *const i8, q);
}
"#,
        r#"pub unsafe fn third(q: &str) { #[proctor(0)] todo!(); }"#,
        &rules,
        Some((
            "q",
            crate::TypeTree::Reference {
                mutability: crate::RefMutability::Shared,
                pointee: Box::new(crate::TypeTree::Primitive { name: "str".into() }),
            },
        )),
    );
    assert!(
        candidate.contains("::std::print!(\"{}\", q);"),
        "{candidate}"
    );
    assert!(installed_candidate_type_checks(&candidate));
}

#[test]
fn synthesized_promoted_narrow_rule_installs_into_third_and_type_checks() {
    let binding = crate::Expression::Path {
        value: crate::ValueIdentity::Binding { id: "<id0>".into() },
    };
    let i32_type = crate::TypeTree::Primitive { name: "i32".into() };
    let i8_type = crate::TypeTree::Primitive { name: "i8".into() };
    let rules = synthesized_printf_rules(
        "%hhd",
        crate::Expression::Cast {
            expression: Box::new(binding.clone()),
            ty: i32_type.clone(),
        },
        crate::Expression::Cast {
            expression: Box::new(binding),
            ty: i8_type,
        },
        vec![],
        i32_type,
    );
    assert_eq!(rules.printf_rules.len(), 1);

    let candidate = apply_printf_rules_to_third(
        r#"
unsafe extern "C" { fn printf(format: *const i8, ...) -> i32; }
pub unsafe fn third(small: i8) {
    printf(b"%hhd\0" as *const u8 as *const i8, small as i32);
}
"#,
        r#"pub unsafe fn third(small: i8) { #[proctor(0)] todo!(); }"#,
        &rules,
        None,
    );
    assert!(
        candidate.contains("::std::print!(\"{}\", (small as i8));"),
        "{candidate}"
    );
    assert!(installed_candidate_type_checks(&candidate));
}

#[test]
fn materialized_array_printf_argument_is_rejected_by_rust_type_checking() {
    let binding = crate::Expression::Path {
        value: crate::ValueIdentity::Binding { id: "<id0>".into() },
    };
    let i32_type = crate::TypeTree::Primitive { name: "i32".into() };
    let rules = synthesized_printf_rules(
        "%d",
        binding.clone(),
        crate::Expression::Array {
            elements: vec![binding],
        },
        vec![],
        i32_type,
    );
    assert_eq!(rules.printf_rules.len(), 1);

    let candidate = apply_printf_rules_to_third(
        r#"
unsafe extern "C" { fn printf(format: *const i8, ...) -> i32; }
pub unsafe fn third(x: i32) {
    printf(b"%d\0" as *const u8 as *const i8, x);
}
"#,
        r#"pub unsafe fn third(x: i32) { #[proctor(0)] todo!(); }"#,
        &rules,
        None,
    );
    assert!(
        candidate.contains("::std::print!(\"{}\", [x]);"),
        "{candidate}"
    );
    assert!(
        installed_candidate_type_checks(&candidate.replace("[x]", "x")),
        "the otherwise identical scalar control must satisfy Display"
    );
    assert!(
        !installed_candidate_type_checks(&candidate),
        "the generated array argument must fail Display type checking"
    );
}

#[test]
fn source_type_and_const_generics_reject_before_rule_application() {
    for (source, function, kind) in [
        ("pub unsafe fn f<T>(p: *mut T) { let _ = p; }", "f", "type"),
        (
            "pub unsafe fn g<const N: usize>(p: *mut [i32; N]) { let _ = p; }",
            "g",
            "const",
        ),
    ] {
        run_compiler_on_str(source, |tcx| {
            let without_rules = make_skeletons(source, tcx).unwrap_err();
            let empty = crate::RuleDocument::default();
            let with_rules = make_skeletons_with_rules(source, Some(&empty), tcx).unwrap_err();
            for error in [&without_rules, &with_rules] {
                assert_eq!(error.kind, GenerationErrorKind::UnsupportedGeneric);
                assert_eq!(error.function_path, function);
                assert!(error.message.contains(kind), "{}", error.message);
            }
            assert_eq!(without_rules, with_rules);
        })
        .unwrap();
    }

    let lifetime_only = "pub unsafe fn h<'a>(p: *mut i32) { let _ = p; }";
    run_compiler_on_str(lifetime_only, |tcx| {
        assert!(make_skeletons(lifetime_only, tcx).is_ok());
        assert!(
            make_skeletons_with_rules(lifetime_only, Some(&crate::RuleDocument::default()), tcx,)
                .is_ok()
        );
    })
    .unwrap();
}

#[test]
fn every_type_spelling_source_fixture_compiles_independently() {
    let names = [
        "motivating",
        "imports",
        "candidates",
        "candidate-precedence",
        "reexports",
        "local-fallback-routes",
        "external-root-alias",
        "source-paths",
        "source-hint-edges",
        "direct-hints",
        "recursive-types",
        "pointers",
        "compound",
        "raw-identifiers",
        "qualified-raw-fallback",
        "standard-constructors",
        "standard-bare-imports",
        "no-std-option-success",
        "named-optional-box",
        "option-collision",
        "box-collision",
        "renamed-constructor-collision",
        "glob-constructor-collision",
        "optional-box-partial-constructor-collision",
        "local-box-collision",
        "extern-prelude-constructor-collision",
        "irrelevant-collisions",
        "no-implicit-prelude-rejection",
        "no-std-box-rejection",
        "box-no-implicit-prelude-rejection",
        "module-no-implicit-prelude-rejection",
        "ancestor-no-implicit-prelude-rejection",
        "preserved-parent",
        "unnameable",
        "tree",
        "comprehensive",
    ];
    for name in names {
        let source = type_spelling_source(name);
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
    assert!(type_spelling_sources::MOTIVATING.starts_with('\n'));
    assert!(type_spelling_sources::MOTIVATING.ends_with('\n'));
    assert!(type_spelling_source("motivating").starts_with("unsafe extern \"C\""));
    assert!(type_spelling_source("motivating").ends_with('}'));
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
        "option-collision" => {
            let signature = signature("wrapped::read");
            assert_eq!(
                signature.input_decs,
                [Some(PtrKind::OptRef(false)), Some(PtrKind::OptRef(false))]
            );
        }
        "box-collision" | "glob-constructor-collision" => {
            let path = if name == "box-collision" {
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
        "renamed-constructor-collision"
        | "extern-prelude-constructor-collision"
        | "no-implicit-prelude-rejection"
        | "module-no-implicit-prelude-rejection"
        | "ancestor-no-implicit-prelude-rejection" => {
            let path = match name {
                "renamed-constructor-collision" => "renamed::read",
                "ancestor-no-implicit-prelude-rejection" => "outer::middle::inner::read",
                _ => "wrapped::read",
            };
            assert_eq!(signature(path).input_decs[0], Some(PtrKind::OptRef(false)));
        }
        "optional-box-partial-constructor-collision" => {
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
        "local-box-collision" => {
            let def_id = local_def_path("consumer::local_only", tcx);
            for binding in ["first", "second"] {
                assert_eq!(
                    local_binding_decision(def_id, binding, &decisions, tcx),
                    PtrKind::Box
                );
            }
        }
        "no-std-box-rejection" | "box-no-implicit-prelude-rejection" => {
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
            canonical_item(&function(&records, path).baseline.skeleton),
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
            let krate = utils::ast::parse_crate(function.baseline.skeleton);
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
        "\"baseline\"",
        "\"applied\"",
        "\"source_signature\"",
        "\"target_signature\"",
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
    let records = generate(type_spelling_source("motivating"));
    let record = function(&records, "src::lib::cb_remove_gamma_rgb");
    assert!(record.target_signature.contains("rgb: cb_rgb"));
    assert!(record.baseline.skeleton.contains("let mut init: cb_rgb"));
    assert!(!record.baseline.skeleton.contains("src::lib::cb_rgb"));
}

#[test]
fn direct_renamed_and_glob_imports_name_inferred_locals() {
    let source = type_spelling_source("imports");
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
    let candidates_source = type_spelling_source("candidates");
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
            .baseline
            .skeleton
            .contains("let mut value: Alpha")
    );
    let source_hint = &function(&first, "aliases::source_hint").target_signature;
    assert!(source_hint.contains("pointer: &Zed"), "{source_hint}");

    let precedence_source = type_spelling_source("candidate-precedence");
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
    let source = type_spelling_source("candidates");
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
            .baseline
            .skeleton
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
    let source = type_spelling_source("reexports");
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
    let local = &function(&records, "consumer::local").baseline.skeleton;
    assert!(local.contains("let mut value: crate::api::Exposed"));
    assert!(!local.contains("hidden::Public"));

    let source = type_spelling_source("local-fallback-routes");
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
    let reexports = type_spelling_source("reexports");
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
    let external = &function(&records, "consumer::external").baseline.skeleton;
    assert!(compact(external).contains(&compact(
        "let mut value: ::std::hash::DefaultHasher = ::std::hash::DefaultHasher::new();"
    )));
    assert!(!external.contains("hash::random"));

    let alias_source = type_spelling_source("external-root-alias");
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
    assert!(
        compact(
            &function(&alias_records, "consumer::external_alias")
                .baseline
                .skeleton
        )
        .contains(&compact(
            "let mut value: ::alt_std::hash::DefaultHasher = rust_std::hash::DefaultHasher::new();"
        ))
    );

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
            .baseline
            .skeleton
            .contains("let mut value: ::aliased_std::hash::DefaultHasher")
    })
    .unwrap();
    assert!(uses_alias);
}

#[test]
fn source_alias_and_relative_pointee_paths_are_reused() {
    let source = type_spelling_source("source-paths");
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
    assert!(local_alias.baseline.transform_labels().contains(&0));
    assert!(
        local_alias
            .baseline
            .skeleton
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

    let source = type_spelling_source("source-hint-edges");
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
            .baseline
            .skeleton
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
    let source = type_spelling_source("pointers");
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
    assert!(!update.baseline.skeleton.contains("crate::Node"));
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
            .baseline
            .skeleton
            .contains("let mut pointer: &mut Node")
    );
    assert!(!local_pointer.baseline.skeleton.contains("crate::Node"));
    assert!(!local_pointer.target_signature.contains("crate::Node"));
    let locals = simple_local_types(source);
    assert!(locals.contains(&("local_pointer".into(), "node".into(), "Node".into())));
    assert!(locals.contains(&("local_pointer".into(), "pointer".into(), "&mut Node".into())));
}

#[test]
fn raw_identifiers_remain_parseable_in_inferred_and_pointer_types() {
    let source = type_spelling_source("raw-identifiers");
    run_compiler_on_str(source, |tcx| {
        let read = local_def_path("r#type::read", tcx);
        let inferred = local_def_path("r#type::inferred", tcx);
        let target = local_def_path("r#type::r#match", tcx).to_def_id();
        assert_eq!(resolve_one_segment_type(read, "r#match", tcx), target);
        assert_eq!(resolve_one_segment_type(inferred, "r#match", tcx), target);
        for record in make_skeletons(source, tcx).unwrap() {
            if let ItemRecord::Function(function) = record {
                utils::ast::parse_crate(function.baseline.skeleton);
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
            .baseline
            .skeleton
            .contains("let mut value: r#match")
    );
    let qualified = type_spelling_source("qualified-raw-fallback");
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
                utils::ast::parse_crate(function.baseline.skeleton);
            }
        }
    })
    .unwrap();
    let records = generate(qualified);
    assert!(
        function(&records, "consumer::inferred")
            .baseline
            .skeleton
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
    let source = type_spelling_source("standard-constructors");
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
            .baseline
            .skeleton
            .contains("let mut p: Box<i32>")
    );
    assert!(
        function(&records, "wrapped::foo")
            .baseline
            .skeleton
            .contains("let mut q: Option<Box<i32>>")
    );

    let source = type_spelling_source("standard-bare-imports");
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
            .baseline
            .skeleton
            .contains("let mut p: Box<i32>")
    );

    let source = type_spelling_source("no-std-option-success");
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

    let source = type_spelling_source("named-optional-box");
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
    let foo = &function(&records, "consumer::foo").baseline.skeleton;
    assert!(foo.contains("let mut p: Box<LocalP>"));
    assert!(foo.contains("let mut q: Option<Box<LocalQ>>"));

    let source = type_spelling_source("irrelevant-collisions");
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
    let source = type_spelling_source("preserved-parent");
    let records = generate(source);
    let record = function(&records, "preserved");
    assert!(
        !record.baseline.transform_labels().contains(&0),
        "the containing `if` label must remain wholly preserved"
    );
    let skeleton = &record.baseline.skeleton;
    assert!(skeleton.contains("let mut value = Local { value: 1 }"));
    assert!(!skeleton.contains("let mut value: Local"));
}

#[test]
fn type_spelling_failures_are_structured_and_atomic() {
    let option_collision = type_spelling_source("option-collision");
    run_compiler_on_str(option_collision, |tcx| {
        assert_constructor_failure_pointer_prerequisites("option-collision", tcx);
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
            "box-collision",
            type_spelling_source("box-collision"),
            "wrapped::allocate",
            &["return", "Box", "wrapped::Box"][..],
        ),
        (
            "renamed-constructor-collision",
            type_spelling_source("renamed-constructor-collision"),
            "renamed::read",
            &["parameter `p`", "OptRef(false)", "fake::WrongOption"][..],
        ),
        (
            "glob-constructor-collision",
            type_spelling_source("glob-constructor-collision"),
            "globbed::allocate",
            &["return", "Box", "fake::glob::Box"][..],
        ),
        (
            "optional-box-partial-constructor-collision",
            type_spelling_source("optional-box-partial-constructor-collision"),
            "wrapped::owned_id",
            &["parameter `p`", "OptBox", "wrapped::Box"][..],
        ),
        (
            "local-box-collision",
            type_spelling_source("local-box-collision"),
            "consumer::local_only",
            &["local `first`", "Box", "consumer::Box"][..],
        ),
        (
            "extern-prelude-constructor-collision",
            type_spelling_source("extern-prelude-constructor-collision"),
            "wrapped::read",
            &["parameter `p`", "Option", "extern prelude"][..],
        ),
        (
            "no-implicit-prelude-rejection",
            type_spelling_source("no-implicit-prelude-rejection"),
            "wrapped::read",
            &["parameter `p`", "Option", "implicit prelude disabled"][..],
        ),
        (
            "no-std-box-rejection",
            type_spelling_source("no-std-box-rejection"),
            "allocate",
            &["return", "Box", "unresolved"][..],
        ),
        (
            "box-no-implicit-prelude-rejection",
            type_spelling_source("box-no-implicit-prelude-rejection"),
            "allocate",
            &["return", "Box", "implicit prelude disabled"][..],
        ),
        (
            "module-no-implicit-prelude-rejection",
            type_spelling_source("module-no-implicit-prelude-rejection"),
            "wrapped::read",
            &["parameter `p`", "Option", "implicit prelude disabled"][..],
        ),
        (
            "ancestor-no-implicit-prelude-rejection",
            type_spelling_source("ancestor-no-implicit-prelude-rejection"),
            "outer::middle::inner::read",
            &["parameter `p`", "Option", "implicit prelude disabled"][..],
        ),
    ];
    for (name, source, expected_path, message_parts) in constructor_failures {
        run_compiler_on_str(source, |tcx| {
            assert_constructor_failure_pointer_prerequisites(name, tcx);
            match name {
                "optional-box-partial-constructor-collision" => {
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
                "no-implicit-prelude-rejection" => {
                    let read = local_def_path("wrapped::read", tcx);
                    assert!(tcx.is_lang_item(
                        resolved_bare_constructor(read, sym::Option, tcx),
                        hir::LangItem::Option
                    ));
                }
                "local-box-collision" => {
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
        if name == "optional-box-partial-constructor-collision" {
            assert!(error.message.contains("requires bare `Box`"));
            assert!(!error.message.contains("requires bare `Option`"));
        }
    }

    let unnameable = type_spelling_source("unnameable");
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
        type_spelling_source("imports"),
        type_spelling_source("candidates"),
        type_spelling_source("candidate-precedence"),
        type_spelling_source("reexports"),
        type_spelling_source("local-fallback-routes"),
        type_spelling_source("external-root-alias"),
        type_spelling_source("raw-identifiers"),
        type_spelling_source("qualified-raw-fallback"),
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
                    utils::ast::parse_crate(function.baseline.skeleton);
                }
            }
        })
        .unwrap();
    }

    let candidates = generate(type_spelling_source("candidates"));
    assert!(
        function(&candidates, "aliases::inferred")
            .baseline
            .skeleton
            .contains("let mut value: Alpha")
    );
    assert!(
        function(&candidates, "aliases::source_hint")
            .target_signature
            .contains("&Zed")
    );
    assert!(
        function(&candidates, "collision::inferred")
            .baseline
            .skeleton
            .contains("crate::left::Thing")
    );
    let reexports = generate(type_spelling_source("reexports"));
    assert!(
        function(&reexports, "consumer::local")
            .baseline
            .skeleton
            .contains("crate::api::Exposed")
    );
    assert!(
        function(&reexports, "consumer::external")
            .baseline
            .skeleton
            .contains("::std::hash::DefaultHasher")
    );
    let routes = generate(type_spelling_source("local-fallback-routes"));
    for (path, ty) in [
        ("consumer::restricted", "crate::restricted_api::Exposed"),
        ("consumer::shortest", "crate::short::S"),
        ("consumer::tie", "crate::alpha::T"),
    ] {
        assert!(function(&routes, path).baseline.skeleton.contains(ty));
    }
    let aliases = generate(type_spelling_source("external-root-alias"));
    assert!(
        function(&aliases, "consumer::external_alias")
            .baseline
            .skeleton
            .contains("::alt_std::hash::DefaultHasher")
    );

    let function_record = candidates
        .iter()
        .find(|record| record.path() == "aliases::inferred")
        .unwrap();
    assert_function_record_json_key_order(function_record);
}

fn comprehensive_fixture() -> &'static str {
    type_spelling_source("comprehensive")
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
            "baseline",
            "applied",
            "source_signature",
            "target_signature",
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
            .baseline
            .skeleton
            .contains("let mut s: &str = \"quote:"),
        "{}",
        before.baseline.skeleton
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
    assert_eq!(labels(&f.baseline.skeleton), [0, 1, 2]);
}

#[test]
fn labels_reset_for_each_function() {
    let records = generate(
        "pub unsafe fn a() -> i32 { let x = 1; x } pub unsafe fn b() -> i32 { let y = 2; y + 1 }",
    );
    for path in ["a", "b"] {
        assert_eq!(labels(&function(&records, path).annotated_source), [0, 1]);
        assert_eq!(labels(&function(&records, path).baseline.skeleton), [0, 1]);
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
    assert_eq!(labels(&f.annotated_source), labels(&f.baseline.skeleton));
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
fn rejects_local_const_and_static_recursively() {
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
fn rejects_representative_other_local_items() {
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
    let skeleton = &function(&records, "f").baseline.skeleton;
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
    let skeleton = compact(&function(&records, "f").baseline.skeleton);
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
    let skeleton = compact(&function(&records, "f").baseline.skeleton);
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
    let skeleton = compact(&function(&records, "f").baseline.skeleton);
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
    let skeleton = compact(&function(&records, "f").baseline.skeleton);
    assert!(skeleton.contains("if flag"));
    assert!(skeleton.contains("} else {"));
    assert_eq!(
        labels(&function(&records, "f").baseline.skeleton),
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
    assert_eq!(labels(&f.baseline.skeleton), (0..=8).collect::<Vec<_>>());
    assert_eq!(f.baseline.skeleton.matches("if ").count(), 4);
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
    let skeleton = compact(&function(&records, "f").baseline.skeleton);
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
    let skeleton = compact(&function(&records, "f").baseline.skeleton);
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
    assert_eq!(labels(&f.baseline.skeleton), (0..=11).collect::<Vec<_>>());
    let skeleton = compact(&f.baseline.skeleton);
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
    assert_eq!(labels(&f.baseline.skeleton), [0, 1, 2, 3, 4, 5]);
    let skeleton = compact(&f.baseline.skeleton);
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
    let skeleton = &function(&records, "keep_names").baseline.skeleton;
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
    run_compiler_on_str(&f.baseline.skeleton, |_| ()).unwrap();
}

#[test]
fn preserves_payloadless_control_expressions_without_holes() {
    let source =
        "pub unsafe fn f(flag: bool) { if flag { return; } loop { if flag { continue; } break; } }";
    let records = generate(source);
    let skeleton = &function(&records, "f").baseline.skeleton;
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
        assert_eq!(labels(&function.baseline.skeleton), [0]);
        assert!(function.baseline.skeleton.contains("if "));
    }
    let wrapped_let = function(&records, "wrapped_let");
    assert_eq!(labels(&wrapped_let.annotated_source), [0, 1]);
    assert_eq!(labels(&wrapped_let.baseline.skeleton), [0, 1]);
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
        assert_eq!(labels(&function.baseline.skeleton), [0, 1]);
        assert_eq!(function.annotated_source.matches("if ").count(), 2);
        assert!(function.baseline.skeleton.contains("if "));
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
            .baseline
            .skeleton
            .contains("let mut p: &mut i32")
    );
    assert!(
        function(&records, "read_local")
            .baseline
            .skeleton
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
            .baseline
            .skeleton
            .contains("let mut p: &[i32]")
    );
    assert!(
        function(&records, "write_array")
            .baseline
            .skeleton
            .contains("let mut p: &mut [i32]")
    );
    assert!(!skeletons_to_json(&records).unwrap().contains("SliceCursor"));
}

#[test]
fn promotes_array_derived_locals_to_explicit_slices() {
    let records = generate(array_pointer_fixture());
    assert!(
        function(&records, "read_array")
            .baseline
            .skeleton
            .contains("let mut p: &[i32] = todo!();")
    );
    assert!(
        function(&records, "write_array")
            .baseline
            .skeleton
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
            .baseline
            .skeleton
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
            .baseline
            .skeleton
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
            .baseline
            .skeleton
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
            .baseline
            .skeleton
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
    type_spelling_source("tree")
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
    let skeleton = &function(&records, "foo").baseline.skeleton;
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
            .baseline
            .skeleton
            .contains("let mut nonnegative: isize")
    );
    assert!(
        function(&records, "caller")
            .baseline
            .skeleton
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
        labels(&function(&records, "model::read").baseline.skeleton),
        [0, 1, 2, 3]
    );
    assert_eq!(
        labels(&function(&records, "helper").baseline.skeleton),
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

    let tree = type_spelling_source("tree");
    let comprehensive = type_spelling_source("comprehensive");
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
        view: tree_function.baseline.clone(),
    };
    let validation_request = ValidationRequest {
        schema_version: 1,
        expected_functions: vec![expected],
        transformation: tree_function.baseline.skeleton.clone(),
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
        accepted_correspondence: vec![],
        schema_version: 1,
        items: vec![ReplacementItem {
            id: tree_function.id,
            path: tree_function.path.clone(),
            name: tree_function.name.clone(),
            view: tree_function.baseline.clone(),
        }],
        transformation: tree_function.baseline.skeleton.clone(),
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

    let compound = type_spelling_source("compound");
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

    let direct = type_spelling_source("direct-hints");
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

    let recursive = type_spelling_source("recursive-types");
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
        type_spelling_source("tree"),
        type_spelling_source("pointers"),
        type_spelling_source("compound"),
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

    let tree = type_spelling_source("tree");
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

    let normalized = normalize_target_safety(type_spelling_source("motivating")).unwrap();
    let replaced = run_compiler_on_str(&normalized, |tcx| {
        let records = make_skeletons(&normalized, tcx).unwrap();
        let record = function(&records, "src::lib::cb_remove_gamma_rgb");
        assert_eq!(record.path, "src::lib::cb_remove_gamma_rgb");
        assert_eq!(
            record.target_signature,
            "pub unsafe fn cb_remove_gamma_rgb(mut rgb: cb_rgb) -> cb_rgb"
        );
        assert_eq!(record.baseline.transform_labels(), [1]);
        let generated_labels = labels(&record.baseline.skeleton);
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
                view: record.baseline.clone(),
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
                view: record.baseline.clone(),
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
                accepted_correspondence: vec![],
                schema_version: 1,
                items: vec![ReplacementItem {
                    id: record.id,
                    path: record.path.clone(),
                    name: record.name.clone(),
                    view: record.baseline.clone(),
                }],
                transformation,
            },
            tcx,
        )
        .unwrap()
    })
    .unwrap()
    .source;
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
    for rendering in [&record.annotated_source, &record.baseline.skeleton] {
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
    assert!(ref_mut.baseline.skeleton.contains("let ref mut borrowed"));
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
    assert!(safe.baseline.skeleton.starts_with("pub unsafe fn safe"));
    assert!(
        safe.baseline
            .skeleton
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
    let value: serde_json::Value =
        serde_json::from_str(&skeletons_to_json(&records).unwrap()).unwrap();
    let function = &value.as_array().unwrap()[0];
    assert_eq!(function["baseline"], function["applied"]);
    assert_eq!(function["baseline"]["needs_transformation"], false);
    assert_eq!(
        function["baseline"]["statement_pair_metadata"],
        serde_json::json!([])
    );
    assert_eq!(
        function["baseline"]["statement_dispositions"],
        serde_json::json!([{"label": 0, "disposition": "preserve", "children": []}])
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
        ["c_strlen", "strlen"]
    );
    assert_eq!(
        function(&records, "hold_callable").foreign_function_names,
        ["c_strlen", "strlen"]
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

    let scan_records = generate(
        r#"unsafe extern "C" {
    #[link_name = "scanf"]
    fn rust_scanf(value: i32) -> i32;
}
unsafe extern "C-unwind" {
    #[link_name = "scanf"]
    fn unwind_scanf(value: i32) -> i32;
}
pub unsafe fn scan(value: i32) -> i32 { rust_scanf(value) }
pub unsafe fn unwind(value: i32) -> i32 { unwind_scanf(value) }
"#,
    );
    assert_eq!(
        function(&scan_records, "scan").foreign_function_names,
        ["rust_scanf", "scanf"]
    );
    assert_eq!(
        function(&scan_records, "unwind").foreign_function_names,
        ["unwind_scanf"]
    );

    let direct_scan = generate(
        r#"unsafe extern "C" { fn scanf(value: i32) -> i32; }
pub unsafe fn direct(value: i32) -> i32 { scanf(value) }
"#,
    );
    assert_eq!(
        function(&direct_scan, "direct").foreign_function_names,
        ["scanf"]
    );

    #[cfg(all(target_os = "linux", target_env = "gnu"))]
    {
        let basename = generate(
            r#"extern crate libc;
pub unsafe fn dependency_basename(value: *mut libc::c_char) -> *mut libc::c_char {
    libc::posix_basename(value)
}
"#,
        );
        assert_eq!(
            function(&basename, "dependency_basename").foreign_function_names,
            ["posix_basename"]
        );
        assert!(
            !function(&basename, "dependency_basename")
                .foreign_function_names
                .iter()
                .any(|name| name == "__xpg_basename")
        );
    }
}

#[test]
fn preserves_scalar_statements_and_metadata() {
    let source = r#"
pub unsafe fn scalar(mut x: i32, y: i32, z: i32) -> i32 {
    let sum = y + z;
    x = sum * 2;
    return x;
}
"#;
    let records = generate(source);
    let function = function(&records, "scalar");
    assert!(!function.baseline.needs_transformation);
    assert!(function.baseline.transform_labels().is_empty());
    let skeleton = compact(&function.baseline.skeleton);
    assert!(skeleton.contains("y + z"));
    assert!(skeleton.contains("sum * 2"));
    assert!(skeleton.contains("return x"));
    assert!(!skeleton.contains("todo!"));
}

#[test]
fn mixed_control_has_recursive_parent_disposition() {
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
    assert!(function.baseline.needs_transformation);
    assert_eq!(function.baseline.transform_labels(), [2]);
    assert_eq!(
        function.baseline.statement_dispositions[0].disposition,
        crate::StatementDispositionKind::PreserveShell
    );
    let skeleton = compact(&function.baseline.skeleton);
    assert!(skeleton.contains("if flag"));
    assert!(skeleton.contains("y + z"));
    assert!(skeleton.contains("y - z"));
    assert!(skeleton.contains("return difference"));
}

#[test]
fn safe_if_and_while_shells_do_not_become_holes_for_transforming_bodies() {
    let source = r#"
pub unsafe fn controls(mut count: usize, flag: bool, pointer: *mut i32) {
    if flag {
        *pointer = 1;
    }
    while count > 0 {
        *pointer = 2;
        count -= 1;
    }
}
"#;
    let records = generate(source);
    let function = function(&records, "controls");
    let skeleton = compact(&function.baseline.skeleton);

    assert!(skeleton.contains("if flag"), "{skeleton}");
    assert!(skeleton.contains("while count > 0"), "{skeleton}");
    assert!(!skeleton.contains("if todo!()"), "{skeleton}");
    assert!(!skeleton.contains("while todo!()"), "{skeleton}");
    assert_eq!(function.baseline.transform_labels(), [1, 3]);
    assert_eq!(
        function.baseline.statement_dispositions[0].disposition,
        crate::StatementDispositionKind::PreserveShell
    );
    assert_eq!(
        function.baseline.statement_dispositions[1].disposition,
        crate::StatementDispositionKind::PreserveShell
    );
}

#[test]
fn sensitive_control_operands_remain_transformable() {
    let source = r#"
pub unsafe fn sensitive(mut pointer: *mut i32) {
    if pointer.is_null() {
        return;
    }
    while *pointer > 0 {
        return;
    }
}
"#;
    let records = generate(source);
    let function = function(&records, "sensitive");
    let skeleton = compact(&function.baseline.skeleton);

    assert!(skeleton.contains("if todo!()"), "{skeleton}");
    assert!(skeleton.contains("while todo!()"), "{skeleton}");
    assert_eq!(function.baseline.transform_labels(), [0, 2]);
}

#[test]
fn callable_policy_is_conservative() {
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
    assert_eq!(caller.baseline.transform_labels(), Vec::<u32>::new());
}

#[test]
fn unsafe_nonlocal_calls_macros_and_raw_pointers_transform() {
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
    assert_eq!(function.baseline.transform_labels(), [0, 1, 2]);
}

#[test]
fn opens_local_adts_but_not_external_representation() {
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
    assert_eq!(function.baseline.transform_labels(), [0, 2]);
    assert!(compact(&function.baseline.skeleton).contains("other_integers"));
}

#[test]
fn restricted_conditionals_preserve_or_stay_opaque() {
    let source = r#"
pub unsafe fn conditional(mut x: i32, flag: bool, pointer: *mut i32) -> i32 {
    x = 1 + if flag { 2 } else { 3 };
    x = 1 + if flag { *pointer } else { 3 };
    x
}
"#;
    let records = generate(source);
    let function = function(&records, "conditional");
    assert_eq!(function.baseline.transform_labels(), [1]);
    let skeleton = compact(&function.baseline.skeleton);
    assert!(skeleton.contains("1 + if flag"));
    assert_eq!(skeleton.matches("todo!()").count(), 1);
}

#[test]
fn future_field_change_marks_containing_values_sensitive() {
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
            .baseline
            .transform_labels()
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
        make_skeletons_with_preservation_overrides(source, None, tcx, &overrides).unwrap()
    })
    .unwrap();
    assert_eq!(
        function(&changed, "move_future")
            .baseline
            .transform_labels(),
        [0, 1]
    );
}

#[test]
fn changed_local_signature_forces_call_transformation() {
    let source = r#"
pub unsafe fn scalar_callee(value: i32) -> i32 { value + 1 }
pub unsafe fn scalar_caller(value: i32) -> i32 { scalar_callee(value) }
"#;
    assert!(
        function(&generate(source), "scalar_caller")
            .baseline
            .transform_labels()
            .is_empty()
    );
    let changed = run_compiler_on_str(source, |tcx| {
        let mut overrides = PreservationDecisionOverrides::default();
        overrides
            .changed_local_signatures
            .insert(local_def("scalar_callee", tcx));
        make_skeletons_with_preservation_overrides(source, None, tcx, &overrides).unwrap()
    })
    .unwrap();
    assert_eq!(
        function(&changed, "scalar_caller")
            .baseline
            .transform_labels(),
        [0]
    );
}

#[test]
fn missing_ast_mapping_and_changed_binding_decision_are_conservative() {
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
        let excluded_roots = FxHashSet::default();
        let checker = HirPreservationCheck {
            tcx,
            decisions: &decisions,
            preservation_overrides: &overrides,
            owner: parameter_hir.owner,
            direct_callee: None,
            excluded_roots: &excluded_roots,
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
fn type_sensitivity_substitutes_generic_local_adts_and_terminates() {
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
        let excluded_roots = FxHashSet::default();
        let mut checker = HirPreservationCheck {
            tcx,
            decisions: &decisions,
            preservation_overrides: &overrides,
            owner: hir::OwnerId { def_id: owner },
            direct_callee: None,
            excluded_roots: &excluded_roots,
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
fn unresolved_projection_is_transformation_sensitive() {
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
        let excluded_roots = FxHashSet::default();
        let mut checker = HirPreservationCheck {
            tcx,
            decisions: &decisions,
            preservation_overrides: &overrides,
            owner: hir::OwnerId { def_id: owner },
            direct_callee: None,
            excluded_roots: &excluded_roots,
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
fn exact_scalar_call_and_pointer_matrix() {
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
            .baseline
            .transform_labels()
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
                .baseline
                .transform_labels()
                .is_empty(),
            "{path}"
        );
    }
    assert_eq!(
        function(&calls, "foreign_call").baseline.transform_labels(),
        [0]
    );
    assert_eq!(
        function(&calls, "unsafe_calls").baseline.transform_labels(),
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
        function(&pointers, "pointer_uses")
            .baseline
            .transform_labels(),
        [0, 1, 2]
    );
}

#[test]
fn exact_declaration_generic_and_macro_matrix() {
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
        function(&declarations, "declarations")
            .baseline
            .transform_labels(),
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
    assert_eq!(function(&nested, "nested").baseline.transform_labels(), [0]);
    assert_eq!(
        function(&nested, "type_arguments")
            .baseline
            .transform_labels(),
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
        function(&macros, "macros").baseline.transform_labels(),
        [0, 1, 2]
    );
}

#[test]
fn exact_local_adt_matrix_opens_alias_union_and_recursive_fields() {
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
        function(&records, "move_values")
            .baseline
            .transform_labels(),
        [0, 1, 2, 3]
    );
}

#[test]
fn exact_patterns_control_and_unsafe_storage_matrix() {
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
        function(&patterns, "patterns").baseline.transform_labels(),
        [1, 6]
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
            .baseline
            .transform_labels()
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
        function(&storage, "storage").baseline.transform_labels(),
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
        function(&control_patterns, "control_patterns")
            .baseline
            .transform_labels(),
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
        function(&mixed_storage, "mixed_storage")
            .baseline
            .transform_labels(),
        [0]
    );
}

#[test]
fn exact_validator_fixture_has_recursive_parent_disposition() {
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
        function(&records, "validate_me")
            .baseline
            .transform_labels(),
        [3]
    );
}

#[test]
fn exact_unsupported_callable_and_desugar_matrix() {
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
        function(&functions, "invoke").baseline.transform_labels(),
        [0]
    );
    assert_eq!(
        function(&functions, "hold_callable")
            .baseline
            .transform_labels(),
        [0, 1]
    );
    assert_eq!(
        function(&functions, "closure").baseline.transform_labels(),
        [0, 1]
    );
    assert_eq!(
        function(&functions, "question").baseline.transform_labels(),
        [0]
    );

    let assembly = generate(
        r#"pub unsafe fn assembly(mut value: u64) -> u64 {
            core::arch::asm!("/* {0} */", inout(reg) value);
            value
        }"#,
    );
    assert_eq!(
        function(&assembly, "assembly").baseline.transform_labels(),
        [0]
    );
}

#[test]
fn records_parameter_and_inferred_local_types_from_source_and_target_asts() {
    let records = generate(
        r#"pub unsafe fn update(mut pointer: *mut i32, mut amount: i32) -> i32 {
            let mut alias = pointer;
            *alias += amount;
            *pointer + *alias
        }"#,
    );
    let record = function(&records, "update");
    assert_eq!(
        record
            .baseline
            .statement_pair_metadata
            .iter()
            .map(|entry| entry.label)
            .collect::<Vec<_>>(),
        record.baseline.transform_labels()
    );
    assert!(
        record
            .baseline
            .statement_pair_metadata
            .iter()
            .all(|entry| entry.pointer_variables_complete)
    );
    assert_eq!(
        record
            .baseline
            .statement_pair_metadata
            .iter()
            .map(|entry| {
                (
                    entry.label,
                    entry.before_statement.as_str(),
                    entry
                        .pointer_variables
                        .iter()
                        .map(|variable| variable.name.as_str())
                        .collect::<Vec<_>>(),
                )
            })
            .collect::<Vec<_>>(),
        [
            (
                0,
                "#[proctor(0)]\nlet mut alias = pointer;",
                vec!["alias", "pointer"],
            ),
            (1, "#[proctor(1)]\n(*alias += amount);", vec!["alias"],),
            (
                2,
                "#[proctor(2)]\n(*pointer + *alias)",
                vec!["pointer", "alias"],
            ),
        ]
    );
    let pointer = &record.baseline.statement_pair_metadata[0].pointer_variables[1];
    assert_eq!(pointer.before_type, "*mut i32");
    assert!(!pointer.before_type_is_inferred);
    assert_eq!(
        pointer.origin,
        PointerVariableOrigin::Parameter { index: 0 }
    );
    assert_eq!(pointer.selected_target_type, "&mut i32");
    assert!(record.target_signature.contains("pointer: &mut i32"));
    let alias = &record.baseline.statement_pair_metadata[0].pointer_variables[0];
    assert_eq!(alias.before_type, "*mut i32");
    assert!(alias.before_type_is_inferred);
    assert_eq!(
        alias.origin,
        PointerVariableOrigin::Local {
            declaration_label: 0
        }
    );
    assert_eq!(alias.selected_target_type, "*mut i32");
    assert!(record.baseline.skeleton.contains("alias: *mut i32"));
    assert!(
        record
            .baseline
            .statement_pair_metadata
            .iter()
            .flat_map(|entry| &entry.pointer_variables)
            .all(|variable| variable.name != "amount")
    );

    let long = generate(
        r#"pub unsafe fn long(
            mut pointer: *mut core::option::Option<
                core::result::Result<
                    [core::mem::MaybeUninit<i32>; 32],
                    core::convert::Infallible,
                >,
            >,
        ) {
            *pointer = None;
        }"#,
    );
    let long_type = &function(&long, "long").baseline.statement_pair_metadata[0].pointer_variables
        [0]
    .before_type;
    assert_eq!(
        long_type,
        "*mut core::option::Option<core::result::Result<[core::mem::MaybeUninit<i32>; 32],\n\
         core::convert::Infallible>>"
    );
    assert!(long_type.contains('\n'));
}

#[test]
fn deduplicates_by_binding_identity_in_first_occurrence_order() {
    let records = generate(
        r#"pub unsafe fn shadow(mut pointer: *mut i32) -> i32 {
            if pointer.is_null() {
                0
            } else {
                let mut value = pointer;
                {
                    let mut value = pointer;
                    *value += 1;
                }
                *value
            }
        }"#,
    );
    let record = function(&records, "shadow");
    let parent = record
        .baseline
        .statement_pair_metadata
        .iter()
        .find(|entry| {
            entry
                .pointer_variables
                .iter()
                .filter(|variable| variable.name == "value")
                .count()
                == 2
        })
        .expect("the transformed parent contains both shadowed bindings");
    let values = parent
        .pointer_variables
        .iter()
        .filter(|variable| variable.name == "value")
        .collect::<Vec<_>>();
    assert_eq!(
        parent
            .pointer_variables
            .iter()
            .map(|variable| (variable.name.as_str(), variable.origin.clone()))
            .collect::<Vec<_>>(),
        [
            ("pointer", PointerVariableOrigin::Parameter { index: 0 },),
            (
                "value",
                PointerVariableOrigin::Local {
                    declaration_label: 2,
                },
            ),
            (
                "value",
                PointerVariableOrigin::Local {
                    declaration_label: 4,
                },
            ),
        ]
    );
    assert_eq!(
        values
            .iter()
            .map(|variable| variable.origin.clone())
            .collect::<Vec<_>>(),
        [
            PointerVariableOrigin::Local {
                declaration_label: 2,
            },
            PointerVariableOrigin::Local {
                declaration_label: 4,
            },
        ]
    );
    let json = skeletons_to_json(&records).unwrap();
    assert!(!json.contains("HirId"));
}

#[test]
fn before_statement_is_the_complete_prompt_facing_source_subtree() {
    let records = generate(
        r#"pub unsafe fn choose(mut pointer: *mut i32, mut flag: bool) -> i32 {
            if !pointer.is_null() && flag {
                *pointer += 1;
                *pointer
            } else {
                0
            }
        }"#,
    );
    let record = function(&records, "choose");
    let parent = record
        .baseline
        .statement_pair_metadata
        .iter()
        .find(|entry| {
            entry
                .before_statement
                .contains("if !pointer.is_null() && flag")
        })
        .unwrap();
    assert_eq!(
        parent.before_statement,
        "#[proctor(0)]\nif !pointer.is_null() && flag {\n\n    #[proctor(1)]\n    (*pointer += 1);\n\n    \
         #[proctor(2)]\n    *pointer\n} else {\n\n    #[proctor(3)]\n    0\n}"
    );
    assert_eq!(
        record
            .baseline
            .statement_pair_metadata
            .iter()
            .find(|entry| entry.label == 1)
            .unwrap()
            .before_statement,
        "#[proctor(1)]\n(*pointer += 1);"
    );
    assert_eq!(
        record
            .baseline
            .statement_pair_metadata
            .iter()
            .find(|entry| entry.label == 2)
            .unwrap()
            .before_statement,
        "#[proctor(2)]\n*pointer"
    );
    assert!(record.annotated_source.contains("mut pointer"));
    assert!(record.annotated_source.contains("mut flag"));
}

#[test]
fn includes_only_outer_raw_pointer_parameters_and_simple_locals() {
    let records = generate(
        r#"pub struct Holder { pub pointer: *mut i32 }
        pub static mut GLOBAL: *mut i32 = core::ptr::null_mut();
        pub unsafe fn exclusions(mut holder: Holder, mut pointer: *mut i32) -> i32 {
            let mut copied = holder.pointer;
            let mut tuple = (pointer, 1_i32);
            let mut scalar = *pointer;
            scalar += *GLOBAL;
            scalar + tuple.1 + *copied
        }"#,
    );
    let names = function(&records, "exclusions")
        .baseline
        .statement_pair_metadata
        .iter()
        .flat_map(|entry| &entry.pointer_variables)
        .map(|variable| variable.name.as_str())
        .collect::<FxHashSet<_>>();
    assert_eq!(names, ["pointer", "copied"].into_iter().collect());
    assert!(
        !names
            .iter()
            .any(|name| name.starts_with("proctor_temp_var_"))
    );

    let source = "pub unsafe fn source(mut pointer: *mut i32) { *pointer += 1; }";
    run_compiler_on_str(source, |tcx| {
        let mut surface = utils::ast::parse_crate(source.to_owned());
        let mut mapper = utils::ir::AstToHirMapper::new(tcx);
        mapper.map_crate_to_mod(&mut surface, tcx.hir_root_module(), false);
        let generated =
            utils::ast::parse_stmt("let proctor_temp_var_0: *mut i32 = pointer;".to_owned());
        let catalog = PointerBindingCatalog {
            variables: FxHashMap::default(),
            known_ineligible: FxHashSet::default(),
        };
        let mut collector = PointerOccurrenceCollector {
            ast_to_hir: &mapper.ast_to_hir,
            catalog: &catalog,
            complete: true,
            seen: FxHashSet::default(),
            variables: vec![],
            tcx,
        };
        collector.visit_stmt(&generated);
        assert!(
            collector.variables.is_empty(),
            "a parser-only generated binding has no immutable source identity"
        );
        assert!(!collector.complete);
    })
    .unwrap();
}

#[test]
fn metadata_labels_exactly_match_transformation_dispositions() {
    let preserved = generate("pub unsafe fn f(mut value: i32) -> i32 { value + 1 }");
    let record = function(&preserved, "f");
    assert!(record.baseline.transform_labels().is_empty());
    assert!(record.baseline.statement_pair_metadata.is_empty());

    let transformed =
        generate("pub unsafe fn f(mut pointer: *mut i32) -> i32 { *pointer += 1; *pointer }");
    let record = function(&transformed, "f");
    assert_eq!(
        record
            .baseline
            .statement_pair_metadata
            .iter()
            .map(|entry| entry.label)
            .collect::<Vec<_>>(),
        record.baseline.transform_labels()
    );
    assert_eq!(
        skeletons_to_json(&transformed).unwrap(),
        skeletons_to_json(&transformed).unwrap()
    );
    let json = skeletons_to_json(&transformed).unwrap();
    let positions = [
        "\"statement_dispositions\"",
        "\"statement_pair_metadata\"",
        "\"foreign_function_names\"",
    ]
    .map(|key| json.find(key).unwrap());
    assert!(positions.windows(2).all(|pair| pair[0] < pair[1]));

    let empty_rows = generate(
        r#"unsafe extern "C" { fn foreign(); }
        pub unsafe fn invoke() { foreign(); }"#,
    );
    let entry = &function(&empty_rows, "invoke")
        .baseline
        .statement_pair_metadata[0];
    assert!(entry.pointer_variables_complete);
    assert!(entry.pointer_variables.is_empty());

    let populated = generate("pub unsafe fn pointer(mut pointer: *mut i32) -> i32 { *pointer }");
    let json = skeletons_to_json(&populated).unwrap();
    let statement_keys = [
        "\"label\"",
        "\"before_statement\"",
        "\"pointer_variables_complete\"",
        "\"pointer_variables\"",
    ]
    .map(|key| json.find(key).unwrap());
    assert!(statement_keys.windows(2).all(|pair| pair[0] < pair[1]));
    let variable_json = serde_json::to_string(
        &function(&populated, "pointer")
            .baseline
            .statement_pair_metadata[0]
            .pointer_variables[0],
    )
    .unwrap();
    let variable_keys = [
        "\"name\"",
        "\"origin\"",
        "\"before_type\"",
        "\"selected_target_type\"",
        "\"before_type_is_inferred\"",
    ]
    .map(|key| variable_json.find(key).unwrap());
    assert!(variable_keys.windows(2).all(|pair| pair[0] < pair[1]));
    assert!(
        serde_json::to_string(&populated)
            .unwrap()
            .contains("\"origin\":{\"kind\":\"parameter\",\"index\":0}")
    );
}

#[test]
fn main_override_aliases_and_raw_fallbacks_report_actual_skeleton_types() {
    let records = generate(
        r#"type Pointer = *mut i32;
        pub unsafe fn alias(mut pointer: Pointer) { *pointer += 1; }
        pub unsafe fn main_0(
            mut argc: core::ffi::c_int,
            mut argv: *mut *mut core::ffi::c_char,
        ) -> core::ffi::c_int {
            let _ = argv;
            argc
        }"#,
    );
    let alias = function(&records, "alias");
    let pointer = alias
        .baseline
        .statement_pair_metadata
        .iter()
        .flat_map(|entry| &entry.pointer_variables)
        .find(|variable| variable.name == "pointer")
        .unwrap();
    assert_eq!(pointer.before_type, "Pointer");
    assert_eq!(pointer.selected_target_type, "&mut i32");
    assert!(alias.target_signature.contains("pointer: &mut i32"));

    let main = function(&records, "main_0");
    let argv = main
        .baseline
        .statement_pair_metadata
        .iter()
        .flat_map(|entry| &entry.pointer_variables)
        .find(|variable| variable.name == "argv")
        .unwrap();
    assert_eq!(argv.before_type, "*mut *mut core::ffi::c_char");
    assert_eq!(argv.selected_target_type, "&mut [&mut [i8]]");

    let raw = generate(raw_pointer_fixture());
    let retained = function(&raw, "keep_alias_raw")
        .baseline
        .statement_pair_metadata
        .iter()
        .flat_map(|entry| &entry.pointer_variables)
        .find(|variable| variable.name == "a")
        .unwrap();
    assert_eq!(retained.before_type, "*mut i32");
    assert_eq!(retained.selected_target_type, "*mut i32");
}

#[test]
fn unmappable_statement_emits_resolvable_rows_and_incomplete_flag() {
    let records = generate(
        r#"macro_rules! bump {
            ($pointer:expr) => {{ *$pointer += 1; }};
        }
        pub unsafe fn incomplete(mut pointer: *mut i32) -> i32 {
            if !pointer.is_null() {
                bump!(pointer);
            }
            *pointer
        }"#,
    );
    let entry = function(&records, "incomplete")
        .baseline
        .statement_pair_metadata
        .iter()
        .find(|entry| entry.before_statement.contains("if !pointer.is_null()"))
        .unwrap();
    assert!(!entry.pointer_variables_complete);
    assert_eq!(entry.pointer_variables.len(), 1);
    let pointer = &entry.pointer_variables[0];
    assert_eq!(pointer.name, "pointer");
    assert_eq!(
        pointer.origin,
        PointerVariableOrigin::Parameter { index: 0 }
    );
    assert_eq!(pointer.before_type, "*mut i32");
    assert_eq!(pointer.selected_target_type, "Option<&mut i32>");
    assert!(!pointer.before_type_is_inferred);

    let source = "pub unsafe fn missing(mut value: i32) { value += 1; }";
    run_compiler_on_str(source, |tcx| {
        let mut surface = utils::ast::parse_crate(source.to_owned());
        let mut mapper = utils::ir::AstToHirMapper::new(tcx);
        mapper.map_crate_to_mod(&mut surface, tcx.hir_root_module(), false);
        let mut ast_to_hir = mapper.ast_to_hir;
        let ItemKind::Fn(box function) = &surface.items[0].kind else { unreachable!() };
        let statement = &function.body.as_ref().unwrap().stmts[0];
        ast_to_hir.local_map.remove(&statement.id);
        let catalog = PointerBindingCatalog {
            variables: FxHashMap::default(),
            known_ineligible: FxHashSet::default(),
        };
        let mut collector = PointerOccurrenceCollector {
            ast_to_hir: &ast_to_hir,
            catalog: &catalog,
            complete: true,
            seen: FxHashSet::default(),
            variables: vec![],
            tcx,
        };
        collector.visit_stmt(statement);
        collector.collect_hir_root(statement);
        assert!(!collector.complete);
        assert!(collector.variables.is_empty());
    })
    .unwrap();

    let source = "pub unsafe fn missing(mut pointer: *mut i32) { *pointer += 1; }";
    run_compiler_on_str(source, |tcx| {
        let mut surface = utils::ast::parse_crate(source.to_owned());
        let mut mapper = utils::ir::AstToHirMapper::new(tcx);
        mapper.map_crate_to_mod(&mut surface, tcx.hir_root_module(), false);
        let ast_to_hir = mapper.ast_to_hir;
        let ItemKind::Fn(box function) = &surface.items[0].kind else { unreachable!() };
        let statement = &function.body.as_ref().unwrap().stmts[0];
        let catalog = PointerBindingCatalog {
            variables: FxHashMap::default(),
            known_ineligible: FxHashSet::default(),
        };
        let mut collector = PointerOccurrenceCollector {
            ast_to_hir: &ast_to_hir,
            catalog: &catalog,
            complete: true,
            seen: FxHashSet::default(),
            variables: vec![],
            tcx,
        };
        collector.visit_stmt(statement);
        collector.collect_hir_root(statement);
        assert!(
            !collector.complete,
            "a resolved raw-pointer use absent from the catalog is incomplete"
        );
        assert!(collector.variables.is_empty());
    })
    .unwrap();

    let known_ineligible = generate(
        r#"pub unsafe fn destructured(mut pair: (*mut i32, i32)) -> i32 {
            let (mut pointer, mut scalar) = pair;
            *pointer += scalar;
            *pointer
        }"#,
    );
    let record = function(&known_ineligible, "destructured");
    assert!(!record.baseline.statement_pair_metadata.is_empty());
    assert!(
        record
            .baseline
            .statement_pair_metadata
            .iter()
            .all(|entry| entry.pointer_variables_complete),
        "resolved raw-pointer destructuring bindings are known exclusions"
    );
    assert!(
        record
            .baseline
            .statement_pair_metadata
            .iter()
            .flat_map(|entry| &entry.pointer_variables)
            .all(|variable| variable.name != "pointer")
    );
}

#[test]
fn contextual_rule_types_use_only_the_closed_expected_type_producers() {
    fn expression_statement(statement: &Stmt) -> &Expr {
        match &statement.kind {
            StmtKind::Expr(expression) | StmtKind::Semi(expression) => expression,
            _ => panic!("expected expression statement"),
        }
    }

    fn strip_parentheses(mut expression: &Expr) -> &Expr {
        while let ExprKind::Paren(inner) = &expression.kind {
            expression = inner;
        }
        expression
    }

    let source = r#"
struct Holder { ptr: *mut i32 }
enum Choice { Value { ptr: *mut i32 } }
struct Sink;
impl Sink { unsafe fn consume(&self, _: *mut i32) {} }
unsafe extern "C" { fn ffi_consume(_: *mut i32); }
unsafe fn consume(_: *mut i32) {}
unsafe fn get_slot() -> *mut *mut i32 { core::ptr::null_mut() }

pub unsafe fn contexts(
    mut q: *mut i32,
    p: *mut i32,
    fp: unsafe fn(*mut i32),
    sink: Sink,
    flag: bool,
) -> *mut i32 {
    let init: *mut i32 = (p);
    q = p;
    consume(p);
    ffi_consume(p);
    fp(p);
    sink.consume(p);
    let _branch = if flag { p } else { q };
    Holder { ptr: p };
    p;
    return p;
}

pub unsafe fn tail(p: *mut i32) -> *mut i32 { p }
pub unsafe fn place(mut out: *mut *mut i32, rhs: *mut i32) { *out = rhs; }
pub unsafe fn boxed_place(
    slot: *mut Option<&'static i32>,
    rhs: Option<&'static i32>,
) { *slot = rhs; }
pub unsafe fn optional_place(
    out: *mut Option<&'static i32>,
    rhs: Option<&'static i32>,
) { *out = rhs; }
pub unsafe fn call_place(rhs: *mut i32) { *get_slot() = rhs; }
pub unsafe fn parenthesized(mut q: *mut i32, rhs: *mut i32) { (q) = rhs; }
pub unsafe fn indexed(slots: &mut [*mut i32], index: usize, rhs: *mut i32) {
    slots[index] = rhs;
}
pub unsafe fn field_place(holder: *mut Holder, rhs: *mut i32) { (*holder).ptr = rhs; }
pub unsafe fn variant_field(p: *mut i32) { Choice::Value { ptr: p }; }
pub unsafe fn external_generic(p: *mut i32) { core::mem::drop::<*mut i32>(p); }
"#;
    run_compiler_on_str(source, |tcx| {
        let mut surface = utils::ast::parse_crate(source.to_owned());
        let mut mapper = utils::ir::AstToHirMapper::new(tcx);
        mapper.map_crate_to_mod(&mut surface, tcx.hir_root_module(), false);
        let ast_to_hir = mapper.ast_to_hir;
        let find_item = |name: &str| {
            surface
                .items
                .iter()
                .find(|item| {
                    item.kind
                        .ident()
                        .is_some_and(|ident| ident.name.as_str() == name)
                })
                .unwrap()
        };
        let primitive = || TypeTree::Primitive { name: "i32".into() };
        let raw_i32 = || TypeTree::RawPointer {
            mutability: RawMutability::Mut,
            pointee: Box::new(primitive()),
        };
        let reference_slice = || TypeTree::Reference {
            mutability: RefMutability::Mutable,
            pointee: Box::new(TypeTree::Slice {
                element: Box::new(primitive()),
            }),
        };
        let option_reference = |mutable| TypeTree::Adt {
            adt_kind: AdtKind::Enum,
            identity: AdtIdentity::External {
                crate_name: "core".into(),
                path: vec!["option".into(), "Option".into()],
            },
            arguments: vec![TypeTree::Reference {
                mutability: if mutable {
                    RefMutability::Mutable
                } else {
                    RefMutability::Shared
                },
                pointee: Box::new(primitive()),
            }],
        };

        let contexts = local_def("contexts", tcx);
        let mut decisions = tools_pointer_decisions(tcx);
        let signature = decisions.signatures.data.get_mut(&contexts).unwrap();
        signature.input_decs[0] = Some(PtrKind::Slice(true));
        signature.output_dec = Some(PtrKind::OptRef(false));
        decisions
            .signatures
            .data
            .get_mut(&local_def("consume", tcx))
            .unwrap()
            .input_decs[0] = Some(PtrKind::Slice(true));
        let init_binding = local_binding_hir_id(contexts, "init", tcx);
        decisions
            .bindings
            .insert(init_binding, PtrKind::OptRef(true));
        let source_item = find_item("contexts");
        let ItemKind::Fn(box function) = &source_item.kind else { unreachable!() };
        let statements = &function.body.as_ref().unwrap().stmts;
        let catalog =
            rule_target_binding_catalog(source_item, contexts, &decisions, &ast_to_hir, tcx);
        let infer = |root: &Expr, lhs| {
            contextual_target_type(
                root.id,
                lhs,
                source_item,
                contexts,
                &catalog,
                &decisions,
                &ast_to_hir,
                tcx,
            )
        };

        let StmtKind::Let(local) = &statements[0].kind else { unreachable!() };
        let rustc_ast::LocalKind::Init(initializer) = &local.kind else { unreachable!() };
        let initializer = strip_parentheses(initializer);
        assert_eq!(infer(initializer, false), Some(option_reference(true)));

        let ExprKind::Assign(left, right, _) = &expression_statement(&statements[1]).kind else {
            unreachable!()
        };
        assert_eq!(infer(right, false), Some(reference_slice()));
        assert_eq!(infer(left, true), Some(reference_slice()));
        assert_eq!(infer(left, false), None);

        let direct_argument = |index: usize| {
            let ExprKind::Call(_, arguments) = &expression_statement(&statements[index]).kind else {
                unreachable!()
            };
            arguments[0].as_ref()
        };
        assert_eq!(infer(direct_argument(2), false), Some(reference_slice()));
        assert_eq!(infer(direct_argument(3), false), Some(raw_i32()));
        assert_eq!(infer(direct_argument(4), false), None);

        let ExprKind::MethodCall(method) = &expression_statement(&statements[5]).kind else {
            unreachable!()
        };
        assert_eq!(infer(&method.args[0], false), None);

        let StmtKind::Let(local) = &statements[6].kind else { unreachable!() };
        let rustc_ast::LocalKind::Init(branch) = &local.kind else { unreachable!() };
        let ExprKind::If(_, then, _) = &branch.kind else { unreachable!() };
        let branch_value = expression_statement(then.stmts.last().unwrap());
        assert_eq!(infer(branch_value, false), None);

        let ExprKind::Struct(value) = &expression_statement(&statements[7]).kind else {
            unreachable!()
        };
        assert_eq!(infer(&value.fields[0].expr, false), Some(raw_i32()));
        assert_eq!(infer(expression_statement(&statements[8]), false), None);
        let ExprKind::Ret(Some(returned)) = &expression_statement(&statements[9]).kind else {
            unreachable!()
        };
        assert_eq!(infer(returned, false), Some(option_reference(false)));

        let tail = local_def("tail", tcx);
        decisions
            .signatures
            .data
            .get_mut(&tail)
            .unwrap()
            .output_dec = Some(PtrKind::BoxedSlice);
        let tail_item = find_item("tail");
        let ItemKind::Fn(box tail_function) = &tail_item.kind else { unreachable!() };
        let tail_expression =
            expression_statement(tail_function.body.as_ref().unwrap().stmts.last().unwrap());
        let tail_catalog = rule_binding_catalog(tail_item, tail, &decisions, &ast_to_hir, tcx);
        let tail_type = contextual_target_type(
            tail_expression.id,
            false,
            tail_item,
            tail,
            &tail_catalog,
            &decisions,
            &ast_to_hir,
            tcx,
        )
        .unwrap();
        let TypeTree::Adt { identity, arguments, .. } = tail_type else { unreachable!() };
        assert!(matches!(identity, AdtIdentity::External { crate_name, path }
            if crate_name == "alloc" && path == ["boxed", "Box"]));
        assert_eq!(arguments.len(), 2, "Box retains its allocator argument");
        assert!(matches!(&arguments[0], TypeTree::Slice { element }
            if **element == primitive()));
        assert!(matches!(&arguments[1], TypeTree::Adt { identity: AdtIdentity::External { crate_name, path }, arguments, .. }
            if crate_name == "alloc" && path == &["alloc", "Global"] && arguments.is_empty()));

        let place = local_def("place", tcx);
        decisions.signatures.data.get_mut(&place).unwrap().input_decs[0] =
            Some(PtrKind::OptRef(true));
        let place_item = find_item("place");
        let ItemKind::Fn(box place_function) = &place_item.kind else { unreachable!() };
        let ExprKind::Assign(place_left, place_right, _) =
            &expression_statement(&place_function.body.as_ref().unwrap().stmts[0]).kind
        else {
            unreachable!()
        };
        let place_catalog = rule_binding_catalog(place_item, place, &decisions, &ast_to_hir, tcx);
        assert_eq!(
            contextual_target_type(
                place_right.id,
                false,
                place_item,
                place,
                &place_catalog,
                &decisions,
                &ast_to_hir,
                tcx,
            ),
            Some(raw_i32())
        );
        assert_eq!(
            contextual_target_type(
                place_left.id,
                true,
                place_item,
                place,
                &place_catalog,
                &decisions,
                &ast_to_hir,
                tcx,
            ),
            None,
            "a dereference is not a bare-local assignment LHS"
        );

        for (function_name, decision) in [
            ("boxed_place", PtrKind::Box),
            ("optional_place", PtrKind::OptRef(true)),
        ] {
            let function_id = local_def(function_name, tcx);
            decisions
                .signatures
                .data
                .get_mut(&function_id)
                .unwrap()
                .input_decs[0] = Some(decision);
            let item = find_item(function_name);
            let ItemKind::Fn(box function) = &item.kind else { unreachable!() };
            let ExprKind::Assign(_, right, _) =
                &expression_statement(&function.body.as_ref().unwrap().stmts[0]).kind
            else {
                unreachable!()
            };
            let catalog = rule_binding_catalog(item, function_id, &decisions, &ast_to_hir, tcx);
            assert_eq!(
                contextual_target_type(
                    right.id,
                    false,
                    item,
                    function_id,
                    &catalog,
                    &decisions,
                    &ast_to_hir,
                    tcx,
                ),
                Some(option_reference(false)),
                "{function_name}"
            );
        }

        let call_place = local_def("call_place", tcx);
        decisions
            .signatures
            .data
            .get_mut(&local_def("get_slot", tcx))
            .unwrap()
            .output_dec = Some(PtrKind::Ref(true));
        let call_place_item = find_item("call_place");
        let ItemKind::Fn(box call_place_function) = &call_place_item.kind else { unreachable!() };
        let ExprKind::Assign(_, call_place_right, _) =
            &expression_statement(&call_place_function.body.as_ref().unwrap().stmts[0]).kind
        else {
            unreachable!()
        };
        let call_place_catalog =
            rule_binding_catalog(call_place_item, call_place, &decisions, &ast_to_hir, tcx);
        assert_eq!(
            contextual_target_type(
                call_place_right.id,
                false,
                call_place_item,
                call_place,
                &call_place_catalog,
                &decisions,
                &ast_to_hir,
                tcx,
            ),
            Some(raw_i32())
        );

        let parenthesized = local_def("parenthesized", tcx);
        decisions
            .signatures
            .data
            .get_mut(&parenthesized)
            .unwrap()
            .input_decs[0] = Some(PtrKind::Box);
        let parenthesized_item = find_item("parenthesized");
        let ItemKind::Fn(box parenthesized_function) = &parenthesized_item.kind else {
            unreachable!()
        };
        let ExprKind::Assign(parenthesized_left, _, _) =
            &expression_statement(&parenthesized_function.body.as_ref().unwrap().stmts[0]).kind
        else {
            unreachable!()
        };
        let parenthesized_catalog = rule_binding_catalog(
            parenthesized_item,
            parenthesized,
            &decisions,
            &ast_to_hir,
            tcx,
        );
        let mut root = parenthesized_left.as_ref();
        while let ExprKind::Paren(inner) = &root.kind {
            root = inner;
        }
        assert!(matches!(
            contextual_target_type(
                root.id,
                true,
                parenthesized_item,
                parenthesized,
                &parenthesized_catalog,
                &decisions,
                &ast_to_hir,
                tcx,
            ),
            Some(TypeTree::Adt { identity: AdtIdentity::External { crate_name, path }, arguments, .. })
                if crate_name == "alloc" && path == ["boxed", "Box"] && arguments.len() == 2
        ));

        for (function_name, configure) in [
            ("indexed", None),
            ("field_place", Some((0, PtrKind::Ref(true)))),
        ] {
            let function_id = local_def(function_name, tcx);
            if let Some((index, decision)) = configure {
                decisions
                    .signatures
                    .data
                    .get_mut(&function_id)
                    .unwrap()
                    .input_decs[index] = Some(decision);
            }
            let item = find_item(function_name);
            let ItemKind::Fn(box function) = &item.kind else { unreachable!() };
            let ExprKind::Assign(_, right, _) =
                &expression_statement(&function.body.as_ref().unwrap().stmts[0]).kind
            else {
                unreachable!()
            };
            let catalog =
                rule_target_binding_catalog(item, function_id, &decisions, &ast_to_hir, tcx);
            assert_eq!(
                contextual_target_type(
                    right.id,
                    false,
                    item,
                    function_id,
                    &catalog,
                    &decisions,
                    &ast_to_hir,
                    tcx,
                ),
                Some(raw_i32()),
                "{function_name}"
            );
        }

        let external_generic = local_def("external_generic", tcx);
        let external_item = find_item("external_generic");
        let ItemKind::Fn(box external_function) = &external_item.kind else { unreachable!() };
        let ExprKind::Call(_, arguments) =
            &expression_statement(&external_function.body.as_ref().unwrap().stmts[0]).kind
        else {
            unreachable!()
        };
        let external_catalog = rule_target_binding_catalog(
            external_item,
            external_generic,
            &decisions,
            &ast_to_hir,
            tcx,
        );
        assert_eq!(
            contextual_target_type(
                arguments[0].id,
                false,
                external_item,
                external_generic,
                &external_catalog,
                &decisions,
                &ast_to_hir,
                tcx,
            ),
            Some(raw_i32())
        );

        let variant_field = local_def("variant_field", tcx);
        let variant_item = find_item("variant_field");
        let ItemKind::Fn(box variant_function) = &variant_item.kind else { unreachable!() };
        let ExprKind::Struct(variant) =
            &expression_statement(&variant_function.body.as_ref().unwrap().stmts[0]).kind
        else {
            unreachable!()
        };
        let variant_catalog = rule_target_binding_catalog(
            variant_item,
            variant_field,
            &decisions,
            &ast_to_hir,
            tcx,
        );
        assert_eq!(
            contextual_target_type(
                variant.fields[0].expr.id,
                false,
                variant_item,
                variant_field,
                &variant_catalog,
                &decisions,
                &ast_to_hir,
                tcx,
            ),
            Some(raw_i32())
        );
    })
    .unwrap();
}

#[test]
fn target_field_type_substitutes_evaluated_generic_base_arguments() {
    let source = r#"
struct Generic<T> { value: T }
unsafe fn update(holder: *mut Generic<*mut i32>, rhs: *mut i32) {
    (*holder).value = rhs;
}
"#;
    run_compiler_on_str(source, |tcx| {
        let mut surface = utils::ast::parse_crate(source.to_owned());
        let mut mapper = utils::ir::AstToHirMapper::new(tcx);
        mapper.map_crate_to_mod(&mut surface, tcx.hir_root_module(), false);
        let ast_to_hir = mapper.ast_to_hir;
        let item = surface
            .items
            .iter()
            .find(|item| {
                item.kind
                    .ident()
                    .is_some_and(|ident| ident.name.as_str() == "update")
            })
            .unwrap();
        let ItemKind::Fn(box function) = &item.kind else { unreachable!() };
        let StmtKind::Semi(assignment) = &function.body.as_ref().unwrap().stmts[0].kind else {
            unreachable!()
        };
        let ExprKind::Assign(left, _, _) = &assignment.kind else { unreachable!() };
        let ExprKind::Field(base, field) = &left.kind else { unreachable!() };
        let hir_base = ast_to_hir.get_expr(base.id, tcx).unwrap();
        let mut target_base = semantic_type_tree(
            tcx.typeck(hir_base.hir_id.owner).expr_ty(hir_base),
            &ast_to_hir,
            tcx,
        )
        .unwrap();
        let primitive = TypeTree::Primitive { name: "i32".into() };
        let target_argument = TypeTree::Adt {
            adt_kind: AdtKind::Enum,
            identity: AdtIdentity::External {
                crate_name: "core".into(),
                path: vec!["option".into(), "Option".into()],
            },
            arguments: vec![TypeTree::Reference {
                mutability: RefMutability::Shared,
                pointee: Box::new(primitive),
            }],
        };
        let TypeTree::Adt { arguments, .. } = &mut target_base else { unreachable!() };
        *arguments = vec![target_argument.clone()];
        assert_eq!(
            target_field_type(base, field.name, target_base, &ast_to_hir, tcx),
            Some(target_argument)
        );
    })
    .unwrap();
}

#[test]
fn rule_selection_materialization_and_statement_installation_are_integrated() {
    let source = "pub unsafe fn f(p: *mut i32) -> bool { p.is_null() }";
    run_compiler_on_str(source, |tcx| {
        let mut surface = utils::ast::parse_crate(source.to_owned());
        let mut mapper = utils::ir::AstToHirMapper::new(tcx);
        mapper.map_crate_to_mod(&mut surface, tcx.hir_root_module(), false);
        let ast_to_hir = mapper.ast_to_hir;
        let function = local_def("f", tcx);
        let mut decisions = tools_pointer_decisions(tcx);
        decisions
            .signatures
            .data
            .get_mut(&function)
            .unwrap()
            .input_decs[0] = Some(PtrKind::OptRef(false));
        let mut item = surface.items[0].clone();
        annotate_function(&mut item, &FxHashSet::default());
        let catalog = rule_binding_catalog(&item, function, &decisions, &ast_to_hir, tcx);
        assert_eq!(catalog.len(), 1);
        let ItemKind::Fn(box body) = &item.kind else { unreachable!() };
        let regions = select_rule_regions(
            &body.body.as_ref().unwrap().stmts[0],
            &catalog,
            &ast_to_hir,
            tcx,
        )
        .unwrap();
        let [region] = &regions[..] else { panic!("expected one selected pointer region") };
        let [_anchor] = &region.observation.pointer_anchors[..] else {
            panic!("expected one pointer anchor")
        };
        let mut observation = region.observation.clone();
        observation.target_expression = serde_json::from_value(serde_json::json!({
            "kind": "literal",
            "value": {"kind": "bool", "value": false}
        }))
        .unwrap();
        let document = crate::ObservationDocument {
            schema_version: crate::OBSERVATION_SCHEMA_VERSION,
            printf_observations: vec![],
            observations: vec![observation.clone(), observation],
        };
        let mut rule = crate::synthesize_rules(&[document]).unwrap();
        assert_eq!(rule.rules.len(), 1);
        let mut unavailable = rule.rules[0].clone();
        unavailable.target_pattern = crate::RuleExpression::Call {
            callee: Box::new(crate::RuleExpression::Path {
                value: crate::RuleValueIdentity::External {
                    crate_name: "unavailable_crate".into(),
                    path: vec!["unspellable".into()],
                },
            }),
            arguments: vec![crate::RuleExpression::Path {
                value: crate::RuleValueIdentity::Variable {
                    sort: crate::VariableSort::Anchor,
                    index: 0,
                },
            }],
        };
        rule.rules.push(unavailable);
        let boolean = |value| crate::RuleExpression::Literal {
            value: crate::RuleLiteral::Bool { value },
        };
        let tail = |expression| crate::RuleBlock {
            statements: vec![crate::RuleStatement::Expression {
                expression,
                semicolon: false,
            }],
        };
        let mut unsupported_shape = rule.rules[0].clone();
        unsupported_shape.target_pattern = crate::RuleExpression::Unary {
            operator: UnaryOperator::Not,
            operand: Box::new(crate::RuleExpression::If {
                condition: Box::new(boolean(true)),
                then: tail(boolean(true)),
                else_expression: Some(Box::new(boolean(false))),
            }),
        };
        rule.rules.push(unsupported_shape);
        let mut target = item.clone();
        let type_speller = TypeSpeller::new(function, &ast_to_hir, tcx);
        let applied = apply_rule_set(
            &item,
            &mut target,
            &BTreeSet::from([0]),
            &rule,
            function,
            &decisions,
            &ast_to_hir,
            &type_speller,
            tcx,
        )
        .unwrap();
        assert_eq!(applied, BTreeSet::from([0]));
        let rendered = pprust::item_to_string(&target);
        assert!(rendered.contains("false"), "{rendered}");
        assert!(!rendered.contains("is_null"), "{rendered}");
    })
    .unwrap();
}

#[test]
fn foreign_rules_reuse_matched_rust_spelling_instead_of_link_symbols() {
    let source = r#"
unsafe extern "C" {
    #[link_name = "c_ping"]
    fn rust_ping(value: i32) -> i32;
}
pub unsafe fn f() -> i32 { rust_ping(1) }
"#;
    let foreign = || crate::RuleExpression::Path {
        value: crate::RuleValueIdentity::ForeignFunction {
            symbol: "c_ping".into(),
        },
    };
    let integer = |value: &str| crate::RuleExpression::Literal {
        value: crate::RuleLiteral::Integer {
            value: crate::RuleIntegerMagnitude::Fixed(value.into()),
            ty: "i32".into(),
        },
    };
    let call = |value: &str| crate::RuleExpression::Call {
        callee: Box::new(foreign()),
        arguments: vec![integer(value)],
    };
    let primitive = crate::RuleTypeTree::Primitive { name: "i32".into() };
    let rules = crate::RuleDocument {
        schema_version: 1,
        printf_rules: vec![],
        rules: vec![crate::Rule {
            source_pattern: call("1"),
            target_pattern: call("2"),
            pointer_anchors: vec![],
            lhs: false,
            source_type: primitive.clone(),
            source_adjusted_type: primitive.clone(),
            target_type: primitive.clone(),
            target_adjusted_type: primitive,
        }],
    };
    run_compiler_on_str(source, |tcx| {
        let records = make_skeletons_with_rules(source, Some(&rules), tcx).unwrap();
        let record = function(&records, "f");
        assert_eq!(
            record.applied.skeleton,
            "pub unsafe fn f() -> i32 {\n    #[proctor(0)]\n    rust_ping(2i32)\n}"
        );
        assert_eq!(
            record.applied.statement_dispositions[0].disposition,
            crate::StatementDispositionKind::RuleApplied
        );
        assert!(!record.applied.needs_transformation);
    })
    .unwrap();
}

#[test]
fn target_only_foreign_identity_uses_one_accessible_local_declaration() {
    let source = r#"
mod ffi {
    unsafe extern "C" {
        #[link_name = "source_ping"]
        pub fn source_rust(value: i32) -> i32;
        #[link_name = "c_ping"]
        pub fn target_rust(value: i32) -> i32;
    }
}
pub unsafe fn f() -> i32 { ffi::source_rust(1) }
"#;
    let call = |symbol: &str| crate::RuleExpression::Call {
        callee: Box::new(crate::RuleExpression::Path {
            value: crate::RuleValueIdentity::ForeignFunction {
                symbol: symbol.into(),
            },
        }),
        arguments: vec![crate::RuleExpression::Literal {
            value: crate::RuleLiteral::Integer {
                value: crate::RuleIntegerMagnitude::Fixed("1".into()),
                ty: "i32".into(),
            },
        }],
    };
    let primitive = crate::RuleTypeTree::Primitive { name: "i32".into() };
    let rules = crate::RuleDocument {
        schema_version: 1,
        printf_rules: vec![],
        rules: vec![crate::Rule {
            source_pattern: call("source_ping"),
            target_pattern: call("c_ping"),
            pointer_anchors: vec![],
            lhs: false,
            source_type: primitive.clone(),
            source_adjusted_type: primitive.clone(),
            target_type: primitive.clone(),
            target_adjusted_type: primitive,
        }],
    };
    run_compiler_on_str(source, |tcx| {
        let records = make_skeletons_with_rules(source, Some(&rules), tcx).unwrap();
        let record = function(&records, "f");
        assert_eq!(
            record.applied.skeleton,
            "pub unsafe fn f() -> i32 {\n    #[proctor(0)]\n    crate::ffi::target_rust(1i32)\n}"
        );
        assert_eq!(
            record.applied.statement_dispositions[0].disposition,
            crate::StatementDispositionKind::RuleApplied
        );
    })
    .unwrap();
}

#[test]
fn equal_foreign_symbols_keep_occurrence_specific_source_spelling() {
    let source = r#"
mod left {
    unsafe extern "C" {
        #[link_name = "c_ping"]
        pub fn left_rust(value: i32) -> i32;
    }
}
mod right {
    unsafe extern "C" {
        #[link_name = "c_ping"]
        pub fn right_rust(value: i32) -> i32;
    }
}
unsafe extern "C" { fn combine(left: i32, right: i32) -> i32; }
use left::left_rust as first;
use right::right_rust as second;
pub unsafe fn f() -> i32 { combine(first(1), second(2)) }
"#;
    let integer = |value: &str| crate::RuleExpression::Literal {
        value: crate::RuleLiteral::Integer {
            value: crate::RuleIntegerMagnitude::Fixed(value.into()),
            ty: "i32".into(),
        },
    };
    let foreign_call = |symbol: &str, argument| crate::RuleExpression::Call {
        callee: Box::new(crate::RuleExpression::Path {
            value: crate::RuleValueIdentity::ForeignFunction {
                symbol: symbol.into(),
            },
        }),
        arguments: vec![argument],
    };
    let first = foreign_call("c_ping", integer("1"));
    let second = foreign_call("c_ping", integer("2"));
    let source_pattern = crate::RuleExpression::Call {
        callee: Box::new(crate::RuleExpression::Path {
            value: crate::RuleValueIdentity::ForeignFunction {
                symbol: "combine".into(),
            },
        }),
        arguments: vec![first, second.clone()],
    };
    let primitive = crate::RuleTypeTree::Primitive { name: "i32".into() };
    let occurrence_rule = crate::Rule {
        source_pattern,
        target_pattern: second,
        pointer_anchors: vec![],
        lhs: false,
        source_type: primitive.clone(),
        source_adjusted_type: primitive.clone(),
        target_type: primitive.clone(),
        target_adjusted_type: primitive,
    };
    let irrelevant = anchorless_foreign_rule("combine", fixed_integer_rule("99"));
    for rules in [
        vec![occurrence_rule.clone(), irrelevant.clone()],
        vec![irrelevant.clone(), occurrence_rule.clone()],
    ] {
        let document = crate::RuleDocument {
            schema_version: 1,
            printf_rules: vec![],
            rules,
        };
        run_compiler_on_str(source, |tcx| {
            let records = make_skeletons_with_rules(source, Some(&document), tcx).unwrap();
            let applied = &function(&records, "f").applied;
            assert_eq!(
                applied.skeleton,
                "pub unsafe fn f() -> i32 {\n    #[proctor(0)]\n    second(2)\n}"
            );
            assert_eq!(
                applied.statement_dispositions[0].disposition,
                crate::StatementDispositionKind::RuleApplied
            );
        })
        .unwrap();
    }
}

fn fixed_integer_rule(value: &str) -> crate::RuleExpression {
    crate::RuleExpression::Literal {
        value: crate::RuleLiteral::Integer {
            value: crate::RuleIntegerMagnitude::Fixed(value.into()),
            ty: "i32".into(),
        },
    }
}

fn foreign_call_rule(symbol: &str, argument: &str) -> crate::RuleExpression {
    crate::RuleExpression::Call {
        callee: Box::new(crate::RuleExpression::Path {
            value: crate::RuleValueIdentity::ForeignFunction {
                symbol: symbol.into(),
            },
        }),
        arguments: vec![fixed_integer_rule(argument)],
    }
}

fn anchorless_foreign_rule(
    source_symbol: &str,
    target_pattern: crate::RuleExpression,
) -> crate::Rule {
    let primitive = crate::RuleTypeTree::Primitive { name: "i32".into() };
    crate::Rule {
        source_pattern: foreign_call_rule(source_symbol, "1"),
        target_pattern,
        pointer_anchors: vec![],
        lhs: false,
        source_type: primitive.clone(),
        source_adjusted_type: primitive.clone(),
        target_type: primitive.clone(),
        target_adjusted_type: primitive,
    }
}

#[test]
fn foreign_static_targets_keep_their_bare_symbol_spelling() {
    let source = r#"
unsafe extern "C" {
    #[link_name = "c_value"]
    static RUST_VALUE: i32;
    fn consume(value: i32) -> i32;
}
pub unsafe fn f() -> i32 { consume(RUST_VALUE) }
"#;
    let primitive = crate::RuleTypeTree::Primitive { name: "i32".into() };
    let foreign_static = crate::RuleExpression::Path {
        value: crate::RuleValueIdentity::ForeignStatic {
            symbol: "c_value".into(),
        },
    };
    let document = crate::RuleDocument {
        schema_version: 1,
        printf_rules: vec![],
        rules: vec![crate::Rule {
            source_pattern: crate::RuleExpression::Call {
                callee: Box::new(crate::RuleExpression::Path {
                    value: crate::RuleValueIdentity::ForeignFunction {
                        symbol: "consume".into(),
                    },
                }),
                arguments: vec![foreign_static.clone()],
            },
            target_pattern: foreign_static,
            pointer_anchors: vec![],
            lhs: false,
            source_type: primitive.clone(),
            source_adjusted_type: primitive.clone(),
            target_type: primitive.clone(),
            target_adjusted_type: primitive,
        }],
    };
    run_compiler_on_str(source, |tcx| {
        let records = make_skeletons_with_rules(source, Some(&document), tcx).unwrap();
        let record = function(&records, "f");
        assert_eq!(
            record.applied.skeleton,
            "pub unsafe fn f() -> i32 {\n    #[proctor(0)]\n    c_value\n}"
        );
        assert_eq!(
            record.applied.statement_dispositions[0].disposition,
            crate::StatementDispositionKind::RuleApplied
        );
    })
    .unwrap();
}

#[test]
fn pointer_valued_foreign_root_requires_supported_target_context() {
    let source = r#"
unsafe extern "C" { fn allocate() -> *mut i32; }
unsafe fn consume(_: *mut i32) {}
pub unsafe fn discarded() { allocate(); }
pub unsafe fn returned() -> *mut i32 { allocate() }
pub unsafe fn argument() { consume(allocate()); }
"#;
    run_compiler_on_str(source, |tcx| {
        let mut surface = utils::ast::parse_crate(source.to_owned());
        let mut mapper = utils::ir::AstToHirMapper::new(tcx);
        mapper.map_crate_to_mod(&mut surface, tcx.hir_root_module(), false);
        let ast_to_hir = mapper.ast_to_hir;
        let mut decisions = tools_pointer_decisions(tcx);
        decisions
            .signatures
            .data
            .get_mut(&local_def("returned", tcx))
            .unwrap()
            .output_dec = Some(PtrKind::OptRef(true));
        decisions
            .signatures
            .data
            .get_mut(&local_def("consume", tcx))
            .unwrap()
            .input_decs[0] = Some(PtrKind::OptRef(true));

        let primitive = crate::RuleTypeTree::Primitive { name: "i32".into() };
        let raw = crate::RuleTypeTree::RawPointer {
            mutability: crate::RawMutability::Mut,
            pointee: Box::new(primitive.clone()),
        };
        let optional_reference = crate::RuleTypeTree::Adt {
            adt_kind: crate::AdtKind::Enum,
            identity: crate::RuleAdtIdentity::External {
                crate_name: "core".into(),
                path: vec!["option".into(), "Option".into()],
            },
            arguments: vec![crate::RuleTypeTree::Reference {
                mutability: crate::RefMutability::Mutable,
                pointee: Box::new(primitive),
            }],
        };
        let allocate = crate::RuleExpression::Call {
            callee: Box::new(crate::RuleExpression::Path {
                value: crate::RuleValueIdentity::ForeignFunction {
                    symbol: "allocate".into(),
                },
            }),
            arguments: vec![],
        };
        let document = crate::RuleDocument {
            schema_version: 1,
            printf_rules: vec![],
            rules: vec![crate::Rule {
                source_pattern: allocate.clone(),
                target_pattern: allocate,
                pointer_anchors: vec![],
                lhs: false,
                source_type: raw.clone(),
                source_adjusted_type: raw.clone(),
                target_type: raw,
                target_adjusted_type: optional_reference,
            }],
        };

        let expected = [
            (
                "discarded",
                BTreeSet::new(),
                "pub unsafe fn discarded() {\n\n    #[proctor(0)]\n    allocate();\n}",
                crate::SkeletonView {
                    skeleton: "pub unsafe fn discarded() {\n    #[proctor(0)]\n    todo!();\n}"
                        .into(),
                    needs_transformation: true,
                    statement_dispositions: vec![crate::StatementDisposition {
                        label: 0,
                        disposition: crate::StatementDispositionKind::Transform,
                        children: vec![],
                    }],
                    statement_pair_metadata: vec![crate::StatementPairMetadata {
                        label: 0,
                        before_statement: "#[proctor(0)]\nallocate();".into(),
                        printf_template: None,
                        pointer_variables_complete: true,
                        pointer_variables: vec![],
                    }],
                },
            ),
            (
                "returned",
                BTreeSet::from([0]),
                "pub unsafe fn returned() -> *mut i32 {\n\n    #[proctor(0)]\n    allocate()\n}",
                crate::SkeletonView {
                    skeleton: "pub unsafe fn returned() -> Option<&mut i32> {\n    #[proctor(0)]\n    allocate()\n}".into(),
                    needs_transformation: false,
                    statement_dispositions: vec![crate::StatementDisposition {
                        label: 0,
                        disposition: crate::StatementDispositionKind::RuleApplied,
                        children: vec![],
                    }],
                    statement_pair_metadata: vec![],
                },
            ),
            (
                "argument",
                BTreeSet::from([0]),
                "pub unsafe fn argument() {\n\n    #[proctor(0)]\n    consume(allocate());\n}",
                crate::SkeletonView {
                    skeleton: "pub unsafe fn argument() {\n    #[proctor(0)]\n    consume(allocate());\n}".into(),
                    needs_transformation: false,
                    statement_dispositions: vec![crate::StatementDisposition {
                        label: 0,
                        disposition: crate::StatementDispositionKind::RuleApplied,
                        children: vec![],
                    }],
                    statement_pair_metadata: vec![],
                },
            ),
        ];
        for (name, expected_disposition, expected_statement, expected_view) in expected {
            let function = local_def(name, tcx);
            let mut item = surface
                .items
                .iter()
                .find(|item| {
                    item.kind
                        .ident()
                        .is_some_and(|ident| ident.name.as_str() == name)
                })
                .unwrap()
                .clone();
            let record_item = item.clone();
            annotate_function(&mut item, &FxHashSet::default());
            let mut target = item.clone();
            let speller = TypeSpeller::new(function, &ast_to_hir, tcx);
            let applied = apply_rule_set(
                &item,
                &mut target,
                &BTreeSet::from([0]),
                &document,
                function,
                &decisions,
                &ast_to_hir,
                &speller,
                tcx,
            )
            .unwrap();
            assert_eq!(applied, expected_disposition, "{name}");
            assert_eq!(
                pprust::item_to_string(&target),
                expected_statement,
                "{name}"
            );
            let record = make_function_record(
                SurfaceItem {
                    id: 0,
                    path: name.into(),
                    item: record_item,
                    def_id: function,
                    kind: ItemKindName::Fn,
                },
                &ast_to_hir,
                &FxHashMap::default(),
                &decisions,
                &PreservationDecisionOverrides::default(),
                Some(&document),
                tcx,
            )
            .unwrap();
            let ItemRecord::Function(record) = record else { unreachable!() };
            assert_eq!(record.applied, expected_view, "{name}");
        }
    })
    .unwrap();
}

#[test]
fn matched_foreign_paths_retain_module_alias_and_plain_spellings() {
    let fixtures = [
        (
            r#"
mod ffi {
    unsafe extern "C" {
        #[link_name = "c_ping"]
        pub fn rust_ping(value: i32) -> i32;
    }
}
pub unsafe fn f() -> i32 { ffi::rust_ping(1) }
"#,
            "ffi::rust_ping(2i32)",
        ),
        (
            r#"
mod ffi {
    unsafe extern "C" {
        #[link_name = "c_ping"]
        pub fn rust_ping(value: i32) -> i32;
    }
}
use ffi::rust_ping as alias;
pub unsafe fn f() -> i32 { alias(1) }
"#,
            "alias(2i32)",
        ),
        (
            r#"
unsafe extern "C" { fn ping(value: i32) -> i32; }
pub unsafe fn f() -> i32 { ping(1) }
"#,
            "ping(2i32)",
        ),
    ];
    for (source, expected) in fixtures {
        let symbol = if expected.starts_with("ping") {
            "ping"
        } else {
            "c_ping"
        };
        let rules = crate::RuleDocument {
            schema_version: 1,
            printf_rules: vec![],
            rules: vec![anchorless_foreign_rule(
                symbol,
                foreign_call_rule(symbol, "2"),
            )],
        };
        run_compiler_on_str(source, |tcx| {
            let records = make_skeletons_with_rules(source, Some(&rules), tcx).unwrap();
            let record = function(&records, "f");
            assert_eq!(
                record.applied.skeleton,
                format!("pub unsafe fn f() -> i32 {{\n    #[proctor(0)]\n    {expected}\n}}")
            );
            assert_eq!(
                record.applied.statement_dispositions,
                vec![crate::StatementDisposition {
                    label: 0,
                    disposition: crate::StatementDispositionKind::RuleApplied,
                    children: vec![],
                }]
            );
            assert!(!record.applied.needs_transformation);
            assert!(record.applied.statement_pair_metadata.is_empty());
        })
        .unwrap();
    }
}

#[test]
fn unavailable_foreign_declarations_fall_back_without_emitting_link_symbols() {
    let fixtures = [
        r#"
mod ffi {
    unsafe extern "C" {
        #[link_name = "source_ping"]
        pub fn source_rust(value: i32) -> i32;
    }
}
pub unsafe fn f() -> i32 { ffi::source_rust(1) }
"#,
        r#"
mod ffi {
    unsafe extern "C" {
        #[link_name = "source_ping"]
        pub fn source_rust(value: i32) -> i32;
    }
}
mod left { unsafe extern "C" { #[link_name = "c_ping"] pub fn left_rust(value: i32) -> i32; } }
mod right { unsafe extern "C" { #[link_name = "c_ping"] pub fn right_rust(value: i32) -> i32; } }
pub unsafe fn f() -> i32 { ffi::source_rust(1) }
"#,
        r#"
mod ffi {
    unsafe extern "C" {
        #[link_name = "source_ping"]
        pub fn source_rust(value: i32) -> i32;
    }
}
mod hidden { unsafe extern "C" { #[link_name = "c_ping"] fn hidden_rust(value: i32) -> i32; } }
pub unsafe fn f() -> i32 { ffi::source_rust(1) }
"#,
    ];
    let preferred = anchorless_foreign_rule("source_ping", foreign_call_rule("c_ping", "1"));
    let fallback = anchorless_foreign_rule("source_ping", fixed_integer_rule("7"));
    for source in fixtures {
        for rules in [
            vec![preferred.clone(), fallback.clone()],
            vec![fallback.clone(), preferred.clone()],
        ] {
            let document = crate::RuleDocument {
                schema_version: 1,
                printf_rules: vec![],
                rules,
            };
            run_compiler_on_str(source, |tcx| {
                let records = make_skeletons_with_rules(source, Some(&document), tcx).unwrap();
                let record = function(&records, "f");
                assert_eq!(
                    record.applied.skeleton,
                    "pub unsafe fn f() -> i32 {\n    #[proctor(0)]\n    7i32\n}"
                );
                assert_eq!(
                    record.applied.statement_dispositions,
                    vec![crate::StatementDisposition {
                        label: 0,
                        disposition: crate::StatementDispositionKind::RuleApplied,
                        children: vec![],
                    }]
                );
            })
            .unwrap();
        }

        let document = crate::RuleDocument {
            schema_version: 1,
            printf_rules: vec![],
            rules: vec![preferred.clone()],
        };
        run_compiler_on_str(source, |tcx| {
            let records = make_skeletons_with_rules(source, Some(&document), tcx).unwrap();
            let record = function(&records, "f");
            assert_eq!(record.applied, record.baseline);
            assert_eq!(record.applied.transform_labels(), [0]);
            assert_eq!(
                record.applied.statement_dispositions[0].disposition,
                crate::StatementDispositionKind::Transform
            );
        })
        .unwrap();
    }
}

#[test]
fn structurally_invalid_foreign_winner_falls_back_without_touching_preserved_sibling() {
    let source = r#"
unsafe extern "C" { fn ping() -> i32; }
pub unsafe fn f() {
    let value: i32 = ping();
    let keep: i32 = 1;
}
"#;
    let primitive = crate::RuleTypeTree::Primitive { name: "i32".into() };
    let ping = crate::RuleExpression::Call {
        callee: Box::new(crate::RuleExpression::Path {
            value: crate::RuleValueIdentity::ForeignFunction {
                symbol: "ping".into(),
            },
        }),
        arguments: vec![],
    };
    let rule = |target_pattern| crate::Rule {
        source_pattern: ping.clone(),
        target_pattern,
        pointer_anchors: vec![],
        lhs: false,
        source_type: primitive.clone(),
        source_adjusted_type: primitive.clone(),
        target_type: primitive.clone(),
        target_adjusted_type: primitive.clone(),
    };
    let invalid = rule(crate::RuleExpression::Array {
        elements: vec![crate::RuleExpression::While {
            condition: Box::new(crate::RuleExpression::Literal {
                value: crate::RuleLiteral::Bool { value: true },
            }),
            body: crate::RuleBlock { statements: vec![] },
        }],
    });
    let fallback = rule(fixed_integer_rule("7"));
    for rules in [
        vec![invalid.clone(), fallback.clone()],
        vec![fallback.clone(), invalid.clone()],
    ] {
        let document = crate::RuleDocument {
            schema_version: 1,
            printf_rules: vec![],
            rules,
        };
        run_compiler_on_str(source, |tcx| {
            let records = make_skeletons_with_rules(source, Some(&document), tcx).unwrap();
            let record = function(&records, "f");
            assert_eq!(
                record.applied.skeleton,
                "pub unsafe fn f() {\n    #[proctor(0)]\n    let mut value: i32 = 7i32;\n    #[proctor(1)]\n    let mut keep: i32 = 1;\n}"
            );
            assert_eq!(
                record.applied.statement_dispositions,
                vec![
                    crate::StatementDisposition {
                        label: 0,
                        disposition: crate::StatementDispositionKind::RuleApplied,
                        children: vec![],
                    },
                    crate::StatementDisposition {
                        label: 1,
                        disposition: crate::StatementDispositionKind::Preserve,
                        children: vec![],
                    },
                ]
            );
            assert!(!record.applied.needs_transformation);
            assert!(record.applied.statement_pair_metadata.is_empty());
        })
        .unwrap();
    }

    let document = crate::RuleDocument {
        schema_version: 1,
        printf_rules: vec![],
        rules: vec![invalid],
    };
    run_compiler_on_str(source, |tcx| {
        let records = make_skeletons_with_rules(source, Some(&document), tcx).unwrap();
        let record = function(&records, "f");
        assert_eq!(
            record.annotated_source,
            "pub unsafe fn f() {\n    #[proctor(0)]\n    let mut value: i32 = ping();\n    #[proctor(1)]\n    let mut keep: i32 = 1;\n}"
        );
        assert_eq!(
            record.baseline.skeleton,
            "pub unsafe fn f() {\n    #[proctor(0)]\n    let mut value: i32 = todo!();\n    #[proctor(1)]\n    let mut keep: i32 = 1;\n}"
        );
        assert_eq!(record.applied, record.baseline);
        assert_eq!(
            record.applied.statement_dispositions,
            vec![
                crate::StatementDisposition {
                    label: 0,
                    disposition: crate::StatementDispositionKind::Transform,
                    children: vec![],
                },
                crate::StatementDisposition {
                    label: 1,
                    disposition: crate::StatementDispositionKind::Preserve,
                    children: vec![],
                },
            ]
        );
        assert_eq!(record.applied.statement_pair_metadata.len(), 1);
    })
    .unwrap();
}

#[test]
fn maximal_foreign_parent_owns_transferred_anchor_context_without_child_fallback() {
    let source = r#"
unsafe extern "C" { fn read_one(pointer: *const i32) -> i32; }
pub unsafe fn f(pointer: *const i32) -> i32 { read_one(pointer) }
"#;
    let primitive = crate::RuleTypeTree::Primitive { name: "i32".into() };
    let raw = crate::RuleTypeTree::RawPointer {
        mutability: crate::RawMutability::Const,
        pointee: Box::new(primitive.clone()),
    };
    let reference = crate::RuleTypeTree::Reference {
        mutability: crate::RefMutability::Shared,
        pointee: Box::new(primitive.clone()),
    };
    let optional_reference = crate::RuleTypeTree::Adt {
        adt_kind: crate::AdtKind::Enum,
        identity: crate::RuleAdtIdentity::External {
            crate_name: "core".into(),
            path: vec!["option".into(), "Option".into()],
        },
        arguments: vec![reference],
    };
    let anchor_identity = crate::RuleValueIdentity::Variable {
        sort: crate::VariableSort::Anchor,
        index: 0,
    };
    let anchor_path = crate::RuleExpression::Path {
        value: anchor_identity,
    };
    let anchors = vec![crate::RulePointerAnchor {
        id: crate::RuleVariable::new(crate::VariableSort::Anchor, 0),
        source_type: raw.clone(),
        target_type: optional_reference.clone(),
    }];
    let parent = crate::Rule {
        source_pattern: crate::RuleExpression::Call {
            callee: Box::new(crate::RuleExpression::Path {
                value: crate::RuleValueIdentity::ForeignFunction {
                    symbol: "read_one".into(),
                },
            }),
            arguments: vec![anchor_path.clone()],
        },
        target_pattern: fixed_integer_rule("7"),
        pointer_anchors: anchors.clone(),
        lhs: false,
        source_type: primitive.clone(),
        source_adjusted_type: primitive.clone(),
        target_type: primitive.clone(),
        target_adjusted_type: primitive.clone(),
    };
    let child = crate::Rule {
        source_pattern: anchor_path.clone(),
        target_pattern: anchor_path,
        pointer_anchors: anchors,
        lhs: false,
        source_type: raw.clone(),
        source_adjusted_type: raw,
        target_type: optional_reference.clone(),
        target_adjusted_type: optional_reference,
    };
    for rules in [
        vec![parent.clone(), child.clone()],
        vec![child.clone(), parent.clone()],
    ] {
        let document = crate::RuleDocument {
            schema_version: 1,
            printf_rules: vec![],
            rules,
        };
        run_compiler_on_str(source, |tcx| {
            let records = make_skeletons_with_rules(source, Some(&document), tcx).unwrap();
            let record = function(&records, "f");
            assert_eq!(
                record.applied,
                crate::SkeletonView {
                    skeleton: "pub unsafe fn f(mut pointer: Option<&i32>) -> i32 {\n    #[proctor(0)]\n    7i32\n}".into(),
                    needs_transformation: false,
                    statement_dispositions: vec![crate::StatementDisposition {
                        label: 0,
                        disposition: crate::StatementDispositionKind::RuleApplied,
                        children: vec![],
                    }],
                    statement_pair_metadata: vec![],
                }
            );
        })
        .unwrap();
    }

    let child_only = crate::RuleDocument {
        schema_version: 1,
        printf_rules: vec![],
        rules: vec![child],
    };
    run_compiler_on_str(source, |tcx| {
        let records = make_skeletons_with_rules(source, Some(&child_only), tcx).unwrap();
        let record = function(&records, "f");
        assert_eq!(
            record.applied,
            crate::SkeletonView {
                skeleton: "pub unsafe fn f(mut pointer: Option<&i32>) -> i32 {\n    #[proctor(0)]\n    todo!()\n}".into(),
                needs_transformation: true,
                statement_dispositions: vec![crate::StatementDisposition {
                    label: 0,
                    disposition: crate::StatementDispositionKind::Transform,
                    children: vec![],
                }],
                statement_pair_metadata: vec![crate::StatementPairMetadata {
                    label: 0,
                    before_statement: "#[proctor(0)]\nread_one(pointer)".into(),
                    printf_template: None,
                    pointer_variables_complete: true,
                    pointer_variables: vec![crate::PointerVariableMetadata {
                        name: "pointer".into(),
                        origin: crate::PointerVariableOrigin::Parameter { index: 0 },
                        before_type: "*const i32".into(),
                        selected_target_type: "Option<&i32>".into(),
                        before_type_is_inferred: false,
                    }],
                }],
            }
        );
        assert_eq!(record.applied, record.baseline);
    })
    .unwrap();
}

#[test]
fn unrelated_transformed_restricted_conditional_does_not_block_rule_application() {
    let source = r#"
extern "C" { fn opaque_value() -> bool; }
pub unsafe fn mixed(p: *mut i32, flag: bool) -> bool {
    let _conditional = Some(if flag { opaque_value() } else { false });
    p.is_null()
}
"#;
    run_compiler_on_str(source, |tcx| {
        let mut surface = utils::ast::parse_crate(source.to_owned());
        let mut mapper = utils::ir::AstToHirMapper::new(tcx);
        mapper.map_crate_to_mod(&mut surface, tcx.hir_root_module(), false);
        let ast_to_hir = mapper.ast_to_hir;
        let function = local_def("mixed", tcx);
        let mut decisions = tools_pointer_decisions(tcx);
        decisions
            .signatures
            .data
            .get_mut(&function)
            .unwrap()
            .input_decs[0] = Some(PtrKind::OptRef(false));
        let mut item = surface
            .items
            .iter()
            .find(|item| {
                item.kind
                    .ident()
                    .is_some_and(|ident| ident.name.as_str() == "mixed")
            })
            .unwrap()
            .clone();
        let opaque_nested_ifs = collect_opaque_nested_ifs(&item, "mixed").unwrap();
        annotate_function(&mut item, &opaque_nested_ifs);
        let classification = classify_function_statements(
            &item,
            &opaque_nested_ifs,
            &ast_to_hir,
            &decisions,
            &PreservationDecisionOverrides::default(),
            tcx,
        );
        assert_eq!(classification.transformed, BTreeSet::from([0, 1]));

        let catalog = rule_binding_catalog(&item, function, &decisions, &ast_to_hir, tcx);
        let ItemKind::Fn(box body) = &item.kind else { unreachable!() };
        let regions = select_rule_regions(
            &body.body.as_ref().unwrap().stmts[1],
            &catalog,
            &ast_to_hir,
            tcx,
        )
        .unwrap();
        let [region] = &regions[..] else { panic!("expected one selected pointer region") };
        let mut observation = region.observation.clone();
        observation.target_expression = serde_json::from_value(serde_json::json!({
            "kind": "literal",
            "value": {"kind": "bool", "value": false}
        }))
        .unwrap();
        let rules = crate::synthesize_rules(&[crate::ObservationDocument {
            schema_version: crate::OBSERVATION_SCHEMA_VERSION,
            printf_observations: vec![],
            observations: vec![observation.clone(), observation],
        }])
        .unwrap();
        let mut target = item.clone();
        let type_speller = TypeSpeller::new(function, &ast_to_hir, tcx);
        let applied = apply_rule_set(
            &item,
            &mut target,
            &classification.transformed,
            &rules,
            function,
            &decisions,
            &ast_to_hir,
            &type_speller,
            tcx,
        )
        .unwrap();
        assert_eq!(applied, BTreeSet::from([1]));
        let rendered = pprust::item_to_string(&target);
        assert!(rendered.contains("Some(if flag { opaque_value() } else { false })"));
        assert!(!rendered.contains("is_null"), "{rendered}");
    })
    .unwrap();
}

#[test]
fn nonmatching_rules_leave_transformed_restricted_conditional_view_unchanged() {
    let source = r#"
extern "C" { fn opaque_value() -> bool; }
pub unsafe fn rule_source(p: *mut i32) -> bool { p.is_null() }
pub unsafe fn no_match(flag: bool) -> Option<bool> {
    Some(if flag { opaque_value() } else { false })
}
"#;
    run_compiler_on_str(source, |tcx| {
        let mut surface = utils::ast::parse_crate(source.to_owned());
        let mut mapper = utils::ir::AstToHirMapper::new(tcx);
        mapper.map_crate_to_mod(&mut surface, tcx.hir_root_module(), false);
        let ast_to_hir = mapper.ast_to_hir;
        let function_id = local_def("rule_source", tcx);
        let mut decisions = tools_pointer_decisions(tcx);
        decisions
            .signatures
            .data
            .get_mut(&function_id)
            .unwrap()
            .input_decs[0] = Some(PtrKind::OptRef(false));
        let mut item = surface
            .items
            .iter()
            .find(|item| {
                item.kind
                    .ident()
                    .is_some_and(|ident| ident.name.as_str() == "rule_source")
            })
            .unwrap()
            .clone();
        annotate_function(&mut item, &FxHashSet::default());
        let catalog = rule_binding_catalog(&item, function_id, &decisions, &ast_to_hir, tcx);
        let ItemKind::Fn(box body) = &item.kind else { unreachable!() };
        let regions = select_rule_regions(
            &body.body.as_ref().unwrap().stmts[0],
            &catalog,
            &ast_to_hir,
            tcx,
        )
        .unwrap();
        let [region] = &regions[..] else { panic!("expected one selected pointer region") };
        let mut observation = region.observation.clone();
        observation.target_expression = serde_json::from_value(serde_json::json!({
            "kind": "literal",
            "value": {"kind": "bool", "value": false}
        }))
        .unwrap();
        let rules = crate::synthesize_rules(&[crate::ObservationDocument {
            schema_version: crate::OBSERVATION_SCHEMA_VERSION,
            printf_observations: vec![],
            observations: vec![observation.clone(), observation],
        }])
        .unwrap();
        assert_eq!(rules.rules.len(), 1);

        let records = make_skeletons_with_rules(source, Some(&rules), tcx).unwrap();
        let no_match = function(&records, "no_match");
        assert_eq!(no_match.baseline.transform_labels(), [0]);
        assert_eq!(no_match.applied, no_match.baseline);
    })
    .unwrap();
}

#[test]
fn selected_region_dump_failure_keeps_a_multi_region_statement_unmodified() {
    let source = r#"
pub unsafe fn usable(p: *mut i32) { *p = 0; }
pub unsafe fn atomic(p: *mut i32, q: *mut i32) {
    *p = (*(q as *mut unsafe fn()), 0).1;
}
"#;
    run_compiler_on_str(source, |tcx| {
        let mut surface = utils::ast::parse_crate(source.to_owned());
        let mut mapper = utils::ir::AstToHirMapper::new(tcx);
        mapper.map_crate_to_mod(&mut surface, tcx.hir_root_module(), false);
        let ast_to_hir = mapper.ast_to_hir;
        let mut decisions = tools_pointer_decisions(tcx);
        let usable_id = local_def("usable", tcx);
        decisions
            .signatures
            .data
            .get_mut(&usable_id)
            .unwrap()
            .input_decs[0] = Some(PtrKind::Ref(true));
        let atomic_id = local_def("atomic", tcx);
        let atomic_signature = decisions.signatures.data.get_mut(&atomic_id).unwrap();
        atomic_signature.input_decs[0] = Some(PtrKind::Ref(true));
        atomic_signature.input_decs[1] = Some(PtrKind::Ref(true));

        let source_item = |name: &str| {
            surface
                .items
                .iter()
                .find(|item| {
                    item.kind
                        .ident()
                        .is_some_and(|ident| ident.name.as_str() == name)
                })
                .unwrap()
                .clone()
        };
        let mut usable = source_item("usable");
        annotate_function(&mut usable, &FxHashSet::default());
        let usable_catalog = rule_binding_catalog(&usable, usable_id, &decisions, &ast_to_hir, tcx);
        let ItemKind::Fn(box usable_function) = &usable.kind else { unreachable!() };
        let regions = select_rule_regions(
            &usable_function.body.as_ref().unwrap().stmts[0],
            &usable_catalog,
            &ast_to_hir,
            tcx,
        )
        .unwrap();
        let [region] = &regions[..] else { panic!("expected one usable region") };
        let anchor_id = region.observation.pointer_anchors[0].id.clone();
        let mut observation = region.observation.clone();
        observation.target_expression = crate::Expression::Path {
            value: crate::ValueIdentity::Binding { id: anchor_id },
        };
        let rules = crate::synthesize_rules(&[crate::ObservationDocument {
            schema_version: crate::OBSERVATION_SCHEMA_VERSION,
            printf_observations: vec![],
            observations: vec![observation.clone(), observation],
        }])
        .unwrap();
        assert_eq!(rules.rules.len(), 1);

        let mut usable_target = usable.clone();
        let usable_speller = TypeSpeller::new(usable_id, &ast_to_hir, tcx);
        assert_eq!(
            apply_rule_set(
                &usable,
                &mut usable_target,
                &BTreeSet::from([0]),
                &rules,
                usable_id,
                &decisions,
                &ast_to_hir,
                &usable_speller,
                tcx,
            )
            .unwrap(),
            BTreeSet::from([0]),
            "the rule used in the atomicity check must itself be applicable"
        );

        let mut atomic = source_item("atomic");
        annotate_function(&mut atomic, &FxHashSet::default());
        let atomic_catalog = rule_binding_catalog(&atomic, atomic_id, &decisions, &ast_to_hir, tcx);
        let ItemKind::Fn(box atomic_function) = &atomic.kind else { unreachable!() };
        assert!(
            select_rule_regions(
                &atomic_function.body.as_ref().unwrap().stmts[0],
                &atomic_catalog,
                &ast_to_hir,
                tcx,
            )
            .is_none(),
            "one selected generic-typed region must invalidate the complete statement dump"
        );
        let mut atomic_target = atomic.clone();
        let baseline = pprust::item_to_string(&atomic_target);
        let atomic_speller = TypeSpeller::new(atomic_id, &ast_to_hir, tcx);
        assert!(
            apply_rule_set(
                &atomic,
                &mut atomic_target,
                &BTreeSet::from([0]),
                &rules,
                atomic_id,
                &decisions,
                &ast_to_hir,
                &atomic_speller,
                tcx,
            )
            .unwrap()
            .is_empty(),
            "the statement disposition must remain transform"
        );
        assert_eq!(pprust::item_to_string(&atomic_target), baseline);
    })
    .unwrap();
}

#[test]
fn two_disjoint_rule_regions_install_together_independently_of_rule_order() {
    let source = r#"
unsafe extern "C" { fn ping(value: i32) -> i32; }
pub unsafe fn dual(p: *mut i32, q: *mut i32) -> (i32, i32, bool) {
    (*p, ping(1), !q.is_null())
}
"#;
    run_compiler_on_str(source, |tcx| {
        let mut surface = utils::ast::parse_crate(source.to_owned());
        let mut mapper = utils::ir::AstToHirMapper::new(tcx);
        mapper.map_crate_to_mod(&mut surface, tcx.hir_root_module(), false);
        let ast_to_hir = mapper.ast_to_hir;
        let function = local_def("dual", tcx);
        let mut decisions = tools_pointer_decisions(tcx);
        let signature = decisions.signatures.data.get_mut(&function).unwrap();
        signature.input_decs[1] = Some(PtrKind::OptRef(false));
        let mut item = surface
            .items
            .iter()
            .find(|item| {
                item.kind
                    .ident()
                    .is_some_and(|ident| ident.name.as_str() == "dual")
            })
            .unwrap()
            .clone();
        annotate_function(&mut item, &FxHashSet::default());
        let catalog = rule_binding_catalog(&item, function, &decisions, &ast_to_hir, tcx);
        let ItemKind::Fn(box body) = &item.kind else { unreachable!() };
        let regions = select_rule_regions(
            &body.body.as_ref().unwrap().stmts[0],
            &catalog,
            &ast_to_hir,
            tcx,
        )
        .unwrap();
        assert_eq!(regions.len(), 3);
        let external = |name: &str| crate::ValueIdentity::External {
            crate_name: "core".into(),
            path: vec!["option".into(), name.into()],
        };
        let method = |receiver, name: &str| crate::Expression::MethodCall {
            receiver: Box::new(receiver),
            method: external(name),
            arguments: vec![],
        };
        let mut observations = vec![];
        for region in regions {
            let mut observation = region.observation;
            observation.target_expression = match observation.source_expression {
                crate::Expression::Unary {
                    operator: UnaryOperator::Deref,
                    ..
                } => crate::Expression::Literal {
                    value: crate::Literal::Integer {
                        value: "3".into(),
                        ty: "i32".into(),
                    },
                },
                crate::Expression::MethodCall { .. } => {
                    let anchor = crate::Expression::Path {
                        value: crate::ValueIdentity::Binding {
                            id: observation.pointer_anchors[0].id.clone(),
                        },
                    };
                    method(anchor, "is_none")
                }
                crate::Expression::Call { .. } => crate::Expression::Call {
                    callee: Box::new(crate::Expression::Path {
                        value: crate::ValueIdentity::ForeignFunction {
                            symbol: "ping".into(),
                        },
                    }),
                    arguments: vec![crate::Expression::Literal {
                        value: crate::Literal::Integer {
                            value: "2".into(),
                            ty: "i32".into(),
                        },
                    }],
                },
                ref other => panic!("unexpected selected region {other:?}"),
            };
            observations.extend([observation.clone(), observation]);
        }
        let rules = crate::synthesize_rules(&[crate::ObservationDocument {
            schema_version: crate::OBSERVATION_SCHEMA_VERSION,
            printf_observations: vec![],
            observations,
        }])
        .unwrap();
        assert_eq!(rules.rules.len(), 3);
        let type_speller = TypeSpeller::new(function, &ast_to_hir, tcx);
        let apply = |document: &crate::RuleDocument| {
            let mut target = item.clone();
            let applied = apply_rule_set(
                &item,
                &mut target,
                &BTreeSet::from([0]),
                document,
                function,
                &decisions,
                &ast_to_hir,
                &type_speller,
                tcx,
            )
            .unwrap();
            (applied, pprust::item_to_string(&target))
        };
        let (forward_applied, forward) = apply(&rules);
        assert_eq!(forward_applied, BTreeSet::from([0]));
        assert_eq!(
            forward,
            "pub unsafe fn dual(p: *mut i32, q: *mut i32) -> (i32, i32, bool) {\n\n    #[proctor(0)]\n    (3i32, ping(2i32), !(q).is_none())\n}"
        );
        let mut reversed = rules.clone();
        reversed.rules.reverse();
        assert_eq!(apply(&reversed), (forward_applied, forward.clone()));

        let incomplete = crate::RuleDocument {
            schema_version: 1,
            printf_rules: vec![],
            rules: vec![rules.rules[0].clone()],
        };
        let (applied, unchanged) = apply(&incomplete);
        assert!(applied.is_empty());
        assert_eq!(unchanged, pprust::item_to_string(&item));

        let complete_view = crate::SkeletonView {
            skeleton: "pub unsafe fn dual(mut p: &i32, mut q: Option<&i32>) -> (i32, i32, bool) {\n    #[proctor(0)]\n    (3i32, ping(2i32), !(q).is_none())\n}".into(),
            needs_transformation: false,
            statement_dispositions: vec![crate::StatementDisposition {
                label: 0,
                disposition: crate::StatementDispositionKind::RuleApplied,
                children: vec![],
            }],
            statement_pair_metadata: vec![],
        };
        for document in [&rules, &reversed] {
            let records = make_skeletons_with_rules(source, Some(document), tcx).unwrap();
            assert_eq!(
                crate::skeleton::tests::function(&records, "dual").applied,
                complete_view
            );
        }
        let records = make_skeletons_with_rules(source, Some(&incomplete), tcx).unwrap();
        assert_eq!(
            crate::skeleton::tests::function(&records, "dual").applied,
            crate::SkeletonView {
                skeleton: "pub unsafe fn dual(mut p: &i32, mut q: Option<&i32>) -> (i32, i32, bool) {\n    #[proctor(0)]\n    todo!()\n}".into(),
                needs_transformation: true,
                statement_dispositions: vec![crate::StatementDisposition {
                    label: 0,
                    disposition: crate::StatementDispositionKind::Transform,
                    children: vec![],
                }],
                statement_pair_metadata: vec![crate::StatementPairMetadata {
                    label: 0,
                    before_statement: "#[proctor(0)]\n(*p, ping(1), !q.is_null())".into(),
                    printf_template: None,
                    pointer_variables_complete: true,
                    pointer_variables: vec![
                        crate::PointerVariableMetadata {
                            name: "p".into(),
                            origin: crate::PointerVariableOrigin::Parameter { index: 0 },
                            before_type: "*mut i32".into(),
                            selected_target_type: "&i32".into(),
                            before_type_is_inferred: false,
                        },
                        crate::PointerVariableMetadata {
                            name: "q".into(),
                            origin: crate::PointerVariableOrigin::Parameter { index: 1 },
                            before_type: "*mut i32".into(),
                            selected_target_type: "Option<&i32>".into(),
                            before_type_is_inferred: false,
                        },
                    ],
                }],
            }
        );
    })
    .unwrap();
}

#[test]
fn observation_and_application_share_identical_region_selection() {
    let source = r#"
struct Holder { ptr: *mut i32 }
unsafe extern "C" {
    fn consume(_: *mut i32);
    fn ping(value: i32) -> i32;
}
unsafe fn selectors(
    holder: *mut Holder,
    p: *mut i32,
    q: *mut i32,
    indirect: unsafe fn(*mut i32),
) {
    let _ = (*holder).ptr;
    let _ = p.is_null();
    consume(p);
    consume((*holder).ptr);
    let _ = (p.is_null(), ping(1));
    let _ = *p + *q;
    let _ = p.offset(q as isize);
    let _closure = || p;
    indirect(p);
    *p = 1;
}
"#;
    run_compiler_on_str(source, |tcx| {
        let mut surface = utils::ast::parse_crate(source.to_owned());
        let mut mapper = utils::ir::AstToHirMapper::new(tcx);
        mapper.map_crate_to_mod(&mut surface, tcx.hir_root_module(), false);
        let item = surface
            .items
            .iter()
            .find(|item| {
                item.kind
                    .ident()
                    .is_some_and(|ident| ident.name.as_str() == "selectors")
            })
            .unwrap();
        let ItemKind::Fn(box function) = &item.kind else { unreachable!() };
        let function_id = local_def("selectors", tcx);
        let decisions = tools_pointer_decisions(tcx);
        let catalog = rule_binding_catalog(
            item,
            function_id,
            &decisions,
            &mapper.ast_to_hir,
            tcx,
        );
        let mut saw_promotion = false;
        let mut saw_absorbed_anchors = false;
        let mut saw_lhs = false;
        let mut saw_two_regions = false;
        let mut saw_empty = false;
        for (statement_index, statement) in function.body.as_ref().unwrap().stmts.iter().enumerate() {
            let Some(expression) = crate::observation::statement_expression(statement) else {
                continue;
            };
            let extraction =
                crate::observation::select_expression_regions(
                    expression,
                    HashSet::new(),
                    Some,
                    &mapper.ast_to_hir,
                    tcx,
                )
                .map(|(_, regions)| {
                    regions
                        .into_iter()
                        .map(|region| {
                            (
                                region.root,
                                region.promoted_field,
                                region.lhs,
                                region
                                    .anchors
                                    .into_iter()
                                    .map(|anchor| tcx.hir_name(anchor.source_binding).to_string())
                                    .collect::<Vec<_>>(),
                            )
                        })
                        .collect::<Vec<_>>()
                });
            let application = crate::observation::select_rule_regions(
                statement,
                &catalog,
                &mapper.ast_to_hir,
                tcx,
            )
            .map(|regions| {
                regions
                    .into_iter()
                    .map(|region| {
                        (
                            region.root,
                            region.promoted_field,
                            region.observation.lhs,
                            region
                                .observation
                                .pointer_anchors
                                .iter()
                                .map(|anchor| region.spellings[&anchor.id].clone())
                                .collect::<Vec<_>>(),
                        )
                    })
                    .collect::<Vec<_>>()
            });
            assert_eq!(
                extraction.as_ref().map(|regions| {
                    regions.to_vec()
                }),
                application,
                "observation extraction and rule application must consume identical maxima"
            );
            match extraction {
                None => unreachable!("selection always returns pairwise-disjoint maxima"),
                Some(regions) => {
                    match statement_index {
                        2 | 3 => assert_eq!(
                            regions
                                .iter()
                                .map(|region| (region.1, region.2, region.3.len()))
                                .collect::<Vec<_>>(),
                            vec![(false, false, 1)],
                            "foreign parents absorb their pointer descendant without inheriting promotion"
                        ),
                        4 => assert_eq!(
                            regions
                                .iter()
                                .map(|region| region.3.len())
                                .collect::<Vec<_>>(),
                            vec![1, 0],
                            "pointer and foreign roots remain disjoint and source-ordered"
                        ),
                        _ => {}
                    }
                    saw_promotion |= regions.iter().any(|region| region.1);
                    saw_lhs |= regions.iter().any(|region| region.2);
                    saw_two_regions |= regions.len() == 2;
                    saw_absorbed_anchors |= regions
                        .iter()
                        .any(|region| region.3.len() == 2 && regions.len() == 1);
                    saw_empty |= regions.is_empty();
                }
            }
        }
        assert!(saw_promotion);
        assert!(saw_absorbed_anchors);
        assert!(saw_lhs);
        assert!(saw_two_regions);
        assert!(saw_empty);
    })
    .unwrap();
}

#[test]
fn post_maximalization_lhs_matches_only_the_rule_with_the_same_role() {
    let fixtures = [
        (
            r#"pub unsafe fn selected(mut pointer: *mut i32) {
                pointer = core::ptr::null_mut();
            }"#,
            true,
        ),
        (
            r#"unsafe extern "C" { fn consume(pointer: *mut i32) -> i32; }
            pub unsafe fn selected(mut pointer: *mut i32, other: *mut i32) {
                let _ = consume({ pointer = other; pointer });
            }"#,
            false,
        ),
    ];
    for (source, expected_lhs) in fixtures {
        run_compiler_on_str(source, |tcx| {
            let mut surface = utils::ast::parse_crate(source.to_owned());
            let mut mapper = utils::ir::AstToHirMapper::new(tcx);
            mapper.map_crate_to_mod(&mut surface, tcx.hir_root_module(), false);
            let item = surface
                .items
                .iter()
                .find(|item| {
                    item.kind
                        .ident()
                        .is_some_and(|ident| ident.name.as_str() == "selected")
                })
                .unwrap();
            let function = local_def("selected", tcx);
            let decisions = tools_pointer_decisions(tcx);
            let catalog = rule_binding_catalog(item, function, &decisions, &mapper.ast_to_hir, tcx);
            let ItemKind::Fn(box body) = &item.kind else { unreachable!() };
            let regions = crate::observation::select_rule_regions(
                &body.body.as_ref().unwrap().stmts[0],
                &catalog,
                &mapper.ast_to_hir,
                tcx,
            )
            .unwrap();
            let [region] = &regions[..] else { panic!("fixture must retain one maximal region") };
            assert_eq!(region.observation.lhs, expected_lhs);

            let mut observation = region.observation.clone();
            observation.target_expression = observation.source_expression.clone();
            observation.target_type = if expected_lhs {
                observation.pointer_anchors[0].target_type.clone()
            } else {
                observation.source_type.clone()
            };
            observation.target_adjusted_type = observation.target_type.clone();
            let rule = crate::synthesize_rules(&[crate::ObservationDocument {
                schema_version: 1,
                printf_observations: vec![],
                observations: vec![observation.clone(), observation.clone()],
            }])
            .unwrap()
            .rules
            .remove(0);
            assert_eq!(rule.lhs, expected_lhs);
            let mut wrong_role = rule.clone();
            wrong_role.lhs = !expected_lhs;
            let input = crate::RuleMatchInput {
                source_expression: region.observation.source_expression.clone(),
                pointer_anchors: region.observation.pointer_anchors.clone(),
                lhs: region.observation.lhs,
                source_type: region.observation.source_type.clone(),
                source_adjusted_type: region.observation.source_adjusted_type.clone(),
                target_type: None,
                target_adjusted_type: expected_lhs
                    .then(|| observation.target_adjusted_type.clone()),
            };
            for rules in [
                vec![rule.clone(), wrong_role.clone()],
                vec![wrong_role.clone(), rule.clone()],
            ] {
                let loaded = crate::LoadedRuleSet::new(&crate::RuleDocument {
                    schema_version: 1,
                    printf_rules: vec![],
                    rules,
                })
                .unwrap();
                let selected = loaded.select(&input).unwrap();
                assert_eq!(loaded.rules()[selected.rule_index].lhs, expected_lhs);
                assert!(
                    loaded
                        .select_with_exclusions(&input, &BTreeSet::from([selected.rule_index]),)
                        .is_none()
                );
            }
        })
        .unwrap();
    }
}

#[test]
fn dependency_external_path_is_structurally_accepted_as_lhs_place() {
    let source = "unsafe fn f() {}";
    run_compiler_on_str(source, |tcx| {
        let mut surface = utils::ast::parse_crate(source.to_owned());
        let mut mapper = utils::ir::AstToHirMapper::new(tcx);
        mapper.map_crate_to_mod(&mut surface, tcx.hir_root_module(), false);
        let function = local_def("f", tcx);
        let type_speller = TypeSpeller::new(function, &mapper.ast_to_hir, tcx);
        let names = HashMap::new();
        let syntax_overrides = BTreeMap::new();
        let type_syntax = HashMap::new();
        let renderer = RuleRenderer {
            names: &names,
            syntax_overrides: &syntax_overrides,
            identity_syntax: &BTreeMap::new(),
            syntax_cursor: Cell::new(0),
            type_syntax: &type_syntax,
            type_speller: &type_speller,
        };
        let expression = crate::Expression::Path {
            value: crate::ValueIdentity::External {
                crate_name: "core".into(),
                path: vec!["mem".into(), "drop".into()],
            },
        };
        let rendered = expression_spelling(&expression, &renderer).unwrap();
        assert!(rendered.ends_with("core::mem::drop"), "{rendered}");
        assert!(parse_rule_expression(rendered, true).is_some());
    })
    .unwrap();
}

#[test]
fn materialization_and_shape_misses_are_local_but_corrupt_invariants_are_fatal() {
    let source = "unsafe fn f(p: *mut i32) { let _ = p.is_null(); }";
    run_compiler_on_str(source, |tcx| {
        let mut surface = utils::ast::parse_crate(source.to_owned());
        let mut mapper = utils::ir::AstToHirMapper::new(tcx);
        mapper.map_crate_to_mod(&mut surface, tcx.hir_root_module(), false);
        let function = local_def("f", tcx);
        let type_speller = TypeSpeller::new(function, &mapper.ast_to_hir, tcx);
        let names = HashMap::new();
        let syntax = BTreeMap::new();
        let identity_syntax = BTreeMap::new();
        let type_syntax = HashMap::new();
        let renderer = RuleRenderer {
            names: &names,
            syntax_overrides: &syntax,
            identity_syntax: &identity_syntax,
            syntax_cursor: Cell::new(0),
            type_syntax: &type_syntax,
            type_speller: &type_speller,
        };
        let unspellable = crate::Expression::Path {
            value: crate::ValueIdentity::External {
                crate_name: "unavailable_crate".into(),
                path: vec!["missing".into()],
            },
        };
        assert!(expression_spelling(&unspellable, &renderer).is_none());
        assert!(parse_rule_expression("if".into(), false).is_none());
        assert!(parse_rule_expression("f()".into(), true).is_none());

        let unsupported =
            utils::ast::parse_crate("unsafe fn f() { #[proctor(0)] unsafe { 1 }; }".into())
                .items
                .remove(0);
        assert!(validate_rule_application_shape(&unsupported).is_err());

        let mut item = surface.items[0].clone();
        annotate_function(&mut item, &FxHashSet::default());
        let mut target = item.clone();
        let invalid = crate::RuleDocument {
            schema_version: crate::RULE_SCHEMA_VERSION + 1,
            printf_rules: vec![],
            rules: vec![],
        };
        let error = apply_rule_set(
            &item,
            &mut target,
            &BTreeSet::from([0]),
            &invalid,
            function,
            &tools_pointer_decisions(tcx),
            &mapper.ast_to_hir,
            &type_speller,
            tcx,
        )
        .unwrap_err();
        assert_eq!(error.kind, GenerationErrorKind::AstHirMismatch);
        assert_eq!(
            pprust::item_to_string(&target),
            pprust::item_to_string(&item)
        );

        let mismatch = make_skeletons("unsafe fn other() { let _ = 1; }", tcx).unwrap_err();
        assert_eq!(mismatch.kind, GenerationErrorKind::AstHirMismatch);
    })
    .unwrap();
}

#[test]
fn rule_type_materialization_reuses_body_alias_syntax() {
    let source = "type Word = i32; unsafe fn f() { let _: Word = 0 as Word; }";
    run_compiler_on_str(source, |tcx| {
        let mut surface = utils::ast::parse_crate(source.to_owned());
        let mut mapper = utils::ir::AstToHirMapper::new(tcx);
        mapper.map_crate_to_mod(&mut surface, tcx.hir_root_module(), false);
        let function = local_def("f", tcx);
        let item = surface
            .items
            .iter()
            .find(|item| {
                item.kind
                    .ident()
                    .is_some_and(|name| name.name.as_str() == "f")
            })
            .unwrap();
        let type_syntax = rule_type_syntax(item, &mapper.ast_to_hir, tcx);
        let names = HashMap::new();
        let syntax_overrides = BTreeMap::new();
        let type_speller = TypeSpeller::new(function, &mapper.ast_to_hir, tcx);
        let renderer = RuleRenderer {
            names: &names,
            syntax_overrides: &syntax_overrides,
            identity_syntax: &BTreeMap::new(),
            syntax_cursor: Cell::new(0),
            type_syntax: &type_syntax,
            type_speller: &type_speller,
        };
        assert_eq!(
            type_tree_spelling(&TypeTree::Primitive { name: "i32".into() }, &renderer),
            Some("Word".to_owned())
        );
    })
    .unwrap();
}

#[test]
fn closed_rule_literals_borrows_methods_and_external_structs_materialize() {
    let source = "unsafe fn f(x: i32) {}";
    run_compiler_on_str(source, |tcx| {
        let mut surface = utils::ast::parse_crate(source.to_owned());
        let mut mapper = utils::ir::AstToHirMapper::new(tcx);
        mapper.map_crate_to_mod(&mut surface, tcx.hir_root_module(), false);
        let function = local_def("f", tcx);
        let type_speller = TypeSpeller::new(function, &mapper.ast_to_hir, tcx);
        let names = HashMap::from([("<id0>".to_owned(), "x".to_owned())]);
        let syntax_overrides = BTreeMap::new();
        let type_syntax = HashMap::new();
        let renderer = RuleRenderer {
            names: &names,
            syntax_overrides: &syntax_overrides,
            identity_syntax: &BTreeMap::new(),
            syntax_cursor: Cell::new(0),
            type_syntax: &type_syntax,
            type_speller: &type_speller,
        };
        let path = || crate::Expression::Path {
            value: crate::ValueIdentity::Binding { id: "<id0>".into() },
        };
        let values = [
            crate::Expression::Literal {
                value: crate::Literal::Float {
                    bits: "7fc0dead".into(),
                    ty: "f32".into(),
                },
            },
            crate::Expression::Literal {
                value: crate::Literal::Char { value: "\n".into() },
            },
            crate::Expression::Literal {
                value: crate::Literal::Char { value: "λ".into() },
            },
            crate::Expression::Literal {
                value: crate::Literal::ByteString {
                    value: vec![0xff, b'"', b'\\'],
                },
            },
            crate::Expression::Literal {
                value: crate::Literal::CString {
                    value: vec![0xff, b'"', b'\\'],
                },
            },
            crate::Expression::AddressOf {
                borrow: BorrowKind::Raw,
                mutability: RawMutability::Const,
                expression: Box::new(path()),
            },
            crate::Expression::AddressOf {
                borrow: BorrowKind::Raw,
                mutability: RawMutability::Mut,
                expression: Box::new(path()),
            },
            crate::Expression::MethodCall {
                receiver: Box::new(path()),
                method: crate::ValueIdentity::External {
                    crate_name: "core".into(),
                    path: vec!["option".into(), "Option".into(), "unwrap".into()],
                },
                arguments: vec![],
            },
            crate::Expression::Struct {
                adt: crate::AdtIdentity::External {
                    crate_name: "core".into(),
                    path: vec!["ops".into(), "range".into(), "Range".into()],
                },
                variant: None,
                fields: vec![
                    crate::StructField {
                        field: crate::FieldIdentity::External {
                            crate_name: "core".into(),
                            path: vec![
                                "ops".into(),
                                "range".into(),
                                "Range".into(),
                                "start".into(),
                            ],
                        },
                        value: path(),
                    },
                    crate::StructField {
                        field: crate::FieldIdentity::External {
                            crate_name: "core".into(),
                            path: vec!["ops".into(), "range".into(), "Range".into(), "end".into()],
                        },
                        value: path(),
                    },
                ],
                rest: None,
            },
        ];
        let rendered = values
            .iter()
            .map(|value| {
                renderer.syntax_cursor.set(0);
                expression_spelling(value, &renderer).unwrap()
            })
            .collect::<Vec<_>>();
        assert!(rendered[0].contains("from_bits(0x7fc0dead)"));
        assert_eq!(rendered[5], "&raw const x");
        assert_eq!(rendered[6], "&raw mut x");
        assert!(rendered[7].contains(".unwrap()"));
        assert!(rendered[8].contains("Range"));
        for value in rendered {
            assert!(
                parse_rule_expression(value.clone(), false).is_some(),
                "{value}"
            );
        }
        for value in ["", "ab"] {
            renderer.syntax_cursor.set(0);
            assert!(
                expression_spelling(
                    &crate::Expression::Literal {
                        value: crate::Literal::Char {
                            value: value.into(),
                        },
                    },
                    &renderer,
                )
                .is_none()
            );
        }
        assert_eq!(
            type_tree_spelling(
                &TypeTree::Primitive {
                    name: "never".into(),
                },
                &renderer,
            ),
            Some("!".to_owned())
        );
    })
    .unwrap();
}

#[test]
fn rule_application_materializes_the_complete_expression_matrix_structurally() {
    let source = "struct Holder { value: i32 } unsafe fn read(_: *mut i32) {} unsafe fn f() {}";
    run_compiler_on_str(source, |tcx| {
        fn shape(expression: &Expr) -> serde_json::Value {
            match &expression.kind {
                ExprKind::Paren(inner) => shape(inner),
                ExprKind::Path(qself, path) => serde_json::json!({
                    "path": path.segments.iter().map(|segment| segment.ident.to_string()).collect::<Vec<_>>(),
                    "qualified": qself.is_some(),
                }),
                ExprKind::MethodCall(call) => serde_json::json!({
                    "method": call.seg.ident.to_string(),
                    "receiver": shape(&call.receiver),
                    "arguments": call.args.iter().map(|argument| shape(argument)).collect::<Vec<_>>(),
                }),
                ExprKind::Call(callee, arguments) => serde_json::json!({
                    "call": shape(callee),
                    "arguments": arguments.iter().map(|argument| shape(argument)).collect::<Vec<_>>(),
                }),
                ExprKind::Unary(operator, operand) => serde_json::json!({
                    "unary": format!("{operator:?}"),
                    "operand": shape(operand),
                }),
                ExprKind::AddrOf(kind, mutability, operand) => serde_json::json!({
                    "address": format!("{kind:?}"),
                    "mutability": format!("{mutability:?}"),
                    "operand": shape(operand),
                }),
                ExprKind::Index(base, index, _) => serde_json::json!({
                    "index": shape(base),
                    "with": shape(index),
                }),
                ExprKind::Cast(value, ty) => serde_json::json!({
                    "cast": shape(value),
                    "type": pprust::ty_to_string(ty),
                }),
                ExprKind::Field(base, field) => serde_json::json!({
                    "field": field.to_string(),
                    "base": shape(base),
                }),
                ExprKind::Binary(operator, left, right) => serde_json::json!({
                    "binary": format!("{:?}", operator.node),
                    "left": shape(left),
                    "right": shape(right),
                }),
                ExprKind::Lit(_) => serde_json::json!({"literal": pprust::expr_to_string(expression)}),
                other => panic!("unsupported application-matrix AST node: {other:?}"),
            }
        }

        let mut surface = utils::ast::parse_crate(source.to_owned());
        let mut mapper = utils::ir::AstToHirMapper::new(tcx);
        mapper.map_crate_to_mod(&mut surface, tcx.hir_root_module(), false);
        let function = local_def("f", tcx);
        let primitive_rule = || crate::RuleTypeTree::Primitive { name: "i32".into() };
        let primitive = || TypeTree::Primitive { name: "i32".into() };
        let rule_anchor = |index| crate::RuleExpression::Path {
            value: crate::RuleValueIdentity::Variable {
                sort: crate::VariableSort::Anchor,
                index,
            },
        };
        let rule_expression = |index| crate::RuleExpression::Variable {
            sort: crate::VariableSort::Expression,
            index,
        };
        let concrete_path = |id: &str| crate::Expression::Path {
            value: crate::ValueIdentity::Binding { id: id.into() },
        };
        let external_rule = |name: &str| crate::RuleValueIdentity::External {
            crate_name: "core".into(),
            path: vec!["ptr".into(), name.into()],
        };
        let external = |name: &str| crate::ValueIdentity::External {
            crate_name: "core".into(),
            path: vec!["ptr".into(), name.into()],
        };
        let rule_method = |receiver, name: &str, arguments| crate::RuleExpression::MethodCall {
            receiver: Box::new(receiver),
            method: external_rule(name),
            arguments,
        };
        let method = |receiver, name: &str, arguments| crate::Expression::MethodCall {
            receiver: Box::new(receiver),
            method: external(name),
            arguments,
        };
        let rule_unary = |operator, operand| crate::RuleExpression::Unary {
            operator,
            operand: Box::new(operand),
        };
        let unary = |operator, operand| crate::Expression::Unary {
            operator,
            operand: Box::new(operand),
        };
        let rule_cast = |expression, name: &str| crate::RuleExpression::Cast {
            expression: Box::new(expression),
            ty: crate::RuleTypeTree::Primitive { name: name.into() },
        };
        let cast = |expression, name: &str| crate::Expression::Cast {
            expression: Box::new(expression),
            ty: TypeTree::Primitive { name: name.into() },
        };
        let rule_index = |base, index| crate::RuleExpression::Index {
            base: Box::new(base),
            index: Box::new(index),
        };
        let rule_integer = |value| crate::RuleExpression::Literal {
            value: crate::RuleLiteral::Integer {
                value,
                ty: "usize".into(),
            },
        };
        let integer = |value: &str| crate::Expression::Literal {
            value: crate::Literal::Integer {
                value: value.into(),
                ty: "usize".into(),
            },
        };
        let chain = |receiver: crate::RuleExpression, first: &str| {
            rule_method(rule_method(receiver, first, vec![]), "unwrap", vec![])
        };
        let offset_source = |name: &str, argument| {
            rule_unary(
                UnaryOperator::Deref,
                rule_method(rule_anchor(0), name, vec![argument]),
            )
        };
        let concrete_offset = |name: &str, argument| {
            unary(
                UnaryOperator::Deref,
                method(concrete_path("<id0>"), name, vec![argument]),
            )
        };
        let make_rule = |source_pattern, target_pattern| crate::Rule {
            source_pattern,
            target_pattern,
            pointer_anchors: vec![crate::RulePointerAnchor {
                id: crate::RuleVariable::new(crate::VariableSort::Anchor, 0),
                source_type: crate::RuleTypeTree::RawPointer {
                    mutability: RawMutability::Const,
                    pointee: Box::new(primitive_rule()),
                },
                target_type: crate::RuleTypeTree::Reference {
                    mutability: RefMutability::Shared,
                    pointee: Box::new(primitive_rule()),
                },
            }],
            lhs: false,
            source_type: primitive_rule(),
            source_adjusted_type: primitive_rule(),
            target_type: primitive_rule(),
            target_adjusted_type: primitive_rule(),
        };
        let input = |source_expression| crate::RuleMatchInput {
            source_expression,
            pointer_anchors: vec![crate::PointerAnchor {
                id: "<id0>".into(),
                source_type: TypeTree::RawPointer {
                    mutability: RawMutability::Const,
                    pointee: Box::new(primitive()),
                },
                target_type: TypeTree::Reference {
                    mutability: RefMutability::Shared,
                    pointee: Box::new(primitive()),
                },
            }],
            lhs: false,
            source_type: primitive(),
            source_adjusted_type: primitive(),
            target_type: Some(primitive()),
            target_adjusted_type: Some(primitive()),
        };
        let expression_variable = rule_expression(0);
        let concrete_variable = concrete_path("<id1>");
        let isize_expression = rule_cast(expression_variable.clone(), "isize");
        let concrete_isize = cast(concrete_variable.clone(), "isize");
        let usize_expression = rule_cast(expression_variable.clone(), "usize");
        let field_identity = crate::RuleMemberIdentity::External {
            crate_name: "fixture".into(),
            path: vec!["Holder".into(), "value".into()],
        };
        let concrete_field_identity = crate::FieldIdentity::External {
            crate_name: "fixture".into(),
            path: vec!["Holder".into(), "value".into()],
        };
        let magnitude = crate::RuleIntegerMagnitude::Variable(crate::RuleVariable::new(
            crate::VariableSort::IntegerMagnitude,
            0,
        ));
        let rule_sum = crate::RuleExpression::Binary {
            operator: BinaryOperator::Add,
            left: Box::new(expression_variable.clone()),
            right: Box::new(rule_integer(magnitude.clone())),
        };
        let concrete_sum = crate::Expression::Binary {
            operator: BinaryOperator::Add,
            left: Box::new(concrete_variable.clone()),
            right: Box::new(integer("1")),
        };
        let local_function = crate::RuleValueIdentity::Variable {
            sort: crate::VariableSort::Function,
            index: 0,
        };
        let concrete_function = crate::ValueIdentity::Function { id: "<fn0>".into() };
        let cases = vec![
            (
                "offset index cast",
                offset_source("offset", isize_expression.clone()),
                rule_index(rule_anchor(0), usize_expression.clone()),
                concrete_offset("offset", concrete_isize.clone()),
                "p[i as usize]",
            ),
            (
                "add index",
                offset_source("add", expression_variable.clone()),
                rule_index(rule_anchor(0), expression_variable.clone()),
                concrete_offset("add", concrete_variable.clone()),
                "p[i]",
            ),
            (
                "null to none",
                rule_method(rule_anchor(0), "is_null", vec![]),
                rule_method(rule_anchor(0), "is_none", vec![]),
                method(concrete_path("<id0>"), "is_null", vec![]),
                "p.is_none()",
            ),
            (
                "negated null to some",
                rule_unary(
                    UnaryOperator::Not,
                    rule_method(rule_anchor(0), "is_null", vec![]),
                ),
                rule_method(rule_anchor(0), "is_some", vec![]),
                unary(
                    UnaryOperator::Not,
                    method(concrete_path("<id0>"), "is_null", vec![]),
                ),
                "p.is_some()",
            ),
            (
                "mutable address dereference simplification",
                crate::RuleExpression::AddressOf {
                    borrow: BorrowKind::Reference,
                    mutability: RawMutability::Mut,
                    expression: Box::new(rule_unary(UnaryOperator::Deref, rule_anchor(0))),
                },
                rule_anchor(0),
                crate::Expression::AddressOf {
                    borrow: BorrowKind::Reference,
                    mutability: RawMutability::Mut,
                    expression: Box::new(unary(
                        UnaryOperator::Deref,
                        concrete_path("<id0>"),
                    )),
                },
                "p",
            ),
            (
                "shared address dereference simplification",
                crate::RuleExpression::AddressOf {
                    borrow: BorrowKind::Reference,
                    mutability: RawMutability::Const,
                    expression: Box::new(rule_unary(UnaryOperator::Deref, rule_anchor(0))),
                },
                rule_anchor(0),
                crate::Expression::AddressOf {
                    borrow: BorrowKind::Reference,
                    mutability: RawMutability::Const,
                    expression: Box::new(unary(
                        UnaryOperator::Deref,
                        concrete_path("<id0>"),
                    )),
                },
                "p",
            ),
            (
                "optional shared dereference",
                rule_unary(UnaryOperator::Deref, rule_anchor(0)),
                rule_unary(UnaryOperator::Deref, chain(rule_anchor(0), "as_deref")),
                unary(UnaryOperator::Deref, concrete_path("<id0>")),
                "*p.as_deref().unwrap()",
            ),
            (
                "optional mutable dereference",
                rule_unary(UnaryOperator::Deref, rule_anchor(0)),
                rule_unary(
                    UnaryOperator::Deref,
                    chain(rule_anchor(0), "as_deref_mut"),
                ),
                unary(UnaryOperator::Deref, concrete_path("<id0>")),
                "*p.as_deref_mut().unwrap()",
            ),
            (
                "field projection",
                crate::RuleExpression::Field {
                    base: Box::new(rule_unary(UnaryOperator::Deref, rule_anchor(0))),
                    field: field_identity.clone(),
                },
                crate::RuleExpression::Field {
                    base: Box::new(rule_anchor(0)),
                    field: field_identity,
                },
                crate::Expression::Field {
                    base: Box::new(unary(UnaryOperator::Deref, concrete_path("<id0>"))),
                    field: concrete_field_identity,
                },
                "p.value",
            ),
            (
                "local function identity",
                crate::RuleExpression::Call {
                    callee: Box::new(crate::RuleExpression::Path {
                        value: local_function.clone(),
                    }),
                    arguments: vec![rule_anchor(0)],
                },
                crate::RuleExpression::Call {
                    callee: Box::new(crate::RuleExpression::Path {
                        value: local_function,
                    }),
                    arguments: vec![chain(rule_anchor(0), "as_deref")],
                },
                crate::Expression::Call {
                    callee: Box::new(crate::Expression::Path {
                        value: concrete_function,
                    }),
                    arguments: vec![concrete_path("<id0>")],
                },
                "read(p.as_deref().unwrap())",
            ),
            (
                "addressed index",
                rule_method(rule_anchor(0), "offset", vec![isize_expression.clone()]),
                crate::RuleExpression::AddressOf {
                    borrow: BorrowKind::Reference,
                    mutability: RawMutability::Const,
                    expression: Box::new(rule_index(rule_anchor(0), usize_expression)),
                },
                method(
                    concrete_path("<id0>"),
                    "offset",
                    vec![concrete_isize.clone()],
                ),
                "&p[i as usize]",
            ),
            (
                "optional indexed dereference",
                offset_source("offset", isize_expression),
                rule_index(chain(rule_anchor(0), "as_deref"), rule_cast(rule_expression(0), "usize")),
                concrete_offset("offset", concrete_isize),
                "p.as_deref().unwrap()[i as usize]",
            ),
            (
                "integer magnitude",
                offset_source("offset", rule_cast(rule_sum.clone(), "isize")),
                rule_index(rule_anchor(0), rule_sum),
                concrete_offset("offset", cast(concrete_sum.clone(), "isize")),
                "p[i + 1usize]",
            ),
        ];
        let names = HashMap::from([
            ("<id0>".to_owned(), "p".to_owned()),
            ("<id1>".to_owned(), "i".to_owned()),
            ("<fn0>".to_owned(), "read".to_owned()),
        ]);
        let type_syntax = HashMap::new();
        let type_speller = TypeSpeller::new(function, &mapper.ast_to_hir, tcx);
        for (name, source_pattern, target_pattern, concrete, expected) in cases {
            let selected = LoadedRuleSet::new(&crate::RuleDocument {
                schema_version: 1,
                printf_rules: vec![],
                rules: vec![make_rule(source_pattern, target_pattern)],
            })
            .unwrap()
            .select(&input(concrete))
            .unwrap_or_else(|| panic!("{name} did not select"));
            let renderer = RuleRenderer {
                names: &names,
                syntax_overrides: &selected.syntax_overrides,
                identity_syntax: &selected.identity_syntax,
                syntax_cursor: Cell::new(0),
                type_syntax: &type_syntax,
                type_speller: &type_speller,
            };
            let rendered = expression_spelling(&selected.target_expression, &renderer)
                .unwrap_or_else(|| panic!("{name} did not render"));
            let actual = parse_rule_expression(rendered, false)
                .unwrap_or_else(|| panic!("{name} did not parse"));
            let expected = parse_rule_expression(expected.to_owned(), false).unwrap();
            assert_eq!(shape(&actual), shape(&expected), "{name}");
        }
    })
    .unwrap();
}

#[test]
fn compiler_source_occurrences_drive_expression_and_identity_metavariables() {
    let source = r#"
unsafe fn read(value: i32) -> i32 { value }
use self::read as alias;
unsafe fn f() { let _ = (((1))) + (2); let _ = alias(1); }
"#;
    run_compiler_on_str(source, |tcx| {
        let mut surface = utils::ast::parse_crate(source.to_owned());
        let mut mapper = utils::ir::AstToHirMapper::new(tcx);
        mapper.map_crate_to_mod(&mut surface, tcx.hir_root_module(), false);
        let function = local_def("f", tcx);
        let item = surface
            .items
            .iter()
            .find(|item| {
                item.kind
                    .ident()
                    .is_some_and(|name| name.name.as_str() == "f")
            })
            .unwrap();
        let ItemKind::Fn(box function_item) = &item.kind else { unreachable!() };
        let expressions = function_item
            .body
            .as_ref()
            .unwrap()
            .stmts
            .iter()
            .map(|statement| {
                let StmtKind::Let(local) = &statement.kind else { unreachable!() };
                let LocalKind::Init(expression) = &local.kind else { unreachable!() };
                expression.as_ref()
            })
            .collect::<Vec<_>>();
        fn syntax(expression: &Expr) -> Vec<String> {
            struct Collector(Vec<String>);
            impl<'ast> visit::Visitor<'ast> for Collector {
                fn visit_expr(&mut self, expression: &'ast Expr) {
                    self.0.push(pprust::expr_to_string(expression));
                    let mut normalized = expression;
                    while let ExprKind::Paren(inner) = &normalized.kind {
                        normalized = inner;
                    }
                    if normalized.id != expression.id {
                        visit::walk_expr(self, normalized);
                    } else {
                        visit::walk_expr(self, expression);
                    }
                }
            }
            let mut collector = Collector(vec![]);
            collector.visit_expr(expression);
            collector.0
        }
        let primitive = crate::RuleTypeTree::Primitive { name: "i32".into() };
        let anchor = crate::RulePointerAnchor {
            id: crate::RuleVariable::new(crate::VariableSort::Anchor, 0),
            source_type: crate::RuleTypeTree::RawPointer {
                mutability: RawMutability::Const,
                pointee: Box::new(primitive.clone()),
            },
            target_type: crate::RuleTypeTree::Reference {
                mutability: RefMutability::Shared,
                pointee: Box::new(primitive.clone()),
            },
        };
        let make_rule = |source_pattern, target_pattern| crate::Rule {
            source_pattern,
            target_pattern,
            pointer_anchors: vec![anchor.clone()],
            lhs: false,
            source_type: primitive.clone(),
            source_adjusted_type: primitive.clone(),
            target_type: primitive.clone(),
            target_adjusted_type: primitive.clone(),
        };
        let integer = |value: &str| crate::Expression::Literal {
            value: crate::Literal::Integer {
                value: value.into(),
                ty: "i32".into(),
            },
        };
        let input = |source_expression| crate::RuleMatchInput {
            source_expression,
            pointer_anchors: vec![crate::PointerAnchor {
                id: "<id0>".into(),
                source_type: TypeTree::RawPointer {
                    mutability: RawMutability::Const,
                    pointee: Box::new(TypeTree::Primitive { name: "i32".into() }),
                },
                target_type: TypeTree::Reference {
                    mutability: RefMutability::Shared,
                    pointee: Box::new(TypeTree::Primitive { name: "i32".into() }),
                },
            }],
            lhs: false,
            source_type: TypeTree::Primitive { name: "i32".into() },
            source_adjusted_type: TypeTree::Primitive { name: "i32".into() },
            target_type: Some(TypeTree::Primitive { name: "i32".into() }),
            target_adjusted_type: Some(TypeTree::Primitive { name: "i32".into() }),
        };
        let expression_variable = |index| crate::RuleExpression::Variable {
            sort: crate::VariableSort::Expression,
            index,
        };
        let expression_rule = make_rule(
            crate::RuleExpression::Binary {
                operator: BinaryOperator::Add,
                left: Box::new(expression_variable(0)),
                right: Box::new(expression_variable(1)),
            },
            expression_variable(1),
        );
        let loaded = LoadedRuleSet::new(&crate::RuleDocument {
            schema_version: 1,
            printf_rules: vec![],
            rules: vec![expression_rule],
        })
        .unwrap();
        let selected = loaded
            .select_with_exclusions_and_syntax(
                &input(crate::Expression::Binary {
                    operator: BinaryOperator::Add,
                    left: Box::new(integer("1")),
                    right: Box::new(integer("2")),
                }),
                &BTreeSet::new(),
                &syntax(expressions[0]),
            )
            .unwrap();
        assert_eq!(selected.syntax_overrides.get(&0).unwrap(), "(2)");

        let function_variable = crate::RuleExpression::Path {
            value: crate::RuleValueIdentity::Variable {
                sort: crate::VariableSort::Function,
                index: 0,
            },
        };
        let call_rule = make_rule(
            crate::RuleExpression::Call {
                callee: Box::new(function_variable.clone()),
                arguments: vec![expression_variable(0)],
            },
            crate::RuleExpression::Call {
                callee: Box::new(function_variable),
                arguments: vec![crate::RuleExpression::Literal {
                    value: crate::RuleLiteral::Integer {
                        value: crate::RuleIntegerMagnitude::Fixed("2".into()),
                        ty: "i32".into(),
                    },
                }],
            },
        );
        let loaded = LoadedRuleSet::new(&crate::RuleDocument {
            schema_version: 1,
            printf_rules: vec![],
            rules: vec![call_rule],
        })
        .unwrap();
        let selected = loaded
            .select_with_exclusions_and_syntax(
                &input(crate::Expression::Call {
                    callee: Box::new(crate::Expression::Path {
                        value: crate::ValueIdentity::Function { id: "<fn0>".into() },
                    }),
                    arguments: vec![integer("1")],
                }),
                &BTreeSet::new(),
                &syntax(expressions[1]),
            )
            .unwrap();
        assert_eq!(selected.identity_syntax.get("<fn0>").unwrap(), "alias");
        let names = HashMap::from([("<fn0>".to_owned(), "read".to_owned())]);
        let type_syntax = HashMap::new();
        let type_speller = TypeSpeller::new(function, &mapper.ast_to_hir, tcx);
        let renderer = RuleRenderer {
            names: &names,
            syntax_overrides: &selected.syntax_overrides,
            identity_syntax: &selected.identity_syntax,
            syntax_cursor: Cell::new(0),
            type_syntax: &type_syntax,
            type_speller: &type_speller,
        };
        assert_eq!(
            expression_spelling(&selected.target_expression, &renderer).unwrap(),
            "alias(2i32)"
        );
    })
    .unwrap();
}

#[test]
fn optional_pointee_requires_an_immediate_reference_or_box() {
    let primitive = TypeTree::Primitive { name: "i32".into() };
    let reference = TypeTree::Reference {
        mutability: RefMutability::Shared,
        pointee: Box::new(primitive.clone()),
    };
    let option = |argument| TypeTree::Adt {
        adt_kind: AdtKind::Enum,
        identity: AdtIdentity::External {
            crate_name: "core".into(),
            path: vec!["option".into(), "Option".into()],
        },
        arguments: vec![argument],
    };
    let boxed = TypeTree::Adt {
        adt_kind: AdtKind::Struct,
        identity: AdtIdentity::External {
            crate_name: "alloc".into(),
            path: vec!["boxed".into(), "Box".into()],
        },
        arguments: vec![primitive.clone()],
    };
    assert_eq!(
        option_or_box_pointee(&option(reference)),
        Some(primitive.clone())
    );
    assert_eq!(option_or_box_pointee(&option(boxed)), Some(primitive));
    assert_eq!(
        option_or_box_pointee(&option(option(TypeTree::Reference {
            mutability: RefMutability::Shared,
            pointee: Box::new(TypeTree::Primitive { name: "i32".into() }),
        }))),
        None
    );
}
