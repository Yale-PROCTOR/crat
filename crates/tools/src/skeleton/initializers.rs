use super::*;

pub(crate) fn initializer_expression(item: &Item) -> Option<&Expr> {
    match &item.kind {
        ItemKind::Static(value) => value.expr.as_deref(),
        ItemKind::Const(value) => value.expr.as_deref(),
        _ => None,
    }
}

pub(crate) fn set_initializer(item: &mut Item, expression: P<Expr>) {
    match &mut item.kind {
        ItemKind::Static(value) => value.expr = Some(expression),
        ItemKind::Const(value) => value.expr = Some(expression),
        _ => unreachable!("initializer targets are static or const items"),
    }
}

pub(crate) fn initializer_function(item: &Item) -> P<Item> {
    let expression = initializer_expression(item).expect("initializer has an expression");
    let ExprKind::Block(block, _) = &expression.kind else {
        unreachable!("only block initializers have a function-shaped view")
    };
    let mut item = utils::item!("unsafe fn __proctor_initializer() {{}}");
    let ItemKind::Fn(function) = &mut item.kind else { unreachable!() };
    function.body = Some(block.clone());
    function.body.as_mut().unwrap().rules = rustc_ast::BlockCheckMode::Default;
    P(item)
}

fn install_function_body(item: &mut Item, function: &Item) {
    let mut expression = P(initializer_expression(item).unwrap().clone());
    let ExprKind::Block(block, _) = &mut expression.kind else { unreachable!() };
    let rules = block.rules;
    let ItemKind::Fn(function) = &function.kind else { unreachable!() };
    *block = function.body.as_ref().unwrap().clone();
    block.rules = rules;
    set_initializer(item, expression);
}

pub(super) fn make_initializer_record(
    surface: &SurfaceItem,
    ast_to_hir: &utils::ir::AstToHir,
    decisions: &InitialPointerDecisions,
    tcx: TyCtxt<'_>,
) -> Result<Option<InitializerRecord>, GenerationError> {
    let Some(expression) = initializer_expression(&surface.item) else { return Ok(None) };
    if !matches!(expression.kind, ExprKind::Block(..)) {
        let mut skeleton = surface.item.clone();
        set_initializer(&mut skeleton, P(todo_expr()));
        return Ok(Some(InitializerRecord {
            annotated_source: render_annotated_item(&surface.item),
            skeleton: render_annotated_item(&skeleton),
            needs_transformation: true,
            block: false,
            statement_dispositions: vec![],
        }));
    }
    let mut source = initializer_function(&surface.item);
    let opaque = collect_opaque_nested_expressions(&source, &surface.path)?;
    let ItemKind::Fn(function) = &source.kind else { unreachable!() };
    let mut validator = BodyValidator {
        function_path: &surface.path,
        opaque_expressions: &opaque,
        opaque_depth: 0,
        closure_depth: 0,
        error: None,
    };
    validator.visit_block(function.body.as_ref().unwrap());
    if let Some(error) = validator.error {
        return Err(error);
    }
    annotate_function(&mut source, &opaque);
    let classification = classify_function_statements(
        &source,
        &opaque,
        ast_to_hir,
        decisions,
        &PreservationDecisionOverrides::default(),
        tcx,
    );
    let transformed = classification.transformed;
    let preserved_shells = classification.preserved_shells;
    let mut skeleton = source.clone();
    let speller = TypeSpeller::new(surface.def_id, ast_to_hir, tcx);
    let empty = BTreeSet::new();
    let mut skeletonizer = Skeletonizer {
        ast_to_hir,
        decisions,
        statements_requiring_transformation: &transformed,
        preserved_shell_statements: &preserved_shells,
        rule_applied_statements: &empty,
        printf_template_statements: &empty,
        type_speller: &speller,
        function_path: &surface.path,
        error: None,
        tcx,
    };
    skeletonizer.visit_item(&mut skeleton);
    if let Some(error) = skeletonizer.error {
        return Err(error);
    }
    let dispositions = make_disposition_forest(
        &skeleton,
        &transformed.iter().copied().collect(),
        &preserved_shells.iter().copied().collect(),
        &HashSet::new(),
        &HashSet::new(),
    )
    .map_err(|error| GenerationError {
        kind: GenerationErrorKind::AstHirMismatch,
        function_path: surface.path.clone(),
        message: error.message,
    })?;
    let mut source_item = surface.item.clone();
    install_function_body(&mut source_item, &source);
    let mut skeleton_item = surface.item.clone();
    install_function_body(&mut skeleton_item, &skeleton);
    Ok(Some(InitializerRecord {
        annotated_source: render_annotated_item(&source_item),
        skeleton: render_annotated_item(&skeleton_item),
        needs_transformation: !transformed.is_empty(),
        block: true,
        statement_dispositions: dispositions,
    }))
}
