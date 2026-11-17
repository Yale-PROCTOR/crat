use super::*;

pub(super) fn normalize_observation_macros(
    item: &mut Item,
    function: LocalDefId,
    targets: &FxHashSet<LocalDefId>,
    ast_to_hir: &utils::ir::AstToHir,
    tcx: TyCtxt<'_>,
) -> Result<(), ReplacementError> {
    let ItemKind::Fn(body) = &mut item.kind else { unreachable!() };
    let mut normalizer = MacroNormalizer {
        ast_to_hir,
        tcx,
        targets,
        speller: crate::skeleton::TypeSpeller::new(function, ast_to_hir, tcx),
        error: None,
    };
    normalizer.visit_block(body.body.as_mut().unwrap());
    normalizer.error.map_or(Ok(()), |message| {
        Err(global_error(ReplacementErrorKind::RewriteFailure, message))
    })
}

struct MacroNormalizer<'a, 'tcx> {
    ast_to_hir: &'a utils::ir::AstToHir,
    tcx: TyCtxt<'tcx>,
    targets: &'a FxHashSet<LocalDefId>,
    speller: crate::skeleton::TypeSpeller<'a, 'tcx>,
    error: Option<String>,
}

impl<'tcx> MacroNormalizer<'_, 'tcx> {
    fn placeholder(&self, expression: &'tcx hir::Expr<'tcx>) -> Result<Option<P<Expr>>, String> {
        struct References<'a, 'tcx> {
            tcx: TyCtxt<'tcx>,
            targets: &'a FxHashSet<LocalDefId>,
            found: bool,
        }
        impl<'tcx> HirVisitor<'tcx> for References<'_, 'tcx> {
            type NestedFilter = rustc_middle::hir::nested_filter::OnlyBodies;

            fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
                self.tcx
            }

            fn visit_expr(&mut self, expression: &'tcx hir::Expr<'tcx>) {
                if let hir::ExprKind::Path(path) = &expression.kind {
                    let owner = self.tcx.hir_enclosing_body_owner(expression.hir_id);
                    if let Res::Def(DefKind::Fn, definition) =
                        self.tcx.typeck(owner).qpath_res(path, expression.hir_id)
                        && definition
                            .as_local()
                            .is_some_and(|definition| self.targets.contains(&definition))
                    {
                        self.found = true;
                    }
                }
                intravisit::walk_expr(self, expression);
            }
        }
        let mut references = References {
            tcx: self.tcx,
            targets: self.targets,
            found: false,
        };
        references.visit_expr(expression);
        if !references.found {
            return Ok(None);
        }
        let owner = self.tcx.hir_enclosing_body_owner(expression.hir_id);
        let ty = self.tcx.typeck(owner).expr_ty(expression);
        if ty.is_never() {
            return Ok(Some(P::new(utils::expr!("::core::todo!()"))));
        }
        let ty = self.speller.render_semantic_type(ty)?;
        let ty = pprust::ty_to_string(&ty);
        // Keep the result type and place semantics, with a macro marker that
        // excludes this statement from learning. This source is never executed.
        Ok(Some(P::new(utils::expr!(
            "*{{ let __proctor_observation_macro: *mut {ty} = ::core::todo!(); __proctor_observation_macro }}"
        ))))
    }
}

impl MutVisitor for MacroNormalizer<'_, '_> {
    fn visit_item(&mut self, _item: &mut Item) {}

    fn visit_ty(&mut self, _ty: &mut Ty) {}

    fn visit_anon_const(&mut self, _constant: &mut rustc_ast::AnonConst) {}

    fn visit_expr(&mut self, expression: &mut Expr) {
        if self.error.is_some() {
            return;
        }
        if matches!(expression.kind, ExprKind::MacCall(..)) {
            let replacement = self
                .ast_to_hir
                .get_expr(expression.id, self.tcx)
                .ok_or_else(|| "observation macro expression has no compiler mapping".to_owned())
                .and_then(|expression| self.placeholder(expression));
            match replacement {
                Ok(Some(mut replacement)) => {
                    replacement.attrs = expression.attrs.clone();
                    replacement.span = expression.span;
                    *expression = *replacement;
                }
                Ok(None) => {}
                Err(error) => self.error = Some(error),
            }
            return;
        }
        mut_visit::walk_expr(self, expression);
    }

    fn flat_map_stmt(&mut self, mut statement: Stmt) -> SmallVec<[Stmt; 1]> {
        if let StmtKind::MacCall(mac) = &statement.kind {
            let replacement = self
                .ast_to_hir
                .get_stmt(statement.id, self.tcx)
                .and_then(|statement| match statement.kind {
                    hir::StmtKind::Expr(expression) => Some((expression, false)),
                    hir::StmtKind::Semi(expression) => Some((expression, true)),
                    _ => None,
                })
                .ok_or_else(|| "observation macro statement has no compiler expression".to_owned())
                .and_then(|(expression, semi)| {
                    self.placeholder(expression)
                        .map(|replacement| (replacement, semi))
                });
            match replacement {
                Ok((Some(mut expression), semi)) => {
                    expression.attrs = mac.attrs.clone();
                    statement.kind = if semi {
                        StmtKind::Semi(expression)
                    } else {
                        StmtKind::Expr(expression)
                    };
                }
                Ok((None, _)) => {}
                Err(error) => self.error = Some(error),
            }
            return smallvec::smallvec![statement];
        }
        mut_visit::walk_flat_map_stmt(self, statement)
    }
}

#[cfg(test)]
mod tests {
    use utils::compilation::run_compiler_on_str;

    use super::*;

    #[test]
    fn placeholders_preserve_result_types_and_leave_unrelated_macros_intact() {
        for (body, name, masked) in [
            (
                "let text = format!(\"{}\", leaf(p)); *p + text.len() as i32",
                "format!",
                true,
            ),
            ("let values = vec![leaf(p)]; *p + values[0]", "vec!", true),
            ("let callbacks = vec![|| *p]; callbacks[0]()", "vec!", false),
            (
                "let text = stringify!(leaf(p)); *p + text.len() as i32",
                "stringify!",
                false,
            ),
        ] {
            let source = format!(
                "pub unsafe fn leaf(p: *const i32) -> i32 {{ *p }} pub unsafe fn caller(p: *const i32) -> i32 {{ {body} }}"
            );
            run_compiler_on_str(&source, |tcx| {
                let mut analysis =
                    parse_crate(&source, ReplacementErrorKind::RewriteFailure).unwrap();
                let mapping = map_surface_to_hir(&mut analysis, tcx).unwrap();
                let mut functions = vec![];
                collect_current_functions(
                    &analysis.items,
                    &mapping.global_map,
                    &mut vec![],
                    &mut functions,
                    &mut HashMap::new(),
                    tcx,
                )
                .unwrap();
                let targets = functions.iter().map(|function| function.def_id).collect();
                let function = &functions[1];
                let mut copy = function.item.clone();
                normalize_observation_macros(&mut copy, function.def_id, &targets, &mapping, tcx)
                    .unwrap();
                let ItemKind::Fn(function) = &mut copy.kind else { unreachable!() };
                function.ident = parsed_ident("observed");
                let copy = pprust::item_to_string(&copy);
                assert_eq!(!copy.contains(name), masked, "{copy}");
                run_compiler_on_str(&format!("{source}\n{copy}"), utils::type_check).expect(&copy);
            })
            .unwrap();
        }
    }
}
