use rustc_ast::{
    self,
    ast::*,
    mut_visit::{self, MutVisitor},
    ptr::P,
};
use rustc_span::source_map::SourceMap;
use smallvec::smallvec;
use thin_vec::ThinVec;

use super::suggestion::{AstEdit, AstEditKind, AstSuggestion, AstSuggestions};

#[derive(Debug)]
pub struct TransformVisitor<'tcx> {
    pub(super) suggestions: AstSuggestions<'tcx>,
    pub updated: bool,
}

impl<'tcx> TransformVisitor<'tcx> {
    #[allow(unused)]
    pub fn new(source_map: &'tcx SourceMap, suggestion_vec: Vec<AstSuggestion>) -> Self {
        let mut suggestions = AstSuggestions::new(source_map);
        for suggestion in suggestion_vec {
            suggestions.add(suggestion.span, suggestion.action);
        }
        Self {
            suggestions,
            updated: false,
        }
    }

    pub fn transform(&mut self, krate: &mut Crate) {
        self.updated = false;
        self.visit_crate(krate);
    }

    #[allow(unused)]
    pub fn print_suggestions(&self) {
        self.suggestions.print_suggestions();
    }

    pub fn assert_finished(&self) {
        self.suggestions.assert_empty();
    }
}

impl MutVisitor for TransformVisitor<'_> {
    fn visit_crate(&mut self, krate: &mut Crate) {
        mut_visit::walk_crate(self, krate);
        let new_items: ThinVec<_> = krate
            .items
            .drain(..)
            .flat_map(|item| {
                let item_span = item.span;
                let mut append_vec: ThinVec<_> = vec![item].into();
                let edit_vec = self.suggestions.pop_by_kind(
                    item_span,
                    vec![
                        AstEditKind::AppendAfterItem,
                        AstEditKind::FlatMapItemsWithAttrs,
                    ],
                );
                for edit in edit_vec {
                    match edit.action {
                        AstEdit::AppendAfterItem(new_item) => {
                            self.updated = true;
                            append_vec.push(P(new_item));
                        }
                        AstEdit::FlatMapItemsWithAttrs(mut new_items) => {
                            self.updated = true;
                            let mut orig_item = append_vec.swap_remove(0);
                            if let Some(first_item) = new_items.first_mut() {
                                first_item.attrs = orig_item.attrs.drain(..).collect();
                            }
                            append_vec = new_items;
                        }
                        _ => {
                            unreachable!();
                        }
                    }
                }
                append_vec
            })
            .collect();
        krate.items.extend(new_items);
    }

    fn visit_item(&mut self, item: &mut Item) {
        mut_visit::walk_item(self, item);
        let edit_vec = self.suggestions.pop_by_kind(
            item.span,
            vec![AstEditKind::ReplaceItem, AstEditKind::RemoveFieldDef],
        );
        for edit in edit_vec {
            match edit.action {
                AstEdit::ReplaceItem(new_item) => {
                    self.updated = true;
                    *item = new_item;
                    item.span = edit.span;
                }
                AstEdit::RemoveFieldDef(span) => {
                    let ItemKind::Struct(_, _, VariantData::Struct { ref mut fields, .. }) =
                        item.kind
                    else {
                        unreachable!(
                            "RemoveFieldDef should only be applied to a struct item definition"
                        );
                    };
                    // Remove the field with the given span from the struct definition.
                    fields.retain(|field| {
                        // Retain fields that do not match the span of the field to be removed.
                        !(field.span.lo() == span.lo() && field.span.hi() == span.hi())
                    });
                    self.updated = true;
                }
                _ => {
                    unreachable!();
                }
            }
        }
    }

    fn visit_block(&mut self, block: &mut Block) {
        mut_visit::walk_block(self, block);
        let edit_vec = self
            .suggestions
            .pop_by_kind(block.span, vec![AstEditKind::PrependToBlock]);
        for edit in edit_vec {
            match edit.action {
                AstEdit::PrependToBlock(new_stmt) => {
                    self.updated = true;
                    // Prepend the statement to the block.
                    block.stmts.insert(0, new_stmt);
                }
                _ => {
                    unreachable!();
                }
            }
        }
    }

    fn flat_map_stmt(&mut self, s: Stmt) -> smallvec::SmallVec<[Stmt; 1]> {
        let edit_vec = self.suggestions.pop_by_kind(
            s.span,
            vec![AstEditKind::ReplaceStmt, AstEditKind::RemoveStmt],
        );
        if edit_vec.is_empty() {
            mut_visit::walk_flat_map_stmt(self, s)
        } else {
            assert_eq!(edit_vec.len(), 1);
            let edit = edit_vec.into_iter().next().unwrap();
            match edit.action {
                AstEdit::ReplaceStmt(new_stmt) => {
                    self.updated = true;
                    // Replace the statement with the new statement.
                    smallvec![new_stmt]
                }
                AstEdit::RemoveStmt => {
                    self.updated = true;
                    // Remove the statement by returning an empty vector.
                    smallvec![]
                }
                _ => {
                    unreachable!()
                }
            }
        }
    }

    fn visit_pat(&mut self, pat: &mut Pat) {
        mut_visit::walk_pat(self, pat);
        let edit_vec = self
            .suggestions
            .pop_by_kind(pat.span, vec![AstEditKind::ReplacePat]);
        for edit in edit_vec {
            match edit.action {
                AstEdit::ReplacePat(new_pat) => {
                    self.updated = true;
                    *pat = new_pat;
                    pat.span = edit.span;
                }
                _ => {
                    unreachable!();
                }
            }
        }
    }

    fn visit_expr(&mut self, expr: &mut Expr) {
        mut_visit::walk_expr(self, expr);
        let edit_vec = self.suggestions.pop_by_kind(
            expr.span,
            vec![AstEditKind::ReplaceExpr, AstEditKind::RemoveExprField],
        );
        for edit in edit_vec {
            match edit.action {
                AstEdit::ReplaceExpr(new_expr) => {
                    self.updated = true;
                    *expr = new_expr;
                    expr.span = edit.span;
                }
                AstEdit::RemoveExprField(span) => {
                    let ExprKind::Struct(struct_expr) = &mut expr.kind else {
                        unreachable!(
                            "RemoveExprField should only be applied to a struct expression"
                        );
                    };
                    // Remove the field with the given span from the struct expression.
                    struct_expr.fields.retain(|field| {
                        // Retain fields that do not match the span of the field to be removed.
                        !(field.span.lo() == span.lo() && field.span.hi() == span.hi())
                    });
                    self.updated = true;
                }
                _ => {
                    unreachable!()
                }
            }
        }
    }

    fn visit_field_def(&mut self, field_def: &mut FieldDef) {
        mut_visit::walk_field_def(self, field_def);
        let edit_vec = self
            .suggestions
            .pop_by_kind(field_def.span, vec![AstEditKind::RemoveFieldAttr]);
        for edit in edit_vec {
            match edit.action {
                AstEdit::RemoveFieldAttr(span) => {
                    // Remove the attribute with the given span from the field definition.
                    field_def
                        .attrs
                        .retain(|attr| !self.suggestions.span_line_eq(attr.span, span));
                    self.updated = true;
                }
                _ => {
                    unreachable!();
                }
            }
        }
    }
}
