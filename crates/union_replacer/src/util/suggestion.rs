use rustc_ast::{ast::*, ptr::P};
use rustc_ast_pretty::pprust;
use rustc_hash::FxHashMap;
use rustc_span::{BytePos, Span, source_map::SourceMap};
use thin_vec::ThinVec;

use super::transform::TransformVisitor;

#[derive(Clone)]
pub struct AstSuggestions<'tcx> {
    pub suggestions: FxHashMap<LoHi, Vec<AstSuggestion>>,
    source_map: &'tcx SourceMap,
}

impl std::fmt::Debug for AstSuggestions<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map().entries(self.suggestions.iter()).finish()
    }
}

impl<'tcx> AstSuggestions<'tcx> {
    pub fn new(source_map: &'tcx SourceMap) -> Self {
        Self {
            suggestions: FxHashMap::default(),
            source_map,
        }
    }

    pub fn into_transform_visitor(self) -> TransformVisitor<'tcx> {
        TransformVisitor {
            suggestions: self,
            updated: false,
        }
    }

    #[allow(unused)]
    pub fn print_suggestions(&self) {
        for (lohi, vec) in &self.suggestions {
            println!("Suggestions for {lohi:?}:");
            for suggestion in vec {
                println!(
                    "\n  - {:?} {}:\n{}",
                    suggestion.span.data(),
                    suggestion.action,
                    self.source_map
                        .span_to_snippet(suggestion.span)
                        .unwrap_or_else(|_| "<snippet unavailable>".to_string())
                );
            }
        }
    }

    pub fn assert_empty(&self) {
        for vec in self.suggestions.values() {
            if !vec.is_empty() {
                panic!(
                    "AstSuggestions is not empty: {:?}",
                    vec.iter().map(|s| s.span).collect::<Vec<_>>()
                );
            }
        }
    }

    pub fn add(&mut self, span: Span, replacement: AstEdit) {
        self.suggestions
            .entry(LoHi::from_span(span))
            .or_default()
            .push(AstSuggestion {
                span,
                action: replacement,
            });
    }

    pub(super) fn pop_by_kind(
        &mut self,
        span: Span,
        kinds: Vec<AstEditKind>,
    ) -> Vec<AstSuggestion> {
        // Suppose the suggestions are distinct by span and path.
        let vec = match self.suggestions.get_mut(&LoHi::from_span(span)) {
            Some(vec) => vec,
            None => return vec![],
        };
        vec.extract_if(.., |s| kinds.contains(&s.action.kind()))
            .collect()
    }

    pub(super) fn span_line_eq(&self, span1: Span, span2: Span) -> bool {
        let span1_expanded = self.source_map.span_extend_to_line(span1);
        let span2_expanded = self.source_map.span_extend_to_line(span2);
        span1_expanded.lo() == span2_expanded.lo() && span1_expanded.hi() == span2_expanded.hi()
    }
}

macro_rules! define_ast_edit {
    (
        $( $variant:ident $( ( $ty:ty ) )? ),* $(,)?
    ) => {
        #[derive(Debug, Clone)]
        #[allow(unused)]
        pub enum AstEdit {
            $(
                $variant $( ( $ty ) )?,
            )*
        }

        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        pub enum AstEditKind {
            $(
                $variant,
            )*
        }

        impl AstEdit {
            pub fn kind(&self) -> AstEditKind {
                match self {
                    $(
                        Self::$variant { .. } => AstEditKind::$variant,
                    )*
                }
            }
        }
    };
}

define_ast_edit!(
    // Handled by visit_crate
    AppendAfterItem(Item),
    FlatMapItemsWithAttrs(ThinVec<P<Item>>), /* Given a item's span, replace it with these items. Leave the original Attributes to the first item. */
    // Handled by visit_item
    ReplaceItem(Item),
    RemoveFieldDef(Span), /* Given the parent Item(kind: struct)'s span, remove a field definition of this span. */
    // handled by visit_block
    PrependToBlock(Stmt), /* For a block expression matching the span, prepend the statement to the block. */
    // Handled by visit_stmt
    ReplaceStmt(Stmt),
    RemoveStmt,
    // Handled by visit_pat
    ReplacePat(Pat),
    // Handled by visit_expr
    ReplaceExpr(Expr),
    RemoveExprField(Span), /* Given the parent Expr's span, remove a field definition of this span. */
    // Handled by visit_field_def
    RemoveFieldAttr(Span), /* Given the parent FieldDef's span, remove a field attribute of this span. */
);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LoHi {
    lo: BytePos,
    hi: BytePos,
}

impl LoHi {
    #[inline]
    fn new(lo: BytePos, hi: BytePos) -> Self {
        Self { lo, hi }
    }

    #[inline]
    fn from_span(span: Span) -> Self {
        Self::new(span.lo(), span.hi())
    }
}

impl std::fmt::Display for AstEdit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::AppendAfterItem(item) => {
                write!(f, "AppendAfterItem({})", pprust::item_to_string(item))
            }
            Self::FlatMapItemsWithAttrs(_) => {
                write!(f, "ReplaceItems()")
            }
            Self::ReplaceItem(item) => write!(f, "ReplaceItem({})", pprust::item_to_string(item)),
            Self::RemoveFieldDef(span) => write!(f, "RemoveFieldDef({span:?})"),
            Self::PrependToBlock(stmt) => {
                write!(f, "PrependToBlock({stmt:?})")
            }
            Self::ReplaceStmt(stmt) => write!(f, "ReplaceStmt({stmt:?})"),
            Self::RemoveStmt => write!(f, "RemoveStmt"),
            Self::ReplacePat(pat) => write!(f, "ReplacePat({pat:?})"),
            Self::ReplaceExpr(expr) => write!(f, "ReplaceExpr({:?})", pprust::expr_to_string(expr)),
            Self::RemoveExprField(span) => write!(f, "RemoveExprField({span:?})"),
            Self::RemoveFieldAttr(span) => write!(f, "RemoveFieldAttr({span:?})"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct AstSuggestion {
    pub span: Span,
    pub action: AstEdit,
}
