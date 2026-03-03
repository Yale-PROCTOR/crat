use std::collections::BTreeMap;

use rustc_ast::{
    Crate, Expr, ExprKind, Path,
    mut_visit::{self, MutVisitor},
};

pub(crate) const ALLOC_UNSAFE_CALLEES: [&str; 4] = ["malloc", "calloc", "realloc", "strdup"];
pub(crate) const CALL240_ALLOCATOR_CALLEES: [&str; 2] = ["malloc", "calloc"];
pub(crate) const BOX_NEW_CALLEES: [&str; 1] = ["Box::new"];
pub(crate) const ALLOCATOR_REASON_KEYS: [&str; 3] = [
    "call240_applied",
    "call250_non_move_required",
    "call240_compile_risk_default_missing",
];
pub(crate) const RAW_CONSTRUCTOR_UNSAFE_CALLEES: [&str; 7] = [
    "Box::from_raw",
    "Box::into_raw",
    "std::slice::from_raw_parts",
    "std::slice::from_raw_parts_mut",
    "crate::slice_cursor::SliceCursor::from_raw_parts",
    "crate::slice_cursor::SliceCursor::from_raw_parts_mut",
    "crate::slice_cursor::SliceCursorRef::from_raw_parts",
];

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct BeforeAfterCounts {
    pub before_total: usize,
    pub after_total: usize,
    pub before_by_callee: BTreeMap<String, usize>,
    pub after_by_callee: BTreeMap<String, usize>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct RewriteStats {
    pub alloc_unsafe: BeforeAfterCounts,
    pub box_new: BeforeAfterCounts,
    pub raw_constructor_unsafe: BeforeAfterCounts,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum AllocatorReason {
    Call240Applied,
    Call250NonMoveRequired,
    Call240CompileRiskDefaultMissing,
}

impl AllocatorReason {
    pub(crate) fn key(self) -> &'static str {
        match self {
            AllocatorReason::Call240Applied => "call240_applied",
            AllocatorReason::Call250NonMoveRequired => "call250_non_move_required",
            AllocatorReason::Call240CompileRiskDefaultMissing => {
                "call240_compile_risk_default_missing"
            }
        }
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct AllocatorReasonStats {
    pub by_reason: BTreeMap<String, usize>,
    pub by_allocator: BTreeMap<String, BTreeMap<String, usize>>,
}

impl AllocatorReasonStats {
    pub(crate) fn record(&mut self, reason: AllocatorReason, allocator: &'static str) {
        *self.by_reason.entry(reason.key().to_owned()).or_default() += 1;
        *self
            .by_allocator
            .entry(allocator.to_owned())
            .or_default()
            .entry(reason.key().to_owned())
            .or_default() += 1;
    }

    pub(crate) fn merge_from(&mut self, other: &AllocatorReasonStats) {
        for (reason, count) in &other.by_reason {
            *self.by_reason.entry(reason.clone()).or_default() += *count;
        }
        for (allocator, by_reason) in &other.by_allocator {
            let dst = self.by_allocator.entry(allocator.clone()).or_default();
            for (reason, count) in by_reason {
                *dst.entry(reason.clone()).or_default() += *count;
            }
        }
    }

    pub(crate) fn reason_count(&self, reason: AllocatorReason) -> usize {
        self.by_reason.get(reason.key()).copied().unwrap_or(0)
    }

    pub(crate) fn reason_count_for_allocator(
        &self,
        allocator: &str,
        reason: AllocatorReason,
    ) -> usize {
        self.by_allocator
            .get(allocator)
            .and_then(|counts| counts.get(reason.key()))
            .copied()
            .unwrap_or(0)
    }
}

#[derive(Debug, Clone, Default)]
pub(crate) struct CallMetricSnapshot {
    pub alloc_unsafe: BTreeMap<String, usize>,
    pub box_new: BTreeMap<String, usize>,
    pub raw_constructor_unsafe: BTreeMap<String, usize>,
}

#[derive(Clone, Copy)]
enum MetricFamily {
    AllocUnsafe,
    BoxNew,
    RawConstructorUnsafe,
}

pub(crate) fn collect_call_metrics(krate: &mut Crate) -> CallMetricSnapshot {
    let mut collector = DirectCallCollector::default();
    collector.visit_crate(krate);
    collector.snapshot
}

pub(crate) fn build_rewrite_stats(
    before: CallMetricSnapshot,
    after: CallMetricSnapshot,
) -> RewriteStats {
    RewriteStats {
        alloc_unsafe: build_before_after_counts(before.alloc_unsafe, after.alloc_unsafe),
        box_new: build_before_after_counts(before.box_new, after.box_new),
        raw_constructor_unsafe: build_before_after_counts(
            before.raw_constructor_unsafe,
            after.raw_constructor_unsafe,
        ),
    }
}

fn build_before_after_counts(
    before_by_callee: BTreeMap<String, usize>,
    after_by_callee: BTreeMap<String, usize>,
) -> BeforeAfterCounts {
    BeforeAfterCounts {
        before_total: before_by_callee.values().sum(),
        after_total: after_by_callee.values().sum(),
        before_by_callee,
        after_by_callee,
    }
}

#[derive(Default)]
struct DirectCallCollector {
    snapshot: CallMetricSnapshot,
}

impl MutVisitor for DirectCallCollector {
    fn visit_expr(&mut self, expr: &mut Expr) {
        if let ExprKind::Call(callee, _) = &mut expr.kind
            && let Some((family, callee_name)) = classify_direct_call(callee)
        {
            let map = match family {
                MetricFamily::AllocUnsafe => &mut self.snapshot.alloc_unsafe,
                MetricFamily::BoxNew => &mut self.snapshot.box_new,
                MetricFamily::RawConstructorUnsafe => &mut self.snapshot.raw_constructor_unsafe,
            };
            *map.entry(callee_name.to_owned()).or_default() += 1;
        }
        mut_visit::walk_expr(self, expr);
    }
}

fn classify_direct_call(expr: &Expr) -> Option<(MetricFamily, &'static str)> {
    match &strip_paren_and_cast(expr).kind {
        ExprKind::Path(_, path) => classify_path(path),
        _ => None,
    }
}

pub(crate) fn classify_call240_allocator_source_expr(expr: &Expr) -> Option<&'static str> {
    let ExprKind::Call(callee, _) = &strip_paren_and_cast(expr).kind else {
        return None;
    };
    let ExprKind::Path(_, path) = &strip_paren_and_cast(callee).kind else {
        return None;
    };
    let segments = path
        .segments
        .iter()
        .map(|segment| segment.ident.name.as_str())
        .collect::<Vec<_>>();
    if path_ends_with(&segments, &["malloc"]) {
        return Some("malloc");
    }
    if path_ends_with(&segments, &["calloc"]) {
        return Some("calloc");
    }
    None
}

fn strip_paren_and_cast(mut expr: &Expr) -> &Expr {
    loop {
        match &expr.kind {
            ExprKind::Paren(inner) | ExprKind::Cast(inner, _) => {
                expr = inner;
            }
            _ => return expr,
        }
    }
}

fn classify_path(path: &Path) -> Option<(MetricFamily, &'static str)> {
    let segments = path
        .segments
        .iter()
        .map(|segment| segment.ident.name.as_str())
        .collect::<Vec<_>>();
    if path_ends_with(&segments, &["malloc"]) {
        return Some((MetricFamily::AllocUnsafe, "malloc"));
    }
    if path_ends_with(&segments, &["calloc"]) {
        return Some((MetricFamily::AllocUnsafe, "calloc"));
    }
    if path_ends_with(&segments, &["realloc"]) {
        return Some((MetricFamily::AllocUnsafe, "realloc"));
    }
    if path_ends_with(&segments, &["strdup"]) {
        return Some((MetricFamily::AllocUnsafe, "strdup"));
    }
    if path_ends_with(&segments, &["Box", "new"]) {
        return Some((MetricFamily::BoxNew, "Box::new"));
    }
    if path_ends_with(&segments, &["Box", "from_raw"]) {
        return Some((MetricFamily::RawConstructorUnsafe, "Box::from_raw"));
    }
    if path_ends_with(&segments, &["Box", "into_raw"]) {
        return Some((MetricFamily::RawConstructorUnsafe, "Box::into_raw"));
    }
    if path_ends_with(&segments, &["std", "slice", "from_raw_parts"]) {
        return Some((
            MetricFamily::RawConstructorUnsafe,
            "std::slice::from_raw_parts",
        ));
    }
    if path_ends_with(&segments, &["std", "slice", "from_raw_parts_mut"]) {
        return Some((
            MetricFamily::RawConstructorUnsafe,
            "std::slice::from_raw_parts_mut",
        ));
    }
    if path_ends_with(
        &segments,
        &["crate", "slice_cursor", "SliceCursor", "from_raw_parts"],
    ) {
        return Some((
            MetricFamily::RawConstructorUnsafe,
            "crate::slice_cursor::SliceCursor::from_raw_parts",
        ));
    }
    if path_ends_with(
        &segments,
        &["crate", "slice_cursor", "SliceCursor", "from_raw_parts_mut"],
    ) {
        return Some((
            MetricFamily::RawConstructorUnsafe,
            "crate::slice_cursor::SliceCursor::from_raw_parts_mut",
        ));
    }
    if path_ends_with(
        &segments,
        &["crate", "slice_cursor", "SliceCursorRef", "from_raw_parts"],
    ) {
        return Some((
            MetricFamily::RawConstructorUnsafe,
            "crate::slice_cursor::SliceCursorRef::from_raw_parts",
        ));
    }
    None
}

fn path_ends_with(segments: &[&str], suffix: &[&str]) -> bool {
    segments.len() >= suffix.len() && segments[segments.len() - suffix.len()..] == *suffix
}

#[cfg(test)]
mod tests {
    use rustc_middle::ty::TyCtxt;

    use super::*;

    fn collect_metrics_for_code(code: &str) -> CallMetricSnapshot {
        ::utils::compilation::run_compiler_on_str(code, |tcx| collect_metrics_for_tcx(tcx))
            .unwrap_or_else(|e| e.raise())
    }

    fn collect_metrics_for_tcx(tcx: TyCtxt<'_>) -> CallMetricSnapshot {
        let mut krate = utils::ast::expanded_ast(tcx);
        let _ = utils::ast::make_ast_to_hir(&mut krate, tcx);
        utils::ast::remove_unnecessary_items_from_ast(&mut krate);
        collect_call_metrics(&mut krate)
    }

    #[test]
    fn counts_direct_allocator_calls() {
        let code = r#"
            unsafe extern "C" {
                fn malloc(size: usize) -> *mut core::ffi::c_void;
            }

            unsafe fn f() {
                let _ = malloc(8);
            }
        "#;
        let metrics = collect_metrics_for_code(code);
        assert_eq!(metrics.alloc_unsafe.get("malloc"), Some(&1));
        assert_eq!(metrics.alloc_unsafe.values().sum::<usize>(), 1);
    }

    #[test]
    fn ignores_allocator_declaration_without_call() {
        let code = r#"
            unsafe extern "C" {
                fn malloc(size: usize) -> *mut core::ffi::c_void;
            }

            fn f() {}
        "#;
        let metrics = collect_metrics_for_code(code);
        assert_eq!(metrics.alloc_unsafe.values().sum::<usize>(), 0);
    }

    #[test]
    fn ignores_wrapper_calls() {
        let code = r#"
            fn os_calloc(size: usize) -> *mut core::ffi::c_void {
                core::ptr::null_mut::<core::ffi::c_void>()
            }

            fn f() {
                let _ = os_calloc(8);
            }
        "#;
        let metrics = collect_metrics_for_code(code);
        assert_eq!(metrics.alloc_unsafe.get("calloc"), None);
        assert_eq!(metrics.alloc_unsafe.values().sum::<usize>(), 0);
    }

    #[test]
    fn detects_box_new_calls() {
        let code = r#"
            fn f() {
                let _ = Box::new(1usize);
                let _ = std::boxed::Box::new(2usize);
            }
        "#;
        let metrics = collect_metrics_for_code(code);
        assert_eq!(metrics.box_new.get("Box::new"), Some(&2));
    }

    #[test]
    fn detects_all_raw_constructor_calls() {
        let code = r#"
            pub mod slice_cursor {
                pub struct SliceCursor<T>(core::marker::PhantomData<T>);
                pub struct SliceCursorRef<T>(core::marker::PhantomData<T>);

                impl<T> SliceCursor<T> {
                    pub fn from_raw_parts(_ptr: *const T, _len: usize) -> Self {
                        Self(core::marker::PhantomData)
                    }
                    pub fn from_raw_parts_mut(_ptr: *mut T, _len: usize) -> Self {
                        Self(core::marker::PhantomData)
                    }
                }

                impl<T> SliceCursorRef<T> {
                    pub fn from_raw_parts(_ptr: *const T, _len: usize) -> Self {
                        Self(core::marker::PhantomData)
                    }
                }
            }

            fn f() {
                let b = Box::new(10i32);
                let p = Box::into_raw(b);
                let _ = unsafe { Box::from_raw(p) };

                let xs = [1i32, 2i32];
                let p_const = xs.as_ptr();
                let mut ys = [3i32, 4i32];
                let p_mut = ys.as_mut_ptr();

                let _ = unsafe { std::slice::from_raw_parts(p_const, 2) };
                let _ = unsafe { std::slice::from_raw_parts_mut(p_mut, 2) };
                let _ = crate::slice_cursor::SliceCursor::from_raw_parts(p_const, 2);
                let _ = crate::slice_cursor::SliceCursor::from_raw_parts_mut(p_mut, 2);
                let _ = crate::slice_cursor::SliceCursorRef::from_raw_parts(p_const, 2);
            }
        "#;
        let metrics = collect_metrics_for_code(code);
        for callee in RAW_CONSTRUCTOR_UNSAFE_CALLEES {
            assert_eq!(
                metrics.raw_constructor_unsafe.get(callee),
                Some(&1),
                "missing count for {callee}"
            );
        }
        assert_eq!(metrics.raw_constructor_unsafe.values().sum::<usize>(), 7);
    }

    #[test]
    fn allocator_reason_stats_merge_and_lookup() {
        let mut lhs = AllocatorReasonStats::default();
        lhs.record(AllocatorReason::Call240Applied, "malloc");
        lhs.record(AllocatorReason::Call240CompileRiskDefaultMissing, "malloc");

        let mut rhs = AllocatorReasonStats::default();
        rhs.record(AllocatorReason::Call250NonMoveRequired, "calloc");
        rhs.record(AllocatorReason::Call240Applied, "malloc");

        lhs.merge_from(&rhs);

        assert_eq!(lhs.reason_count(AllocatorReason::Call240Applied), 2);
        assert_eq!(lhs.reason_count(AllocatorReason::Call250NonMoveRequired), 1);
        assert_eq!(
            lhs.reason_count_for_allocator("malloc", AllocatorReason::Call240Applied),
            2
        );
        assert_eq!(
            lhs.reason_count_for_allocator("calloc", AllocatorReason::Call250NonMoveRequired),
            1
        );
    }
}
