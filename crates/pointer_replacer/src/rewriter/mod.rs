use std::path::PathBuf;

use etrace::some_or;
use points_to::andersen;
use rustc_ast::mut_visit::MutVisitor;
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::{
    mir::Local,
    ty::{self, TyCtxt},
};
use rustc_span::def_id::LocalDefId;
use serde::Deserialize;
use transform::TransformVisitor;

use crate::{
    analyses::{
        self,
        borrow::{
            BorrowPromotionResults, PromotedMutRefs as PromotedMutRefResult,
            lifetime_flow::LifetimeFlowResults,
        },
        fn_ptr_groups::FnPtrGroups,
        fn_ptr_rewrite_decision::FnPtrRewriteDecision,
        offset_sign::sign::OffsetSignResult,
        output_params::OutputParams,
        ownership::{
            AnalysisKind as OwnershipAnalysisKind, CrateCtxt, solidify::SolidifiedOwnershipSchemes,
            whole_program::WholeProgramAnalysis,
        },
        struct_copy::StructCopyAnalysisResult,
        type_qualifier::foster::{fatness::FatnessResult, mutability::MutabilityResult},
    },
    utils::rustc::RustProgram,
};

pub(crate) mod array_local_index_rewriter;
pub(crate) mod collector;
pub(crate) mod decision;
pub(crate) mod diagnostics;
mod lifetimes;
pub(crate) mod serializer;
mod struct_array_field_pre;
mod transform;

pub struct Analysis {
    pub(crate) borrow_promotion_result: BorrowPromotionResults,
    pub(crate) borrow_lifetime_flows: LifetimeFlowResults,
    pub(crate) promoted_mut_ref_result: PromotedMutRefResult,
    pub(crate) promoted_shared_ref_result: PromotedMutRefResult,
    pub(crate) mutability_result: MutabilityResult,
    pub(crate) fatness_result: FatnessResult,
    pub(crate) aliases: FxHashMap<LocalDefId, FxHashMap<Local, FxHashSet<Local>>>,
    pub(crate) output_params: OutputParams,
    pub(crate) ownership_schemes: Option<SolidifiedOwnershipSchemes>,
    pub(crate) offset_sign_result: OffsetSignResult,
    pub(crate) nullity_result: analyses::nullity::NullityResult,
    pub(crate) struct_copy_result: StructCopyAnalysisResult,
}

#[derive(Debug, Default, Clone, Deserialize)]
pub struct Config {
    pub c_exposed_fns: FxHashSet<String>,
    #[serde(default)]
    pub verbose: bool,
    #[serde(default)]
    pub test_serialization: bool,
    #[serde(default)]
    pub dump_analysis_to: Option<PathBuf>,
    #[serde(default)]
    pub load_analysis_from: Option<PathBuf>,
    #[cfg(test)]
    pub force_ownership_analysis_failure: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BytemuckDependency {
    None,
    Runtime,
    MustCast,
    Derive,
}

impl BytemuckDependency {
    pub fn from_flags(runtime: bool, must_cast: bool, derive: bool) -> Self {
        match (runtime, must_cast, derive) {
            (_, _, true) => Self::Derive,
            (_, true, false) => Self::MustCast,
            (true, false, false) => Self::Runtime,
            (false, false, false) => Self::None,
        }
    }

    pub fn needs_runtime(self) -> bool {
        !matches!(self, Self::None)
    }

    pub fn needs_must_cast(self) -> bool {
        matches!(self, Self::MustCast | Self::Derive)
    }

    pub fn needs_derive(self) -> bool {
        matches!(self, Self::Derive)
    }
}

pub fn replace_local_borrows(config: &Config, tcx: TyCtxt<'_>) -> (String, BytemuckDependency) {
    let mut krate = utils::ast::expanded_ast(tcx);
    let ast_to_hir = utils::ast::make_ast_to_hir(&mut krate, tcx);
    utils::ast::remove_unnecessary_items_from_ast(&mut krate);

    let input = collect_input(tcx);
    let arena = typed_arena::Arena::new();
    let tss = utils::ty_shape::get_ty_shapes(&arena, tcx, false);
    let andersen_config = andersen::Config {
        use_optimized_mir: false,
        c_exposed_fns: config.c_exposed_fns.clone(),
    };
    let pre_points_to = andersen::pre_analyze(&andersen_config, &tss, tcx);
    let points_to_solutions = andersen::analyze(&andersen_config, &pre_points_to, &tss, tcx);

    let analysis_results = if let Some(path) = &config.load_analysis_from {
        serializer::load_analysis_from_file(path).unwrap_or_else(|err| {
            panic!(
                "failed to load pointer analysis from {}: {err:#}",
                path.display()
            )
        })
    } else {
        let aliases = find_param_aliases(&pre_points_to, &points_to_solutions, tcx);
        let points_to = andersen::post_analyze(
            &andersen_config,
            pre_points_to.clone(),
            points_to_solutions.clone(),
            &tss,
            tcx,
        );

        let mutability_result =
            analyses::type_qualifier::foster::mutability::mutability_analysis(&input);
        let output_params =
            analyses::output_params::compute_output_params(&input, &mutability_result, &aliases);
        let ownership_schemes = maybe_solidified_ownership(config, &input, &output_params);
        let source_var_groups = analyses::mir_variable_grouping::SourceVarGroups::new(&input);
        let mutables = source_var_groups.postprocess_mut_res(&input, &mutability_result);
        let borrow_promotion_result =
            analyses::borrow::mutable_references_no_guarantee(&input, &mutables);
        let borrow_lifetime_flows = borrow_promotion_result.lifetime_flows.clone();
        let struct_copy_result =
            analyses::struct_copy::analyze(&input, &borrow_promotion_result.mutable_fields);
        let promoted_mut_ref_result = source_var_groups
            .postprocess_promoted_mut_refs(borrow_promotion_result.mutable_locals.clone());
        let promoted_shared_ref_result = source_var_groups
            .postprocess_promoted_mut_refs(borrow_promotion_result.shared_locals.clone());
        let fatness_result = analyses::type_qualifier::foster::fatness::fatness_analysis(&input);
        let mut offset_sign_result = analyses::offset_sign::sign::offset_sign_analysis(&input);
        offset_sign_result.access_signs =
            source_var_groups.postprocess_offset_signs(offset_sign_result.access_signs);
        let mut nullity_result = analyses::nullity::analyze(&input, &points_to);
        nullity_result.non_null_locals =
            source_var_groups.postprocess_non_null_locals(nullity_result.non_null_locals);
        Analysis {
            borrow_promotion_result,
            borrow_lifetime_flows,
            promoted_mut_ref_result,
            promoted_shared_ref_result,
            mutability_result,
            fatness_result,
            aliases,
            output_params,
            ownership_schemes,
            offset_sign_result,
            nullity_result,
            struct_copy_result,
        }
    };
    let analysis_results = if config.test_serialization {
        let serialized = serializer::serialize_analysis(&analysis_results);
        serializer::deserialize_analysis(serialized)
    } else {
        analysis_results
    };
    if let Some(path) = &config.dump_analysis_to {
        serializer::dump_analysis_to_file(&analysis_results, path).unwrap_or_else(|err| {
            panic!(
                "failed to dump pointer analysis to {}: {err:#}",
                path.display()
            )
        });
    }

    let fn_ptr_groups = FnPtrGroups::build(
        &pre_points_to,
        &points_to_solutions,
        &input,
        &analysis_results,
    );
    let fn_ptr_rewrite = FnPtrRewriteDecision::build(
        &pre_points_to,
        &points_to_solutions,
        &input,
        &analysis_results,
        &tss,
        &fn_ptr_groups,
        &config.c_exposed_fns,
    );

    let diagnostics = diagnostics::DecisionDiagnostics::from_env();
    let mut visitor = TransformVisitor::new(
        config,
        &input,
        &analysis_results,
        &pre_points_to,
        &points_to_solutions,
        &tss,
        ast_to_hir,
        fn_ptr_groups,
        fn_ptr_rewrite,
        diagnostics,
    );
    visitor.visit_crate(&mut krate);

    // add SliceCursor module to the crate if it was used
    let slice_cursor_used = visitor.slice_cursor.get();
    let mut code = pprust::crate_to_string_for_macros(&krate);
    if slice_cursor_used {
        code.push('\n');
        code.push_str(slice_cursor_mod_str());
    }

    visitor.emit_diagnostics();

    (code, visitor.bytemuck_dependency())
}

pub fn rewrite_struct_arrays(config: &Config, tcx: TyCtxt<'_>) -> (String, bool) {
    let mut krate = utils::ast::expanded_ast(tcx);
    let ast_to_hir = utils::ast::make_ast_to_hir(&mut krate, tcx);
    utils::ast::remove_unnecessary_items_from_ast(&mut krate);

    let input = collect_input(tcx);
    let arena = typed_arena::Arena::new();
    let tss = utils::ty_shape::get_ty_shapes(&arena, tcx, false);
    let andersen_config = andersen::Config {
        use_optimized_mir: false,
        c_exposed_fns: config.c_exposed_fns.clone(),
    };
    let pre_points_to = andersen::pre_analyze(&andersen_config, &tss, tcx);
    let points_to = andersen::analyze(&andersen_config, &pre_points_to, &tss, tcx);
    let points_to = andersen::post_analyze(&andersen_config, pre_points_to, points_to, &tss, tcx);

    let candidates = analyses::struct_array_field::find_candidates(&input, &points_to);
    let changed = struct_array_field_pre::apply_struct_array_transform(
        &mut krate,
        &candidates,
        tcx,
        &ast_to_hir,
    );

    (pprust::crate_to_string_for_macros(&krate), changed)
}

pub fn rewrite_array_local_provenance(config: &Config, tcx: TyCtxt<'_>) -> (String, bool) {
    let mut krate = utils::ast::expanded_ast(tcx);
    let ast_to_hir = utils::ast::make_ast_to_hir(&mut krate, tcx);
    utils::ast::remove_unnecessary_items_from_ast(&mut krate);

    let input = collect_input(tcx);
    let arena = typed_arena::Arena::new();
    let tss = utils::ty_shape::get_ty_shapes(&arena, tcx, false);
    let andersen_config = andersen::Config {
        use_optimized_mir: false,
        c_exposed_fns: config.c_exposed_fns.clone(),
    };
    let pre_points_to = andersen::pre_analyze(&andersen_config, &tss, tcx);
    let alloc_fns = pre_points_to.alloc_fns.clone();
    let points_to_solutions = andersen::analyze(&andersen_config, &pre_points_to, &tss, tcx);
    let points_to = andersen::post_analyze(
        &andersen_config,
        pre_points_to,
        points_to_solutions,
        &tss,
        tcx,
    );
    let mutability_result =
        analyses::type_qualifier::foster::mutability::mutability_analysis(&input);
    let source_var_groups = analyses::mir_variable_grouping::SourceVarGroups::new(&input);
    let mut nullity_result = analyses::nullity::analyze(&input, &points_to);
    nullity_result.non_null_locals =
        source_var_groups.postprocess_non_null_locals(nullity_result.non_null_locals);
    let provenances =
        analyses::array_local_provenance::array_local_provenance_analysis(&input, &alloc_fns);

    let changed = array_local_index_rewriter::apply_array_local_index_rewrite(
        &mut krate,
        &input,
        &provenances,
        &mutability_result,
        &nullity_result,
        &points_to,
        &ast_to_hir,
    );

    (pprust::crate_to_string_for_macros(&krate), changed)
}

pub(crate) fn collect_input(tcx: TyCtxt<'_>) -> RustProgram<'_> {
    let mut functions = vec![];
    let mut structs = vec![];
    for maybe_owner in tcx.hir_crate(()).owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        match item.kind {
            ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
            ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
            _ => {}
        };
    }

    RustProgram {
        tcx,
        functions,
        structs,
    }
}

fn maybe_solidified_ownership<'tcx>(
    _config: &Config,
    input: &RustProgram<'tcx>,
    output_params: &OutputParams,
) -> Option<SolidifiedOwnershipSchemes> {
    #[cfg(test)]
    if _config.force_ownership_analysis_failure {
        return None;
    }

    let _verbose_guard = crate::analyses::ownership::whole_program::set_verbose(_config.verbose);
    let crate_ctxt = CrateCtxt::new(input);
    <WholeProgramAnalysis as OwnershipAnalysisKind>::analyze(crate_ctxt, output_params)
        .ok()
        .map(|results| results.solidify(input))
}

pub(crate) fn find_param_aliases<'tcx>(
    pre: &andersen::PreAnalysisData<'tcx>,
    points_to: &andersen::Solutions,
    tcx: TyCtxt<'tcx>,
) -> FxHashMap<LocalDefId, FxHashMap<Local, FxHashSet<Local>>> {
    let mut param_aliases = FxHashMap::default();
    for def_id in tcx.hir_body_owners() {
        let calls = some_or!(pre.call_args.get(&def_id), continue);
        let mut aliases: FxHashMap<_, FxHashSet<_>> = FxHashMap::default();
        let body = tcx.mir_drops_elaborated_and_const_checked(def_id).borrow();
        for call_args in calls {
            for i in 0..body.arg_count {
                for j in 0..i {
                    let arg_i = some_or!(call_args[i], continue);
                    let arg_j = some_or!(call_args[j], continue);
                    let mut sol_i = points_to[arg_i].clone();
                    sol_i.intersect(&points_to[arg_j]);
                    if !sol_i.is_empty() {
                        let i = Local::from_usize(i + 1);
                        let j = Local::from_usize(j + 1);
                        aliases.entry(i).or_default().insert(j);
                        aliases.entry(j).or_default().insert(i);
                    }
                }
            }
        }
        if !aliases.is_empty() {
            param_aliases.insert(def_id, aliases);
        }
    }
    param_aliases
}

#[allow(unused)]
fn print_nullity_counts(
    input: &RustProgram<'_>,
    nullity_result: &analyses::nullity::NullityResult,
) {
    for &did in &input.functions {
        let body = input
            .tcx
            .mir_drops_elaborated_and_const_checked(did)
            .borrow();
        let raw_pointer_params = body
            .args_iter()
            .filter(|&local| matches!(body.local_decls[local].ty.kind(), ty::TyKind::RawPtr(..)))
            .collect::<Vec<_>>();
        let total = raw_pointer_params.len();
        if total == 0 {
            continue;
        }

        let non_null = nullity_result
            .non_null_params
            .get(&did)
            .map(|params| {
                raw_pointer_params
                    .iter()
                    .filter(|&&local| params.contains(local))
                    .count()
            })
            .unwrap_or(0);

        println!(
            "crat_nullity\t{}\t{}\t{}",
            input.tcx.def_path_str(did.to_def_id()),
            total,
            non_null
        );
    }
}

fn slice_cursor_mod_str() -> &'static str {
    r#"pub mod slice_cursor {
    use std::ops::Index;
    use std::ops::IndexMut;
    use std::ops::Range;
    use std::ops::RangeFrom;
    use std::ops::RangeFull;
    use std::ops::RangeTo;

    pub struct SliceCursorMut<'a, T> {
        base: &'a mut [T],
        pos: usize,
    }

    impl<'a, T> SliceCursorMut<'a, T> {
        pub const fn new(base: &'a mut [T]) -> Self {
            Self { base, pos: 0 }
        }

        pub const fn with_pos(base: &'a mut [T], pos: usize) -> Self {
            Self { base, pos }
        }

        pub const fn empty() -> Self {
            Self { base: &mut [], pos: 0 }
        }

        pub const fn from_mut(val: &'a mut T) -> Self {
            Self { base: std::slice::from_mut(val), pos: 0 }
        }

        pub const unsafe fn from_raw_parts(ptr: *const T, len: usize) -> Self {
            unsafe { Self::from_raw_parts_mut(ptr as *mut T, len) }
        }

        pub const unsafe fn from_raw_parts_mut(ptr: *mut T, len: usize) -> Self {
            Self { base: unsafe { std::slice::from_raw_parts_mut(ptr, len) }, pos: 0 }
        }

        pub fn as_deref_mut(&mut self) -> SliceCursorMut<'_, T> {
            SliceCursorMut { base: &mut self.base[..], pos: self.pos }
        }

        pub fn as_deref(&self) -> SliceCursor<'_, T> {
            SliceCursor { base: &self.base[..], pos: self.pos }
        }

        pub fn into_deref(self) -> SliceCursor<'a, T> {
            SliceCursor { base: self.base, pos: self.pos }
        }

        pub const fn seek(&mut self, offset: isize) {
            self.pos = self.pos.wrapping_add_signed(offset);
        }

        pub const fn offset_by(mut self, offset: isize) -> Self {
            self.seek(offset);
            self
        }

        pub fn is_empty(&self) -> bool {
            self.pos >= self.base.len()
        }

        pub fn as_mut_ptr(&mut self) -> *mut T {
            self.base[self.pos..].as_mut_ptr()
        }

        pub fn as_ptr(&self) -> *const T {
            self.base[self.pos..].as_ptr()
        }

        pub fn first(&self) -> Option<&T> {
            self.base.get(self.pos)
        }

        pub fn first_mut(&mut self) -> Option<&mut T> {
            self.base.get_mut(self.pos)
        }

        pub fn as_slice(&self) -> &[T] {
            &self.base[self.pos..]
        }

        pub fn as_slice_mut(&mut self) -> &mut [T] {
            &mut self.base[self.pos..]
        }
    }

    pub struct SliceCursor<'a, T> {
        base: &'a [T],
        pos: usize,
    }

    impl<'a, T> Copy for SliceCursor<'a, T> {}

    impl<'a, T> Clone for SliceCursor<'a, T> {
        fn clone(&self) -> Self {
            *self
        }
    }

    impl<'a, T> SliceCursor<'a, T> {
        pub const fn new(slice: &'a [T]) -> Self {
            Self { base: slice, pos: 0 }
        }

        pub const fn with_pos(base: &'a [T], pos: usize) -> Self {
            Self { base, pos }
        }

        pub const fn empty() -> Self {
            Self { base: &[], pos: 0 }
        }

        pub const fn from_ref(val: &'a T) -> Self {
            Self { base: std::slice::from_ref(val), pos: 0 }
        }

        pub const unsafe fn from_raw_parts(ptr: *const T, len: usize) -> Self {
            Self { base: unsafe { std::slice::from_raw_parts(ptr, len) }, pos: 0 }
        }

        pub const fn seek(&mut self, offset: isize) {
            self.pos = self.pos.wrapping_add_signed(offset);
        }

        pub const fn offset_by(mut self, offset: isize) -> Self {
            self.seek(offset);
            self
        }

        pub fn is_empty(&self) -> bool {
            self.pos >= self.base.len()
        }

        pub fn as_ptr(&self) -> *const T {
            self.base[self.pos..].as_ptr()
        }

        pub fn first(&self) -> Option<&T> {
            self.base.get(self.pos)
        }

        pub fn as_slice(&self) -> &'a [T] {
            &self.base[self.pos..]
        }
    }

    #[inline(always)]
    fn abs_idx(pos: usize, index: isize) -> usize {
        pos.wrapping_add_signed(index)
    }

    macro_rules! impl_readable_index {
        ($cursor_type:ident, $($idx_type:ty),*) => {
            $(
                impl<T> Index<$idx_type> for $cursor_type<'_, T> {
                    type Output = T;
                    #[inline]
                    fn index(&self, index: $idx_type) -> &Self::Output {
                        &self.base[abs_idx(self.pos, index as isize)]
                    }
                }

                impl<T> Index<Range<$idx_type>> for $cursor_type<'_, T> {
                    type Output = [T];
                    #[inline]
                    fn index(&self, range: Range<$idx_type>) -> &Self::Output {
                        let start = abs_idx(self.pos, range.start as isize);
                        let end = abs_idx(self.pos, range.end as isize);
                        &self.base[start..end]
                    }
                }

                impl<T> Index<RangeFrom<$idx_type>> for $cursor_type<'_, T> {
                    type Output = [T];
                    #[inline]
                    fn index(&self, range: RangeFrom<$idx_type>) -> &Self::Output {
                        let start = abs_idx(self.pos, range.start as isize);
                        &self.base[start..]
                    }
                }

                impl<T> Index<RangeTo<$idx_type>> for $cursor_type<'_, T> {
                    type Output = [T];
                    #[inline]
                    fn index(&self, range: RangeTo<$idx_type>) -> &Self::Output {
                        let end = abs_idx(self.pos, range.end as isize);
                        &self.base[self.pos..end]
                    }
                }
            )*

            impl<T> Index<RangeFull> for $cursor_type<'_, T> {
                type Output = [T];
                #[inline]
                fn index(&self, _: RangeFull) -> &Self::Output {
                    &self.base[self.pos..]
                }
            }
        };
    }

    macro_rules! impl_mutable_index {
        ($($idx_type:ty),*) => {
            $(
                impl<T> IndexMut<$idx_type> for SliceCursorMut<'_, T> {
                    #[inline]
                    fn index_mut(&mut self, index: $idx_type) -> &mut Self::Output {
                        let i = abs_idx(self.pos, index as isize);
                        &mut self.base[i]
                    }
                }

                impl<T> IndexMut<Range<$idx_type>> for SliceCursorMut<'_, T> {
                    #[inline]
                    fn index_mut(&mut self, range: Range<$idx_type>) -> &mut Self::Output {
                        let start = abs_idx(self.pos, range.start as isize);
                        let end = abs_idx(self.pos, range.end as isize);
                        &mut self.base[start..end]
                    }
                }

                impl<T> IndexMut<RangeFrom<$idx_type>> for SliceCursorMut<'_, T> {
                    #[inline]
                    fn index_mut(&mut self, range: RangeFrom<$idx_type>) -> &mut Self::Output {
                        let start = abs_idx(self.pos, range.start as isize);
                        &mut self.base[start..]
                    }
                }

                impl<T> IndexMut<RangeTo<$idx_type>> for SliceCursorMut<'_, T> {
                    #[inline]
                    fn index_mut(&mut self, range: RangeTo<$idx_type>) -> &mut Self::Output {
                        let end = abs_idx(self.pos, range.end as isize);
                        &mut self.base[self.pos..end]
                    }
                }
            )*

            impl<T> IndexMut<RangeFull> for SliceCursorMut<'_, T> {
                #[inline]
                fn index_mut(&mut self, _: RangeFull) -> &mut Self::Output {
                    &mut self.base[self.pos..]
                }
            }
        };
    }

    impl_readable_index!(SliceCursorMut, isize, usize, i32);
    impl_readable_index!(SliceCursor, isize, usize, i32);
    impl_mutable_index!(isize, usize, i32);
}"#
}
