use etrace::some_or;
use points_to::andersen;
use rustc_ast::mut_visit::MutVisitor;
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::{mir::Local, ty::TyCtxt};
use rustc_span::def_id::LocalDefId;
use serde::Deserialize;
use transform::TransformVisitor;

use crate::{
    analyses::{
        self,
        borrow::PromotedMutRefs as PromotedMutRefResult,
        offset_sign::sign::OffsetSignResult,
        output_params::OutputParams,
        ownership::{
            AnalysisKind as OwnershipAnalysisKind, CrateCtxt, solidify::SolidifiedOwnershipSchemes,
            whole_program::WholeProgramAnalysis,
        },
        type_qualifier::foster::{fatness::FatnessResult, mutability::MutabilityResult},
    },
    utils::rustc::RustProgram,
};

mod collector;
mod decision;
mod transform;

pub struct Analysis {
    promoted_mut_ref_result: PromotedMutRefResult,
    promoted_shared_ref_result: PromotedMutRefResult,
    mutability_result: MutabilityResult,
    fatness_result: FatnessResult,
    aliases: FxHashMap<LocalDefId, FxHashMap<Local, FxHashSet<Local>>>,
    output_params: OutputParams,
    ownership_schemes: Option<SolidifiedOwnershipSchemes>,
    offset_sign_result: OffsetSignResult,
}

#[derive(Debug, Default, Clone, Deserialize)]
pub struct Config {
    pub c_exposed_fns: FxHashSet<String>,
    #[serde(default)]
    pub verbose: bool,
    #[cfg(test)]
    pub force_ownership_analysis_failure: bool,
}

pub fn replace_local_borrows(config: &Config, tcx: TyCtxt<'_>) -> (String, bool) {
    let mut krate = utils::ast::expanded_ast(tcx);
    let ast_to_hir = utils::ast::make_ast_to_hir(&mut krate, tcx);
    utils::ast::remove_unnecessary_items_from_ast(&mut krate);

    let arena = typed_arena::Arena::new();
    let tss = utils::ty_shape::get_ty_shapes(&arena, tcx, false);
    let andersen_config = andersen::Config {
        use_optimized_mir: false,
        c_exposed_fns: config.c_exposed_fns.clone(),
    };
    let pre_points_to = andersen::pre_analyze(&andersen_config, &tss, tcx);
    let points_to = andersen::analyze(&andersen_config, &pre_points_to, &tss, tcx);
    let aliases = find_param_aliases(&pre_points_to, &points_to, tcx);

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
    let input = RustProgram {
        tcx,
        functions,
        structs,
    };

    let mutability_result =
        analyses::type_qualifier::foster::mutability::mutability_analysis(&input);
    let output_params =
        analyses::output_params::compute_output_params(&input, &mutability_result, &aliases);
    let ownership_schemes = maybe_solidified_ownership(config, &input, &output_params);
    let source_var_groups = analyses::mir_variable_grouping::SourceVarGroups::new(&input);
    let mutables = source_var_groups.postprocess_mut_res(&input, &mutability_result);
    let (mutable_references, shared_references) =
        analyses::borrow::mutable_references_no_guarantee(&input, &mutables);
    let promoted_mut_ref_result =
        source_var_groups.postprocess_promoted_mut_refs(mutable_references);
    let promoted_shared_ref_result =
        source_var_groups.postprocess_promoted_mut_refs(shared_references);
    let fatness_result = analyses::type_qualifier::foster::fatness::fatness_analysis(&input);
    let mut offset_sign_result = analyses::offset_sign::sign::offset_sign_analysis(&input);
    offset_sign_result.access_signs =
        source_var_groups.postprocess_offset_signs(offset_sign_result.access_signs);
    let analysis_results = Analysis {
        promoted_mut_ref_result,
        promoted_shared_ref_result,
        mutability_result,
        fatness_result,
        aliases,
        output_params,
        ownership_schemes,
        offset_sign_result,
    };

    let mut visitor = TransformVisitor::new(&input, &analysis_results, ast_to_hir);
    visitor.visit_crate(&mut krate);

    // add SliceCursor module to the crate if it was used
    let slice_cursor_used = visitor.slice_cursor.get();
    let mut code = pprust::crate_to_string_for_macros(&krate);
    if slice_cursor_used {
        code.push('\n');
        code.push_str(slice_cursor_mod_str());
    }

    (code, visitor.bytemuck.get())
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

fn find_param_aliases<'tcx>(
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
        pub fn new(base: &'a mut [T]) -> Self {
            Self { base, pos: 0 }
        }

        pub fn with_pos(base: &'a mut [T], pos: usize) -> Self {
            Self { base, pos }
        }

        pub fn empty() -> Self {
            Self { base: &mut [], pos: 0 }
        }

        pub fn from_mut(val: &'a mut T) -> Self {
            Self { base: std::slice::from_mut(val), pos: 0 }
        }

        pub unsafe fn from_raw_parts(ptr: *const T, len: usize) -> Self {
            unsafe { Self::from_raw_parts_mut(ptr as *mut T, len) }
        }

        pub unsafe fn from_raw_parts_mut(ptr: *mut T, len: usize) -> Self {
            Self { base: unsafe { std::slice::from_raw_parts_mut(ptr, len) }, pos: 0 }
        }

        pub fn as_deref_mut(&mut self) -> SliceCursorMut<'_, T> {
            SliceCursorMut { base: &mut self.base[..], pos: self.pos }
        }

        pub fn as_deref(self) -> SliceCursor<'a, T> {
            SliceCursor { base: self.base, pos: self.pos }
        }

        pub fn seek(&mut self, offset: isize) {
            self.pos = self.pos.wrapping_add_signed(offset);
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
        pub fn new(slice: &'a [T]) -> Self {
            Self { base: slice, pos: 0 }
        }

        pub fn with_pos(base: &'a [T], pos: usize) -> Self {
            Self { base, pos }
        }

        pub fn empty() -> Self {
            Self { base: &[], pos: 0 }
        }

        pub fn from_ref(val: &'a T) -> Self {
            Self { base: std::slice::from_ref(val), pos: 0 }
        }

        pub unsafe fn from_raw_parts(ptr: *const T, len: usize) -> Self {
            Self { base: unsafe { std::slice::from_raw_parts(ptr, len) }, pos: 0 }
        }

        pub fn seek(&mut self, offset: isize) {
            self.pos = self.pos.wrapping_add_signed(offset);
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

        pub fn as_slice(&self) -> &[T] {
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

#[cfg(test)]
mod tests {
    use std::{
        fs,
        path::{Path, PathBuf},
    };

    use rustc_ast::{
        AngleBracketedArg, GenericArg, GenericArgs, Ty, TyKind,
        visit::{self, Visitor},
    };
    use rustc_middle::ty::TyCtxt;
    use rustc_span::sym;

    use super::{Config, replace_local_borrows};

    #[derive(Clone, Copy, Debug, Default)]
    struct TypeCensus {
        raw_ptrs: usize,
        option_box_scalars: usize,
        option_boxed_slices: usize,
    }

    impl std::ops::AddAssign for TypeCensus {
        fn add_assign(&mut self, rhs: Self) {
            self.raw_ptrs += rhs.raw_ptrs;
            self.option_box_scalars += rhs.option_box_scalars;
            self.option_boxed_slices += rhs.option_boxed_slices;
        }
    }

    #[derive(Clone, Copy)]
    enum OptionBoxKind {
        Scalar,
        BoxedSlice,
    }

    #[derive(Debug)]
    struct ProjectRewriteRecord {
        project: String,
        raw_ptrs_before: usize,
        raw_ptrs_after: usize,
        option_box_scalars_added: usize,
        option_boxed_slices_added: usize,
    }

    #[derive(Default)]
    struct TypeCensusVisitor {
        census: TypeCensus,
    }

    impl Visitor<'_> for TypeCensusVisitor {
        fn visit_ty(&mut self, ty: &Ty) {
            if matches!(ty.kind, TyKind::Ptr(_)) {
                self.census.raw_ptrs += 1;
            }
            match option_box_kind(ty) {
                Some(OptionBoxKind::Scalar) => self.census.option_box_scalars += 1,
                Some(OptionBoxKind::BoxedSlice) => self.census.option_boxed_slices += 1,
                None => {}
            }
            visit::walk_ty(self, ty);
        }
    }

    fn option_box_kind(ty: &Ty) -> Option<OptionBoxKind> {
        let TyKind::Path(_, option_path) = &ty.kind else {
            return None;
        };
        let option_seg = option_path.segments.last()?;
        if option_seg.ident.name != sym::Option {
            return None;
        }

        let boxed_ty = angle_bracketed_single_type(option_seg.args.as_deref())?;
        let TyKind::Path(_, box_path) = &boxed_ty.kind else {
            return None;
        };
        let box_seg = box_path.segments.last()?;
        if box_seg.ident.name.as_str() != "Box" {
            return None;
        }

        let inner_ty = angle_bracketed_single_type(box_seg.args.as_deref())?;
        if matches!(inner_ty.kind, TyKind::Slice(_)) {
            Some(OptionBoxKind::BoxedSlice)
        } else {
            Some(OptionBoxKind::Scalar)
        }
    }

    fn angle_bracketed_single_type(args: Option<&GenericArgs>) -> Option<&Ty> {
        let GenericArgs::AngleBracketed(args) = args? else {
            return None;
        };
        let [AngleBracketedArg::Arg(GenericArg::Type(ty))] = &args.args[..] else {
            return None;
        };
        Some(ty)
    }

    fn type_census_from_tcx(tcx: TyCtxt<'_>) -> TypeCensus {
        let mut visitor = TypeCensusVisitor::default();
        ::utils::ast::foreach_crate(
            |krate| {
                visitor.visit_crate(&krate);
            },
            tcx,
        );
        visitor.census
    }

    fn b02_root() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../..")
            .join("B02-translated-rust")
    }

    fn b02_project_dirs(root: &Path) -> Vec<PathBuf> {
        let mut projects = Vec::new();
        for category in fs::read_dir(root)
            .unwrap_or_else(|err| panic!("failed to read B02 root `{}`: {err}", root.display()))
        {
            let category = category.unwrap_or_else(|err| {
                panic!("failed to iterate B02 root `{}`: {err}", root.display())
            });
            let category_path = category.path();
            if !category_path.is_dir() {
                continue;
            }

            for project in fs::read_dir(&category_path).unwrap_or_else(|err| {
                panic!(
                    "failed to read B02 category `{}`: {err}",
                    category_path.display()
                )
            }) {
                let project = project.unwrap_or_else(|err| {
                    panic!(
                        "failed to iterate B02 category `{}`: {err}",
                        category_path.display()
                    )
                });
                let project_path = project.path();
                if project_path.is_dir() && project_path.join("Cargo.toml").is_file() {
                    projects.push(project_path);
                }
            }
        }
        projects.sort();
        projects
    }

    #[test]
    #[ignore = "expensive B02 corpus rewrite sweep"]
    fn b02_corpus_rewrite_sweep_records_option_box_rewrites() {
        let root = b02_root();
        assert!(
            root.is_dir(),
            "expected B02 corpus directory at `{}`",
            root.display()
        );

        let projects = b02_project_dirs(&root);
        assert!(
            !projects.is_empty(),
            "expected at least one B02 project under `{}`",
            root.display()
        );

        let mut totals_before = TypeCensus::default();
        let mut totals_after = TypeCensus::default();
        let mut records = Vec::with_capacity(projects.len());

        for project_dir in projects {
            let rel_project = project_dir
                .strip_prefix(&root)
                .unwrap_or(project_dir.as_path())
                .display()
                .to_string();
            let lib_rel = ::utils::find_lib_path(&project_dir).unwrap_or_else(|err| {
                panic!("failed to locate lib path for `{rel_project}`: {err}")
            });
            let lib_path = project_dir.join(&lib_rel);
            let (before, rewritten) =
                ::utils::compilation::run_compiler_on_path(&lib_path, |tcx| {
                    let before = type_census_from_tcx(tcx);
                    let (rewritten, _) = replace_local_borrows(&Config::default(), tcx);
                    (before, rewritten)
                })
                .unwrap_or_else(|_| panic!("failed to rewrite `{}`", lib_path.display()));
            let after = ::utils::compilation::run_compiler_on_str(&rewritten, type_census_from_tcx)
                .unwrap_or_else(|_| panic!("failed to compile rewritten `{}`", lib_path.display()));

            totals_before += before;
            totals_after += after;
            records.push(ProjectRewriteRecord {
                project: rel_project,
                raw_ptrs_before: before.raw_ptrs,
                raw_ptrs_after: after.raw_ptrs,
                option_box_scalars_added: after
                    .option_box_scalars
                    .saturating_sub(before.option_box_scalars),
                option_boxed_slices_added: after
                    .option_boxed_slices
                    .saturating_sub(before.option_boxed_slices),
            });
        }

        let total_scalar_boxes = totals_after
            .option_box_scalars
            .saturating_sub(totals_before.option_box_scalars);
        let total_boxed_slices = totals_after
            .option_boxed_slices
            .saturating_sub(totals_before.option_boxed_slices);

        eprintln!("B02 rewrite census across {} projects:", records.len());
        for record in &records {
            eprintln!(
                "{}: raw_ptrs {} -> {}, +Option<Box<T>>={}, +Option<Box<[T]>>={}",
                record.project,
                record.raw_ptrs_before,
                record.raw_ptrs_after,
                record.option_box_scalars_added,
                record.option_boxed_slices_added,
            );
        }
        eprintln!(
            "Totals: raw_ptrs {} -> {}, +Option<Box<T>>={}, +Option<Box<[T]>>={}",
            totals_before.raw_ptrs, totals_after.raw_ptrs, total_scalar_boxes, total_boxed_slices,
        );

        assert!(
            total_scalar_boxes + total_boxed_slices > 0,
            "expected corpus rewrite sweep to materialize at least one owning box rewrite",
        );
    }
}
