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
    offset_sign_result: OffsetSignResult,
}

#[derive(Debug, Default, Clone, Deserialize)]
pub struct Config {
    pub c_exposed_fns: FxHashSet<String>,
}

pub fn replace_local_borrows(config: &Config, tcx: TyCtxt<'_>) -> (String, bool, bool) {
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

    (code, visitor.bytemuck.get(), slice_cursor_used)
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

    pub struct SliceCursor<'a, T> {
        base: &'a mut [T],
        pos: usize,
    }

    impl<'a, T> SliceCursor<'a, T> {
        pub fn new(base: &'a mut [T]) -> Self {
            Self { base, pos: 0 }
        }

        pub fn with_pos(base: &'a mut [T], pos: usize) -> Self {
            Self { base, pos }
        }

        pub fn empty() -> Self {
            Self { base: &mut [], pos: 0 }
        }

        pub fn from_ref(val: &'a T) -> SliceCursorRef<'a, T> {
            SliceCursorRef::from_ref(val)
        }

        pub fn from_mut(val: &'a mut T) -> Self {
            Self { base: std::slice::from_mut(val), pos: 0 }
        }

        pub fn from_raw_parts(ptr: *const T, len: usize) -> Self {
            Self::from_raw_parts_mut(ptr as *mut T, len)
        }

        pub fn from_raw_parts_mut(ptr: *mut T, len: usize) -> Self {
            Self { base: unsafe { std::slice::from_raw_parts_mut(ptr, len) }, pos: 0 }
        }

        pub fn fork(&mut self) -> SliceCursor<'a, T> {
            let ptr = self.base.as_mut_ptr();
            let len = self.base.len();
            SliceCursor { base: unsafe { std::slice::from_raw_parts_mut(ptr, len) }, pos: self.pos }
        }

        pub fn to_ref_cursor(&self) -> SliceCursorRef<'a, T> {
            let ptr = self.base.as_ptr();
            let len = self.base.len();
            SliceCursorRef {
                base: unsafe { std::slice::from_raw_parts(ptr, len) },
                pos: self.pos,
            }
        }

        pub fn seek(&mut self, offset: isize) {
            self.pos = self.pos.wrapping_add_signed(offset);
        }

        pub fn is_empty(&self) -> bool {
            self.base.is_empty()
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

        pub fn as_slice(&self) -> &'a [T] {
            let ptr = self.base[self.pos..].as_ptr();
            let len = self.base.len() - self.pos;
            unsafe { std::slice::from_raw_parts(ptr, len) }
        }

        pub fn as_slice_mut(&mut self) -> &'a mut [T] {
            let ptr = self.base[self.pos..].as_mut_ptr();
            let len = self.base.len() - self.pos;
            unsafe { std::slice::from_raw_parts_mut(ptr, len) }
        }
    }

    pub struct SliceCursorRef<'a, T> {
        base: &'a [T],
        pos: usize,
    }

    impl<'a, T> SliceCursorRef<'a, T> {
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

        pub fn from_raw_parts(ptr: *const T, len: usize) -> Self {
            Self { base: unsafe { std::slice::from_raw_parts(ptr, len) }, pos: 0 }
        }

        pub fn fork(&self) -> SliceCursorRef<'a, T> {
            SliceCursorRef { base: self.base, pos: self.pos }
        }

        pub fn seek(&mut self, offset: isize) {
            self.pos = self.pos.wrapping_add_signed(offset);
        }

        pub fn is_empty(&self) -> bool {
            self.base.is_empty()
        }

        pub fn as_ptr(&self) -> *const T {
            self.base[self.pos..].as_ptr()
        }

        pub fn first(&self) -> Option<&T> {
            self.base.get(self.pos)
        }

        pub fn as_slice(&self) -> &'a [T] {
            let ptr = self.base[self.pos..].as_ptr();
            let len = self.base.len() - self.pos;
            unsafe { std::slice::from_raw_parts(ptr, len) }
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
                impl<T> IndexMut<$idx_type> for SliceCursor<'_, T> {
                    #[inline]
                    fn index_mut(&mut self, index: $idx_type) -> &mut Self::Output {
                        let i = abs_idx(self.pos, index as isize);
                        &mut self.base[i]
                    }
                }

                impl<T> IndexMut<Range<$idx_type>> for SliceCursor<'_, T> {
                    #[inline]
                    fn index_mut(&mut self, range: Range<$idx_type>) -> &mut Self::Output {
                        let start = abs_idx(self.pos, range.start as isize);
                        let end = abs_idx(self.pos, range.end as isize);
                        &mut self.base[start..end]
                    }
                }

                impl<T> IndexMut<RangeFrom<$idx_type>> for SliceCursor<'_, T> {
                    #[inline]
                    fn index_mut(&mut self, range: RangeFrom<$idx_type>) -> &mut Self::Output {
                        let start = abs_idx(self.pos, range.start as isize);
                        &mut self.base[start..]
                    }
                }

                impl<T> IndexMut<RangeTo<$idx_type>> for SliceCursor<'_, T> {
                    #[inline]
                    fn index_mut(&mut self, range: RangeTo<$idx_type>) -> &mut Self::Output {
                        let end = abs_idx(self.pos, range.end as isize);
                        &mut self.base[self.pos..end]
                    }
                }
            )*

            impl<T> IndexMut<RangeFull> for SliceCursor<'_, T> {
                #[inline]
                fn index_mut(&mut self, _: RangeFull) -> &mut Self::Output {
                    &mut self.base[self.pos..]
                }
            }
        };
    }

    impl_readable_index!(SliceCursor, isize, usize, i32);
    impl_readable_index!(SliceCursorRef, isize, usize, i32);
    impl_mutable_index!(isize, usize, i32);
}"#
}
