use rustc_hash::FxHashMap;
use rustc_hir::ItemKind;
use rustc_index::{Idx, IndexVec, bit_set::ChunkedBitSet};
use rustc_middle::{
    mir::{BasicBlock, Location},
    ty::TyCtxt,
};
use rustc_span::def_id::LocalDefId;
use typed_arena::Arena;
use utils::{compilation, ty_shape};

use super::andersen::{self, AnalysisResult, Loc};

// To inspect the MIR of test cases, you can:

// - Look at the compiled MIR code in the comments of the test case functions.
//
// 1. `AnalysisResult.ends`
//
// Each local variable in an MIR body is assigned one or more indices in the
// analysis, representing its location(s) in the points-to graph.
//
// The indices are assigned in the following order:
//
// - Function arguments
// - Return value
// - Remaining local variables (in the order they are declared, i.e., by name:
//   `_1`, `_2`, ...)
//
// If a local variable has a struct type, each of its fields is assigned a
// separate index.  For example, a struct with three fields will occupy three
// consecutive indices-say, `1`, `2`, and `3`.  The next local variable will
// then start at index `4`.
//
// Each index corresponds to a specific "location", and every location has an
// associated "end": the furthest location that is reachable from it.
//
// - For most locations, the "end" is simply the location itself.
// - However, for struct variables, the index of the first field is treated as
//   representing the entire struct. Its "end" is updated to point to the last
//   field of the struct, marking the span of the entire struct.
//
// The `AnalysisResult.ends` vector record this mapping:
//
// ```
// AnalysisResult.ends[<index of the location>] = <index of the end of that location>
// ```
//
// Example assertion:
//
// ```
// assert_eq!(res.ends, vec![0, 1, 2, 5, 4, 5, 6, 7, 8, 9]);
// ```
//
//
// 2. `AnalysisResult.solutions`
//
// The `AnalysisResult.solutions` vector maps each location index to the set
// of locations it may point to-a conservative union of all points-to targets.
//
// You can write assertions like:
//
// ```
// assert_eq!(sol(&res, <index of the location>), <expected set of indices of locations>);
// ```
//
//
// 3. `AnalysisResult.writes`
//
// `AnalysisResult.writes` records statements that perform memory writes,
// mapping each statement to the set of written locations.
//
// Only locations that are "pointable" (i.e., appear in any `solutions` set,
// directly or via their `ends` range) are included. For example, if `4` is
// a pointable location and `ends[4] = 5`, then `5` is also considered pointable.
//
// Each statement is identified by a `(block, statement_index)` pair:
// - `block`: the index of the basic block
// - `statement_index`: the index of the statement within that basic block
//
// Note: Some statements (e.g., function calls) act as **terminators** in MIR
// and implicitly end the current basic block. As a result, even if
// statement appear sequential in MIR source, they may belong to different
// basic blocks.
//
// ```
// assert_eq!(wg(&w, <basic block index>, <statement index>), <expected set of written location indices>);
// ```
//
// 4. `AnalysisResult.bitfield_writes`
//
// MIR statements that write to bitfields are recorded in the
// `AnalysisResult.bitfield_writes` map, which maps statement locations to the
// set of written bitfield indices.
//
// Bitfields are declared in struct definitions, using the
// `#[bitfield(name=...)]` macro.  Bitfield indices are assigned after the
// regular struct fields, in the order they are declared.
//
// Bitfield writes are easy to notice, as they always use generated setter
// functions.
//
// ```
// assert_eq!(bw(&w, <basic block index>, <statement index>), <expected set of indices of written bitfields>);
// ```

fn analyze_fn_with<F>(types: &str, params: &str, code: &str, f: F)
where F: FnOnce(AnalysisResult, TyCtxt<'_>) + Send {
    let name = "f";
    let code = format!(
        "
        extern crate libc;
        #[macro_use]
        extern crate c2rust_bitfields;
        extern \"C\" {{
            fn malloc(_: libc::c_ulong) -> *mut libc::c_void;
        }}
        {}
        unsafe extern \"C\" fn {}({}) {{
            {}
        }}
    ",
        types, name, params, code
    );
    compilation::run_compiler_on_str(&code, |tcx| {
        let arena = Arena::new();
        let tss = ty_shape::get_ty_shapes(&arena, tcx, true);
        let config = andersen::Config {
            use_optimized_mir: true,
        };
        let pre = andersen::pre_analyze(&config, &tss, tcx);
        let solutions = andersen::analyze(&config, &pre, &tss, tcx);
        let res = andersen::post_analyze(&config, pre, solutions, &tss, tcx);
        f(res, tcx)
    })
    .unwrap();
}

fn analyze_fn<F>(code: &str, f: F)
where F: FnOnce(AnalysisResult, TyCtxt<'_>) + Send {
    analyze_fn_with("", "", code, f);
}

fn find(name: &str, tcx: TyCtxt<'_>) -> LocalDefId {
    tcx.hir_free_items()
        .find_map(|item_id| {
            let item = tcx.hir_item(item_id);
            let (ItemKind::Fn { ident, .. } | ItemKind::Static(_, ident, _, _)) = item.kind else {
                return None;
            };
            if ident.name.as_str() != name {
                return None;
            }
            Some(item_id.owner_id.def_id)
        })
        .unwrap()
}

fn sol(res: &AnalysisResult, i: usize) -> Vec<usize> {
    res.solutions[Loc::from_usize(i)]
        .iter()
        .map(|l| l.index())
        .collect()
}

fn ends_to_vec(ends: &IndexVec<Loc, Loc>) -> Vec<usize> {
    ends.iter().map(|l| l.index()).collect()
}

fn v(i: usize) -> Vec<usize> {
    (0..=i).collect()
}

fn e() -> Vec<usize> {
    Vec::new()
}

#[test]
fn test_eq_ref() {
    // _1 = const 0_i32
    // _3 = &mut _1
    // _2 = &raw mut (*_3)
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = &mut x;
        ",
        |res, _| {
            assert_eq!(ends_to_vec(&res.ends), v(3));
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), vec![1]);
            assert_eq!(sol(&res, 3), vec![1]);
        },
    );
}

#[test]
fn test_eq() {
    // _1 = const 0_i32
    // _2 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _4 = &mut _1
    // _3 = &raw mut (*_4)
    // _2 = _3
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut z: *mut libc::c_int = 0 as *mut libc::c_int;
        let mut y: *mut libc::c_int = &mut x;
        z = y;
        ",
        |res, _| {
            assert_eq!(ends_to_vec(&res.ends), v(4));
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), vec![1]);
            assert_eq!(sol(&res, 3), vec![1]);
            assert_eq!(sol(&res, 4), vec![1]);
        },
    );
}

#[test]
fn test_eq_two() {
    // _1 = const 0_i32
    // _2 = const 0_i32
    // _4 = &mut _1
    // _3 = &raw mut (*_4)
    // _5 = _3
    // _7 = &mut _2
    // _6 = &raw mut (*_7)
    // _3 = move _6
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut z: *mut libc::c_int = &mut x;
        let mut w: *mut libc::c_int = z;
        z = &mut y;
        ",
        |res, _| {
            assert_eq!(ends_to_vec(&res.ends), v(7));
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), e());
            assert_eq!(sol(&res, 3), vec![1, 2]);
            assert_eq!(sol(&res, 4), vec![1]);
            assert_eq!(sol(&res, 5), vec![1, 2]);
            assert_eq!(sol(&res, 6), vec![2]);
            assert_eq!(sol(&res, 7), vec![2]);
        },
    );
}

#[test]
fn test_eq_propagate() {
    // _1 = const 0_i32
    // _2 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _3 = _2
    // _4 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _4 = _3
    // _6 = &mut _1
    // _5 = &raw mut (*_6)
    // _2 = move _5
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = 0 as *mut libc::c_int;
        let mut z: *mut libc::c_int = y;
        let mut w: *mut libc::c_int = 0 as *mut libc::c_int;
        w = z;
        y = &mut x;
        ",
        |res, _| {
            assert_eq!(ends_to_vec(&res.ends), v(6));
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), vec![1]);
            assert_eq!(sol(&res, 3), vec![1]);
            assert_eq!(sol(&res, 4), vec![1]);
            assert_eq!(sol(&res, 5), vec![1]);
            assert_eq!(sol(&res, 6), vec![1]);
        },
    );
}

#[test]
fn test_eq_deref() {
    // _1 = const 0_i32
    // _3 = &mut _1
    // _2 = &raw mut (*_3)
    // _5 = &mut _2
    // _4 = &raw mut (*_5)
    // _6 = (*_4)
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = &mut x;
        let mut z: *mut *mut libc::c_int = &mut y;
        let mut w: *mut libc::c_int = *z;
        ",
        |res, _| {
            assert_eq!(ends_to_vec(&res.ends), v(6));
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), vec![1]);
            assert_eq!(sol(&res, 3), vec![1]);
            assert_eq!(sol(&res, 4), vec![2]);
            assert_eq!(sol(&res, 5), vec![2]);
            assert_eq!(sol(&res, 6), vec![1]);
        },
    );
}

#[test]
fn test_eq_deref_subset() {
    // _1 = const 0_i32
    // _2 = const 0_i32
    // _4 = &mut _1
    // _3 = &raw mut (*_4)
    // _6 = &mut _3
    // _5 = &raw mut (*_6)
    // _8 = &mut _2
    // _7 = &raw mut (*_8)
    // _9 = (*_5)
    // _7 = move _9
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut z: *mut libc::c_int = &mut x;
        let mut w: *mut *mut libc::c_int = &mut z;
        let mut v: *mut libc::c_int = &mut y;
        v = *w;
        ",
        |res, _| {
            assert_eq!(ends_to_vec(&res.ends), v(9));
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), e());
            assert_eq!(sol(&res, 3), vec![1]);
            assert_eq!(sol(&res, 4), vec![1]);
            assert_eq!(sol(&res, 5), vec![3]);
            assert_eq!(sol(&res, 6), vec![3]);
            assert_eq!(sol(&res, 7), vec![1, 2]);
            assert_eq!(sol(&res, 8), vec![2]);
            assert_eq!(sol(&res, 9), vec![1]);
        },
    );
}

#[test]
fn test_eq_deref_propagate() {
    // _1 = const 0_i32
    // _3 = &mut _1
    // _2 = &raw mut (*_3)
    // _5 = &mut _2
    // _4 = &raw mut (*_5)
    // _6 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _7 = _6
    // _8 = (*_4)
    // _6 = move _8
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = &mut x;
        let mut z: *mut *mut libc::c_int = &mut y;
        let mut w: *mut libc::c_int = 0 as *mut libc::c_int;
        let mut v: *mut libc::c_int = w;
        w = *z;
        ",
        |res, _| {
            assert_eq!(ends_to_vec(&res.ends), v(8));
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), vec![1]);
            assert_eq!(sol(&res, 3), vec![1]);
            assert_eq!(sol(&res, 4), vec![2]);
            assert_eq!(sol(&res, 5), vec![2]);
            assert_eq!(sol(&res, 6), vec![1]);
            assert_eq!(sol(&res, 7), vec![1]);
            assert_eq!(sol(&res, 8), vec![1]);
        },
    );
}

#[test]
fn test_deref_eq() {
    // _1 = const 0_i32
    // _2 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _4 = &mut _2
    // _3 = &raw mut (*_4)
    // _6 = &mut _1
    // _5 = &raw mut (*_6)
    // (*_3) = move _5
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = 0 as *mut libc::c_int;
        let mut z: *mut *mut libc::c_int = &mut y;
        *z = &mut x;
        ",
        |res, _| {
            assert_eq!(ends_to_vec(&res.ends), v(6));
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), vec![1]);
            assert_eq!(sol(&res, 3), vec![2]);
            assert_eq!(sol(&res, 4), vec![2]);
            assert_eq!(sol(&res, 5), vec![1]);
            assert_eq!(sol(&res, 6), vec![1]);
        },
    );
}

#[test]
fn test_deref_eq_subset() {
    // _1 = const 0_i32
    // _2 = const 0_i32
    // _4 = &mut _1
    // _3 = &raw mut (*_4)
    // _6 = &mut _3
    // _5 = &raw mut (*_6)
    // _8 = &mut _2
    // _7 = &raw mut (*_8)
    // (*_5) = move _7
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut z: *mut libc::c_int = &mut x;
        let mut w: *mut *mut libc::c_int = &mut z;
        *w = &mut y;
        ",
        |res, _| {
            assert_eq!(ends_to_vec(&res.ends), v(8));
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), e());
            assert_eq!(sol(&res, 3), vec![1, 2]);
            assert_eq!(sol(&res, 4), vec![1]);
            assert_eq!(sol(&res, 5), vec![3]);
            assert_eq!(sol(&res, 6), vec![3]);
            assert_eq!(sol(&res, 7), vec![2]);
            assert_eq!(sol(&res, 8), vec![2]);
        },
    );
}

#[test]
fn test_deref_eq_propagate() {
    // _1 = const 0_i32
    // _2 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _4 = &mut _2
    // _3 = &raw mut (*_4)
    // _5 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _6 = _2
    // _5 = move _6
    // _8 = &mut _1
    // _7 = &raw mut (*_8)
    // (*_3) = move _7
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = 0 as *mut libc::c_int;
        let mut z: *mut *mut libc::c_int = &mut y;
        let mut w: *mut libc::c_int = 0 as *mut libc::c_int;
        w = y;
        *z = &mut x;
        ",
        |res, _| {
            assert_eq!(ends_to_vec(&res.ends), v(8));
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), vec![1]);
            assert_eq!(sol(&res, 3), vec![2]);
            assert_eq!(sol(&res, 4), vec![2]);
            assert_eq!(sol(&res, 5), vec![1]);
            assert_eq!(sol(&res, 6), vec![1]);
            assert_eq!(sol(&res, 7), vec![1]);
            assert_eq!(sol(&res, 8), vec![1]);
        },
    );
}

#[test]
fn test_array_aggregate() {
    // _1 = const 0_i32
    // _2 = const 0_i32
    // _5 = &mut _1
    // _4 = &raw mut (*_5)
    // _7 = &mut _2
    // _6 = &raw mut (*_7)
    // _3 = [move _4, move _6]
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut p: [*mut libc::c_int; 2] = [&mut x, &mut y];
        ",
        |res, _| {
            assert_eq!(ends_to_vec(&res.ends), v(7));
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), e());
            assert_eq!(sol(&res, 3), vec![1, 2]);
            assert_eq!(sol(&res, 4), vec![1]);
            assert_eq!(sol(&res, 5), vec![1]);
            assert_eq!(sol(&res, 6), vec![2]);
            assert_eq!(sol(&res, 7), vec![2]);
        },
    );
}

#[test]
fn test_array_eq_ref() {
    // _2 = const 0_usize as *mut i32 (PointerWithExposedProvenance)
    // _1 = [move _2; 2]
    // _3 = const 0_i32
    // _4 = const 0_i32
    // _6 = &mut _3
    // _5 = &raw mut (*_6)
    // _7 = const 0_i32 as usize (IntToInt)
    // _8 = Lt(copy _7, const 2_usize)
    // _1[_7] = move _5
    // _10 = &mut _4
    // _9 = &raw mut (*_10)
    // _11 = const 1_i32 as usize (IntToInt)
    // _12 = Lt(copy _11, const 2_usize)
    // _1[_11] = move _9
    analyze_fn(
        "
        let mut p: [*mut libc::c_int; 2] = [0 as *mut libc::c_int; 2];
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: libc::c_int = 0 as libc::c_int;
        p[0 as libc::c_int as usize] = &mut x;
        p[1 as libc::c_int as usize] = &mut y;
        ",
        |res, _| {
            assert_eq!(ends_to_vec(&res.ends), v(12));
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), vec![3, 4]);
            assert_eq!(sol(&res, 2), e());
            assert_eq!(sol(&res, 3), e());
            assert_eq!(sol(&res, 4), e());
            assert_eq!(sol(&res, 5), vec![3]);
            assert_eq!(sol(&res, 6), vec![3]);
            assert_eq!(sol(&res, 7), e());
            assert_eq!(sol(&res, 8), e());
            assert_eq!(sol(&res, 9), vec![4]);
            assert_eq!(sol(&res, 10), vec![4]);
            assert_eq!(sol(&res, 11), e());
            assert_eq!(sol(&res, 12), e());
        },
    );
}

#[test]
fn test_struct_aggregate() {
    // _1 = const 0_i32
    // _2 = const 0_i32
    // _5 = &mut _1
    // _4 = &raw mut (*_5)
    // _7 = &mut _2
    // _6 = &raw mut (*_7)
    // _3 = s { x: move _4, y: move _6, z: const 0_i32 }
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: *mut libc::c_int,
            pub y: *mut libc::c_int,
            pub z: libc::c_int,
        }
        ",
        "",
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut z: s = {
            let mut init = s {
                x: &mut x,
                y: &mut y,
                z: 0 as libc::c_int,
            };
            init
        };
        ",
        |res, _| {
            assert_eq!(ends_to_vec(&res.ends), vec![0, 1, 2, 5, 4, 5, 6, 7, 8, 9]);
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), e());
            assert_eq!(sol(&res, 3), vec![1]);
            assert_eq!(sol(&res, 4), vec![2]);
            assert_eq!(sol(&res, 5), e());
            assert_eq!(sol(&res, 6), vec![1]);
            assert_eq!(sol(&res, 7), vec![1]);
            assert_eq!(sol(&res, 8), vec![2]);
            assert_eq!(sol(&res, 9), vec![2]);
        },
    );
}

#[test]
fn test_struct_eq_ref() {
    // _1 = const 0_i32
    // _2 = const 0_i32
    // _3 = const 0_i32
    // _4 = const 0_i32
    // _6 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _7 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _5 = t { x: move _6, y: move _7 }
    // _9 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _10 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _8 = t { x: move _9, y: move _10 }
    // _13 = &mut _1
    // _12 = &raw mut (*_13)
    // _15 = &mut _2
    // _14 = &raw mut (*_15)
    // _11 = t { x: move _12, y: move _14 }
    // _18 = &mut _3
    // _17 = &raw mut (*_18)
    // _20 = &mut _4
    // _19 = &raw mut (*_20)
    // _16 = t { x: move _17, y: move _19 }
    // _5 = _11
    // _8 = _16
    // _23 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _24 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _22 = t { x: move _23, y: move _24 }
    // _26 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _27 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _25 = t { x: move _26, y: move _27 }
    // _21 = s { x: move _22, y: move _25 }
    // _28 = s { x: _11, y: _16 }
    // _21 = _28
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct t {
            pub x: *mut libc::c_int,
            pub y: *mut libc::c_int,
        }
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: t,
            pub y: t,
        }
        ",
        "",
        "
        let mut x0: libc::c_int = 0 as libc::c_int;
        let mut x1: libc::c_int = 0 as libc::c_int;
        let mut x2: libc::c_int = 0 as libc::c_int;
        let mut x3: libc::c_int = 0 as libc::c_int;
        let mut t0: t = t {
            x: 0 as *mut libc::c_int,
            y: 0 as *mut libc::c_int,
        };
        let mut t1: t = t {
            x: 0 as *mut libc::c_int,
            y: 0 as *mut libc::c_int,
        };
        let mut t2: t = {
            let mut init = t { x: &mut x0, y: &mut x1 };
            init
        };
        let mut t3: t = {
            let mut init = t { x: &mut x2, y: &mut x3 };
            init
        };
        t0 = t2;
        t1 = t3;
        let mut s0: s = s {
            x: t {
                x: 0 as *mut libc::c_int,
                y: 0 as *mut libc::c_int,
            },
            y: t {
                x: 0 as *mut libc::c_int,
                y: 0 as *mut libc::c_int,
            },
        };
        let mut s1: s = {
            let mut init = s { x: t2, y: t3 };
            init
        };
        s0 = s1;
        ",
        |res, _| {
            assert_eq!(
                ends_to_vec(&res.ends),
                vec![
                    0, 1, 2, 3, 4, 6, 6, 7, 8, 10, 10, 11, 12, 14, 14, 15, 16, 17, 18, 20, 20, 21,
                    22, 23, 24, 28, 26, 28, 28, 30, 30, 31, 32, 34, 34, 35, 36, 40, 38, 40, 40
                ]
            );
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), e());
            assert_eq!(sol(&res, 3), e());
            assert_eq!(sol(&res, 4), e());
            assert_eq!(sol(&res, 5), vec![1]);
            assert_eq!(sol(&res, 6), vec![2]);
            assert_eq!(sol(&res, 7), e());
            assert_eq!(sol(&res, 8), e());
            assert_eq!(sol(&res, 9), vec![3]);
            assert_eq!(sol(&res, 10), vec![4]);
            assert_eq!(sol(&res, 11), e());
            assert_eq!(sol(&res, 12), e());
            assert_eq!(sol(&res, 13), vec![1]);
            assert_eq!(sol(&res, 14), vec![2]);
            assert_eq!(sol(&res, 15), vec![1]);
            assert_eq!(sol(&res, 16), vec![1]);
            assert_eq!(sol(&res, 17), vec![2]);
            assert_eq!(sol(&res, 18), vec![2]);
            assert_eq!(sol(&res, 19), vec![3]);
            assert_eq!(sol(&res, 20), vec![4]);
            assert_eq!(sol(&res, 21), vec![3]);
            assert_eq!(sol(&res, 22), vec![3]);
            assert_eq!(sol(&res, 23), vec![4]);
            assert_eq!(sol(&res, 24), vec![4]);
            assert_eq!(sol(&res, 25), vec![1]);
            assert_eq!(sol(&res, 26), vec![2]);
            assert_eq!(sol(&res, 27), vec![3]);
            assert_eq!(sol(&res, 28), vec![4]);
            assert_eq!(sol(&res, 29), e());
            assert_eq!(sol(&res, 30), e());
            assert_eq!(sol(&res, 31), e());
            assert_eq!(sol(&res, 32), e());
            assert_eq!(sol(&res, 33), e());
            assert_eq!(sol(&res, 34), e());
            assert_eq!(sol(&res, 35), e());
            assert_eq!(sol(&res, 36), e());
            assert_eq!(sol(&res, 37), vec![1]);
            assert_eq!(sol(&res, 38), vec![2]);
            assert_eq!(sol(&res, 39), vec![3]);
            assert_eq!(sol(&res, 40), vec![4]);
        },
    );
}

#[test]
fn test_struct_deref_eq() {
    // _1 = const 0_i32
    // _2 = const 0_i32
    // _3 = const 0_i32
    // _4 = const 0_i32
    // _7 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _8 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _6 = t { x: move _7, y: move _8 }
    // _10 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _11 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _9 = t { x: move _10, y: move _11 }
    // _5 = s { x: move _6, y: move _9 }
    // _13 = &mut _5
    // _12 = &raw mut (*_13)
    // _15 = &mut _1
    // _14 = &raw mut (*_15)
    // (((*_12).0: t).0: *mut i32) = move _14
    // _17 = &mut _2
    // _16 = &raw mut (*_17)
    // (((*_12).0: t).1: *mut i32) = move _16
    // _19 = &mut _3
    // _18 = &raw mut (*_19)
    // (((*_12).1: t).0: *mut i32) = move _18
    // _21 = &mut _4
    // _20 = &raw mut (*_21)
    // (((*_12).1: t).1: *mut i32) = move _20
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct t {
            pub x: *mut libc::c_int,
            pub y: *mut libc::c_int,
        }
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: t,
            pub y: t,
        }
        ",
        "",
        "
        let mut x0: libc::c_int = 0 as libc::c_int;
        let mut x1: libc::c_int = 0 as libc::c_int;
        let mut x2: libc::c_int = 0 as libc::c_int;
        let mut x3: libc::c_int = 0 as libc::c_int;
        let mut z: s = s {
            x: t {
                x: 0 as *mut libc::c_int,
                y: 0 as *mut libc::c_int,
            },
            y: t {
                x: 0 as *mut libc::c_int,
                y: 0 as *mut libc::c_int,
            },
        };
        let mut w: *mut s = &mut z;
        (*w).x.x = &mut x0;
        (*w).x.y = &mut x1;
        (*w).y.x = &mut x2;
        (*w).y.y = &mut x3;
        ",
        |res, _| {
            assert_eq!(
                ends_to_vec(&res.ends),
                vec![
                    0, 1, 2, 3, 4, 8, 6, 8, 8, 10, 10, 11, 12, 14, 14, 15, 16, 17, 18, 19, 20, 21,
                    22, 23, 24, 25, 26
                ]
            );
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), e());
            assert_eq!(sol(&res, 3), e());
            assert_eq!(sol(&res, 4), e());
            assert_eq!(sol(&res, 5), vec![1]);
            assert_eq!(sol(&res, 6), vec![2]);
            assert_eq!(sol(&res, 7), vec![3]);
            assert_eq!(sol(&res, 8), vec![4]);
            assert_eq!(sol(&res, 9), e());
            assert_eq!(sol(&res, 10), e());
            assert_eq!(sol(&res, 11), e());
            assert_eq!(sol(&res, 12), e());
            assert_eq!(sol(&res, 13), e());
            assert_eq!(sol(&res, 14), e());
            assert_eq!(sol(&res, 15), e());
            assert_eq!(sol(&res, 16), e());
            assert_eq!(sol(&res, 17), vec![5]);
            assert_eq!(sol(&res, 18), vec![5]);
            assert_eq!(sol(&res, 19), vec![1]);
            assert_eq!(sol(&res, 20), vec![1]);
            assert_eq!(sol(&res, 21), vec![2]);
            assert_eq!(sol(&res, 22), vec![2]);
            assert_eq!(sol(&res, 23), vec![3]);
            assert_eq!(sol(&res, 24), vec![3]);
            assert_eq!(sol(&res, 25), vec![4]);
            assert_eq!(sol(&res, 26), vec![4]);
        },
    );
}

#[test]
fn test_struct_eq_deref() {
    // _1 = const 0_i32
    // _2 = const 0_i32
    // _3 = const 0_i32
    // _4 = const 0_i32
    // _9 = &mut _1
    // _8 = &raw mut (*_9)
    // _11 = &mut _2
    // _10 = &raw mut (*_11)
    // _7 = t { x: move _8, y: move _10 }
    // _14 = &mut _3
    // _13 = &raw mut (*_14)
    // _16 = &mut _4
    // _15 = &raw mut (*_16)
    // _12 = t { x: move _13, y: move _15 }
    // _6 = s { x: _7, y: _12 }
    // _5 = _6
    // _18 = &mut _5
    // _17 = &raw mut (*_18)
    // _19 = (((*_17).0: t).0: *mut i32)
    // _20 = (((*_17).0: t).1: *mut i32)
    // _21 = (((*_17).1: t).0: *mut i32)
    // _22 = (((*_17).1: t).1: *mut i32)
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct t {
            pub x: *mut libc::c_int,
            pub y: *mut libc::c_int,
        }
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: t,
            pub y: t,
        }
        ",
        "",
        "
        let mut x0: libc::c_int = 0 as libc::c_int;
        let mut x1: libc::c_int = 0 as libc::c_int;
        let mut x2: libc::c_int = 0 as libc::c_int;
        let mut x3: libc::c_int = 0 as libc::c_int;
        let mut z: s = {
            let mut init = s {
                x: {
                    let mut init = t { x: &mut x0, y: &mut x1 };
                    init
                },
                y: {
                    let mut init = t { x: &mut x2, y: &mut x3 };
                    init
                },
            };
            init
        };
        let mut w: *mut s = &mut z;
        let mut y0: *mut libc::c_int = (*w).x.x;
        let mut y1: *mut libc::c_int = (*w).x.y;
        let mut y2: *mut libc::c_int = (*w).y.x;
        let mut y3: *mut libc::c_int = (*w).y.y;
        ",
        |res, _| {
            assert_eq!(
                ends_to_vec(&res.ends),
                vec![
                    0, 1, 2, 3, 4, 8, 6, 8, 8, 12, 10, 12, 12, 14, 14, 15, 16, 17, 18, 20, 20, 21,
                    22, 23, 24, 25, 26, 27, 28, 29, 30
                ]
            );
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), e());
            assert_eq!(sol(&res, 3), e());
            assert_eq!(sol(&res, 4), e());
            assert_eq!(sol(&res, 5), vec![1]);
            assert_eq!(sol(&res, 6), vec![2]);
            assert_eq!(sol(&res, 7), vec![3]);
            assert_eq!(sol(&res, 8), vec![4]);
            assert_eq!(sol(&res, 9), vec![1]);
            assert_eq!(sol(&res, 10), vec![2]);
            assert_eq!(sol(&res, 11), vec![3]);
            assert_eq!(sol(&res, 12), vec![4]);
            assert_eq!(sol(&res, 13), vec![1]);
            assert_eq!(sol(&res, 14), vec![2]);
            assert_eq!(sol(&res, 15), vec![1]);
            assert_eq!(sol(&res, 16), vec![1]);
            assert_eq!(sol(&res, 17), vec![2]);
            assert_eq!(sol(&res, 18), vec![2]);
            assert_eq!(sol(&res, 19), vec![3]);
            assert_eq!(sol(&res, 20), vec![4]);
            assert_eq!(sol(&res, 21), vec![3]);
            assert_eq!(sol(&res, 22), vec![3]);
            assert_eq!(sol(&res, 23), vec![4]);
            assert_eq!(sol(&res, 24), vec![4]);
            assert_eq!(sol(&res, 25), vec![5]);
            assert_eq!(sol(&res, 26), vec![5]);
            assert_eq!(sol(&res, 27), vec![1]);
            assert_eq!(sol(&res, 28), vec![2]);
            assert_eq!(sol(&res, 29), vec![3]);
            assert_eq!(sol(&res, 30), vec![4]);
        },
    );
}

#[test]
fn test_struct_field_ref() {
    // _3 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _4 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _2 = t { x: move _3, y: move _4 }
    // _6 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _7 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _5 = t { x: move _6, y: move _7 }
    // _1 = s { x: move _2, y: move _5 }
    // _9 = &mut ((_1.0: t).0: *mut i32)
    // _8 = &raw mut (*_9)
    // _11 = &mut ((_1.0: t).1: *mut i32)
    // _10 = &raw mut (*_11)
    // _13 = &mut ((_1.1: t).0: *mut i32)
    // _12 = &raw mut (*_13)
    // _15 = &mut ((_1.1: t).1: *mut i32)
    // _14 = &raw mut (*_15)
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct t {
            pub x: *mut libc::c_int,
            pub y: *mut libc::c_int,
        }
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: t,
            pub y: t,
        }
        ",
        "",
        "
        let mut s: s = s {
            x: t {
                x: 0 as *mut libc::c_int,
                y: 0 as *mut libc::c_int,
            },
            y: t {
                x: 0 as *mut libc::c_int,
                y: 0 as *mut libc::c_int,
            },
        };
        let mut x0: *mut *mut libc::c_int = &mut s.x.x;
        let mut x1: *mut *mut libc::c_int = &mut s.x.y;
        let mut x2: *mut *mut libc::c_int = &mut s.y.x;
        let mut x3: *mut *mut libc::c_int = &mut s.y.y;
        ",
        |res, _| {
            assert_eq!(
                ends_to_vec(&res.ends),
                vec![
                    0, 4, 2, 4, 4, 6, 6, 7, 8, 10, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20
                ]
            );
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), e());
            assert_eq!(sol(&res, 3), e());
            assert_eq!(sol(&res, 4), e());
            assert_eq!(sol(&res, 5), e());
            assert_eq!(sol(&res, 6), e());
            assert_eq!(sol(&res, 7), e());
            assert_eq!(sol(&res, 8), e());
            assert_eq!(sol(&res, 9), e());
            assert_eq!(sol(&res, 10), e());
            assert_eq!(sol(&res, 11), e());
            assert_eq!(sol(&res, 12), e());
            assert_eq!(sol(&res, 13), vec![1]);
            assert_eq!(sol(&res, 14), vec![1]);
            assert_eq!(sol(&res, 15), vec![2]);
            assert_eq!(sol(&res, 16), vec![2]);
            assert_eq!(sol(&res, 17), vec![3]);
            assert_eq!(sol(&res, 18), vec![3]);
            assert_eq!(sol(&res, 19), vec![4]);
            assert_eq!(sol(&res, 20), vec![4]);
        },
    );
}

#[test]
fn test_struct_field_deref_ref() {
    // _3 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _4 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _2 = t { x: move _3, y: move _4 }
    // _6 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _7 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _5 = t { x: move _6, y: move _7 }
    // _1 = s { x: move _2, y: move _5 }
    // _9 = &mut (_1.0: t)
    // _8 = &raw mut (*_9)
    // _11 = &mut (_1.1: t)
    // _10 = &raw mut (*_11)
    // _13 = &mut ((*_8).0: *mut i32)
    // _12 = &raw mut (*_13)
    // _15 = &mut ((*_8).1: *mut i32)
    // _14 = &raw mut (*_15)
    // _17 = &mut ((*_10).0: *mut i32)
    // _16 = &raw mut (*_17)
    // _19 = &mut ((*_10).1: *mut i32)
    // _18 = &raw mut (*_19)
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct t {
            pub x: *mut libc::c_int,
            pub y: *mut libc::c_int,
        }
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: t,
            pub y: t,
        }
        ",
        "",
        "
        let mut s: s = s {
            x: t {
                x: 0 as *mut libc::c_int,
                y: 0 as *mut libc::c_int,
            },
            y: t {
                x: 0 as *mut libc::c_int,
                y: 0 as *mut libc::c_int,
            },
        };
        let mut t0: *mut t = &mut s.x;
        let mut t1: *mut t = &mut s.y;
        let mut x0: *mut *mut libc::c_int = &mut (*t0).x;
        let mut x1: *mut *mut libc::c_int = &mut (*t0).y;
        let mut x2: *mut *mut libc::c_int = &mut (*t1).x;
        let mut x3: *mut *mut libc::c_int = &mut (*t1).y;
        ",
        |res, _| {
            assert_eq!(
                ends_to_vec(&res.ends),
                vec![
                    0, 4, 2, 4, 4, 6, 6, 7, 8, 10, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21,
                    22, 23, 24
                ]
            );
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), e());
            assert_eq!(sol(&res, 3), e());
            assert_eq!(sol(&res, 4), e());
            assert_eq!(sol(&res, 5), e());
            assert_eq!(sol(&res, 6), e());
            assert_eq!(sol(&res, 7), e());
            assert_eq!(sol(&res, 8), e());
            assert_eq!(sol(&res, 9), e());
            assert_eq!(sol(&res, 10), e());
            assert_eq!(sol(&res, 11), e());
            assert_eq!(sol(&res, 12), e());
            assert_eq!(sol(&res, 13), vec![1]);
            assert_eq!(sol(&res, 14), vec![1]);
            assert_eq!(sol(&res, 15), vec![3]);
            assert_eq!(sol(&res, 16), vec![3]);
            assert_eq!(sol(&res, 17), vec![1]);
            assert_eq!(sol(&res, 18), vec![1]);
            assert_eq!(sol(&res, 19), vec![2]);
            assert_eq!(sol(&res, 20), vec![2]);
            assert_eq!(sol(&res, 21), vec![3]);
            assert_eq!(sol(&res, 22), vec![3]);
            assert_eq!(sol(&res, 23), vec![4]);
            assert_eq!(sol(&res, 24), vec![4]);
        },
    );
}

#[test]
fn test_struct_deref_eq_ends() {
    // _1 = const 0_i32
    // _2 = const 0_i32
    // _3 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _4 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _7 = &mut _3
    // _6 = &raw mut (*_7)
    // _5 = move _6 as *mut s (PtrToPtr)
    // _9 = &mut _1
    // _8 = &raw mut (*_9)
    // ((*_5).0: *mut i32) = move _8
    // _11 = &mut _2
    // _10 = &raw mut (*_11)
    // ((*_5).1: *mut i32) = move _10
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: *mut libc::c_int,
            pub y: *mut libc::c_int,
        }
        ",
        "",
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut z: *mut libc::c_int = 0 as *mut libc::c_int;
        let mut w: *mut libc::c_int = 0 as *mut libc::c_int;
        let mut v: *mut s = &mut z as *mut *mut libc::c_int as *mut s;
        (*v).x = &mut x;
        (*v).y = &mut y;
        ",
        |res, _| {
            assert_eq!(ends_to_vec(&res.ends), v(11));
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), e());
            assert_eq!(sol(&res, 3), vec![1]);
            assert_eq!(sol(&res, 4), e());
            assert_eq!(sol(&res, 5), vec![3]);
            assert_eq!(sol(&res, 6), vec![3]);
            assert_eq!(sol(&res, 7), vec![3]);
            assert_eq!(sol(&res, 8), vec![1]);
            assert_eq!(sol(&res, 9), vec![1]);
            assert_eq!(sol(&res, 10), vec![2]);
            assert_eq!(sol(&res, 11), vec![2]);
        },
    );
}

#[test]
fn test_struct_eq_deref_ends() {
    // _1 = const 0_i32
    // _2 = const 0_i32
    // _4 = &mut _1
    // _3 = &raw mut (*_4)
    // _6 = &mut _2
    // _5 = &raw mut (*_6)
    // _9 = &mut _3
    // _8 = &raw mut (*_9)
    // _7 = move _8 as *mut s (PtrToPtr)
    // _10 = ((*_7).0: *mut i32)
    // _11 = ((*_7).1: *mut i32)
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: *mut libc::c_int,
            pub y: *mut libc::c_int,
        }
        ",
        "",
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut z: *mut libc::c_int = &mut x;
        let mut w: *mut libc::c_int = &mut y;
        let mut v: *mut s = &mut z as *mut *mut libc::c_int as *mut s;
        let mut u: *mut libc::c_int = (*v).x;
        let mut t: *mut libc::c_int = (*v).y;
        ",
        |res, _| {
            assert_eq!(ends_to_vec(&res.ends), v(11));
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), e());
            assert_eq!(sol(&res, 3), vec![1]);
            assert_eq!(sol(&res, 4), vec![1]);
            assert_eq!(sol(&res, 5), vec![2]);
            assert_eq!(sol(&res, 6), vec![2]);
            assert_eq!(sol(&res, 7), vec![3]);
            assert_eq!(sol(&res, 8), vec![3]);
            assert_eq!(sol(&res, 9), vec![3]);
            assert_eq!(sol(&res, 10), vec![1]);
            assert_eq!(sol(&res, 11), e());
        },
    );
}

#[test]
fn test_struct_ref_deref_ends() {
    // _1 = const 0_i32
    // _4 = &mut _1
    // _3 = &raw mut (*_4)
    // _2 = move _3 as *mut s (PtrToPtr)
    // _6 = &mut ((*_2).0: *mut i32)
    // _5 = &raw mut (*_6)
    // _8 = &mut ((*_2).1: *mut i32)
    // _7 = &raw mut (*_8)
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: *mut libc::c_int,
            pub y: *mut libc::c_int,
        }
        ",
        "",
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut s = &mut x as *mut libc::c_int as *mut s;
        let mut z: *mut *mut libc::c_int = &mut (*y).x;
        let mut w: *mut *mut libc::c_int = &mut (*y).y;
        ",
        |res, _| {
            assert_eq!(ends_to_vec(&res.ends), v(8));
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), vec![1]);
            assert_eq!(sol(&res, 3), vec![1]);
            assert_eq!(sol(&res, 4), vec![1]);
            assert_eq!(sol(&res, 5), vec![1]);
            assert_eq!(sol(&res, 6), vec![1]);
            assert_eq!(sol(&res, 7), e());
            assert_eq!(sol(&res, 8), e());
        },
    );
}

#[test]
fn test_union_aggregate() {
    // _1 = const 0_i32
    // _4 = &mut _1
    // _3 = &raw mut (*_4)
    // _2 = u { x: move _3 }
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub union u {
            pub x: *mut libc::c_int,
            pub y: *mut libc::c_int,
        }
        ",
        "",
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: u = u { y: &mut x };
        ",
        |res, _| {
            assert_eq!(ends_to_vec(&res.ends), vec![0, 1, 3, 3, 4, 5]);
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), e());
            assert_eq!(sol(&res, 3), vec![1]);
            assert_eq!(sol(&res, 4), vec![1]);
            assert_eq!(sol(&res, 5), vec![1]);
        },
    );
}

#[test]
fn test_copy_for_deref() {
    // _1 = const 0_i32
    // _2 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _4 = &mut _2
    // _3 = &raw mut (*_4)
    // _6 = &mut _3
    // _5 = &raw mut (*_6)
    // _8 = &mut _1
    // _7 = &raw mut (*_8)
    // _9 = deref_copy (*_5)
    // (*_9) = move _7
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
        }
        ",
        "",
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = 0 as *mut libc::c_int;
        let mut z: *mut *mut libc::c_int = &mut y;
        let mut w: *mut *mut *mut libc::c_int = &mut z;
        **w = &mut x;
        ",
        |res, _| {
            assert_eq!(ends_to_vec(&res.ends), v(9));
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), vec![1]);
            assert_eq!(sol(&res, 3), vec![2]);
            assert_eq!(sol(&res, 4), vec![2]);
            assert_eq!(sol(&res, 5), vec![3]);
            assert_eq!(sol(&res, 6), vec![3]);
            assert_eq!(sol(&res, 7), vec![1]);
            assert_eq!(sol(&res, 8), vec![1]);
            assert_eq!(sol(&res, 9), vec![2]);
        },
    );
}

#[test]
fn test_static() {
    // _3 = const {alloc1: *mut i32}
    // _2 = &mut (*_3)
    // _1 = &raw mut (*_2)
    analyze_fn_with(
        "
        pub static mut x: libc::c_int = 0;
        ",
        "",
        "
        let mut y: *mut libc::c_int = &mut x;
        ",
        |res, _| {
            assert_eq!(ends_to_vec(&res.ends), v(4));
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), vec![0]);
            assert_eq!(sol(&res, 3), vec![0]);
            assert_eq!(sol(&res, 4), vec![0]);
        },
    );
}

#[test]
fn test_static_struct_field_eq() {
    // _2 = const 0_usize as *const i32 (PointerFromExposedAddress)
    // _1 = move _2 as *mut i32 (PtrToPtr)
    // _4 = const 0_usize as *const i32 (PointerFromExposedAddress)
    // _3 = move _4 as *mut i32 (PtrToPtr)
    // _0 = s { x: move _1, y: move _3 }
    //
    // _1 = const 0_i32
    // _2 = const 0_i32
    // _4 = &mut _1
    // _3 = &raw mut (*_4)
    // _5 = const {alloc1: *mut s}
    // ((*_5).0: *mut i32) = move _3
    // _7 = &mut _2
    // _6 = &raw mut (*_7)
    // _8 = const {alloc1: *mut s}
    // ((*_8).1: *mut i32) = move _6
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: *mut libc::c_int,
            pub y: *mut libc::c_int,
        }
        pub static mut z: s = s {
            x: 0 as *const libc::c_int as *mut libc::c_int,
            y: 0 as *const libc::c_int as *mut libc::c_int,
        };
        ",
        "",
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: libc::c_int = 0 as libc::c_int;
        z.x = &mut x;
        z.y = &mut y;
        ",
        |res, _| {
            assert_eq!(
                ends_to_vec(&res.ends),
                vec![1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
            );
            assert_eq!(sol(&res, 0), vec![7]);
            assert_eq!(sol(&res, 1), vec![8]);
            assert_eq!(sol(&res, 2), e());
            assert_eq!(sol(&res, 3), e());
            assert_eq!(sol(&res, 4), e());
            assert_eq!(sol(&res, 5), e());
            assert_eq!(sol(&res, 6), e());
            assert_eq!(sol(&res, 7), e());
            assert_eq!(sol(&res, 8), e());
            assert_eq!(sol(&res, 9), vec![7]);
            assert_eq!(sol(&res, 10), vec![7]);
            assert_eq!(sol(&res, 11), vec![0]);
            assert_eq!(sol(&res, 12), vec![8]);
            assert_eq!(sol(&res, 13), vec![8]);
            assert_eq!(sol(&res, 14), vec![0]);
        },
    );
}

#[test]
fn test_static_struct_field_ref() {
    // _0 = s { x: const 0_i32, y: const 0_i32 }
    //
    // _3 = const {alloc1: *mut s}
    // _2 = &mut ((*_3).0: i32)
    // _1 = &raw mut (*_2)
    // _6 = const {alloc1: *mut s}
    // _5 = &mut ((*_6).1: i32)
    // _4 = &raw mut (*_5)
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
            pub y: libc::c_int,
        }
        pub static mut s: s = s { x: 0, y: 0 };
        ",
        "",
        "
        let mut x: *mut libc::c_int = &mut s.x;
        let mut y: *mut libc::c_int = &mut s.y;
        ",
        |res, _| {
            assert_eq!(ends_to_vec(&res.ends), vec![1, 1, 2, 3, 4, 5, 6, 7, 8]);
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), e());
            assert_eq!(sol(&res, 3), vec![0]);
            assert_eq!(sol(&res, 4), vec![0]);
            assert_eq!(sol(&res, 5), vec![0]);
            assert_eq!(sol(&res, 6), vec![1]);
            assert_eq!(sol(&res, 7), vec![1]);
            assert_eq!(sol(&res, 8), vec![0]);
        },
    );
}

#[test]
fn test_static_ref() {
    // _3 = const {alloc1: *mut i32}
    // _2 = &(*_3)
    // _1 = &raw const (*_2)
    // _0 = move _1 as *mut i32 (PtrToPtr)
    analyze_fn_with(
        "
        pub static mut x: libc::c_int = 0 as libc::c_int;
        pub static mut y: *mut libc::c_int = unsafe {
            &x as *const libc::c_int as *mut libc::c_int
        };
        ",
        "",
        "
        ",
        |res, _| {
            assert_eq!(ends_to_vec(&res.ends), v(5));
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), vec![0]);
            assert_eq!(sol(&res, 2), vec![0]);
            assert_eq!(sol(&res, 3), vec![0]);
            assert_eq!(sol(&res, 4), vec![0]);
            assert_eq!(sol(&res, 5), e());
        },
    );
}

#[test]
fn test_static_struct_ref() {
    // _5 = const {alloc1: *mut i32}
    // _4 = &(*_5)
    // _3 = &raw const (*_4)
    // _2 = move _3 as *mut i32 (PtrToPtr)
    // _9 = const {alloc2: *mut i32}
    // _8 = &(*_9)
    // _7 = &raw const (*_8)
    // _6 = move _7 as *mut i32 (PtrToPtr)
    // _1 = s { x: move _2, y: move _6 }
    // _0 = _1
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: *mut libc::c_int,
            pub y: *mut libc::c_int,
        }
        pub static mut x: libc::c_int = 0 as libc::c_int;
        pub static mut y: libc::c_int = 0 as libc::c_int;
        pub static mut z: s = unsafe {
            {
                let mut init = s {
                    x: &x as *const libc::c_int as *mut libc::c_int,
                    y: &y as *const libc::c_int as *mut libc::c_int,
                };
                init
            }
        };
        ",
        "",
        "
        ",
        |res, _| {
            assert_eq!(
                ends_to_vec(&res.ends),
                vec![0, 1, 3, 3, 5, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
            );
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), vec![0]);
            assert_eq!(sol(&res, 3), vec![1]);
            assert_eq!(sol(&res, 4), vec![0]);
            assert_eq!(sol(&res, 5), vec![1]);
            assert_eq!(sol(&res, 6), vec![0]);
            assert_eq!(sol(&res, 7), vec![0]);
            assert_eq!(sol(&res, 8), vec![0]);
            assert_eq!(sol(&res, 9), vec![0]);
            assert_eq!(sol(&res, 10), vec![1]);
            assert_eq!(sol(&res, 11), vec![1]);
            assert_eq!(sol(&res, 12), vec![1]);
            assert_eq!(sol(&res, 13), vec![1]);
            assert_eq!(sol(&res, 14), e());
        },
    );
}

#[test]
fn test_cycle() {
    // _1 = const 0_i32
    // _2 = const 0_i32
    // _4 = &mut _1
    // _3 = &raw mut (*_4)
    // _6 = &mut _2
    // _5 = &raw mut (*_6)
    // _7 = _5
    // _3 = move _7
    // _8 = _3
    // _5 = move _8
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut z: *mut libc::c_int = &mut x;
        let mut w: *mut libc::c_int = &mut y;
        z = w;
        w = z;
        ",
        |res, _| {
            assert_eq!(ends_to_vec(&res.ends), v(8));
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), e());
            assert_eq!(sol(&res, 3), vec![1, 2]);
            assert_eq!(sol(&res, 4), vec![1]);
            assert_eq!(sol(&res, 5), vec![1, 2]);
            assert_eq!(sol(&res, 6), vec![2]);
            assert_eq!(sol(&res, 7), vec![1, 2]);
            assert_eq!(sol(&res, 8), vec![1, 2]);
        },
    );
}

#[test]
fn test_cycle_propagate_eq() {
    // _1 = const 0_i32
    // _2 = const 0_i32
    // _4 = &mut _1
    // _3 = &raw mut (*_4)
    // _5 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _7 = &mut _2
    // _6 = &raw mut (*_7)
    // _8 = _5
    // _3 = move _8
    // _9 = _3
    // _5 = move _9
    // _10 = _5
    // _6 = move _10
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut z: *mut libc::c_int = &mut x;
        let mut w: *mut libc::c_int = 0 as *mut libc::c_int;
        let mut v: *mut libc::c_int = &mut y;
        z = w;
        w = z;
        v = w;
        ",
        |res, _| {
            assert_eq!(ends_to_vec(&res.ends), v(10));
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), e());
            assert_eq!(sol(&res, 3), vec![1]);
            assert_eq!(sol(&res, 4), vec![1]);
            assert_eq!(sol(&res, 5), vec![1]);
            assert_eq!(sol(&res, 6), vec![1, 2]);
            assert_eq!(sol(&res, 7), vec![2]);
            assert_eq!(sol(&res, 8), vec![1]);
            assert_eq!(sol(&res, 9), vec![1]);
            assert_eq!(sol(&res, 10), vec![1]);
        },
    );
}

#[test]
fn test_cycle_propagate_eq_deref() {
    // _1 = const 0_i32
    // _3 = &mut _1
    // _2 = &raw mut (*_3)
    // _5 = &mut _2
    // _4 = &raw mut (*_5)
    // _6 = const 0_usize as *mut *mut i32 (PointerFromExposedAddress)
    // _7 = _4
    // _6 = move _7
    // _8 = _6
    // _4 = move _8
    // _9 = (*_4)
    // _10 = (*_6)
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = &mut x;
        let mut z: *mut *mut libc::c_int = &mut y;
        let mut w: *mut *mut libc::c_int = 0 as *mut *mut libc::c_int;
        w = z;
        z = w;
        let mut v: *mut libc::c_int = *z;
        let mut u: *mut libc::c_int = *w;
        ",
        |res, _| {
            assert_eq!(ends_to_vec(&res.ends), v(10));
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), vec![1]);
            assert_eq!(sol(&res, 3), vec![1]);
            assert_eq!(sol(&res, 4), vec![2]);
            assert_eq!(sol(&res, 5), vec![2]);
            assert_eq!(sol(&res, 6), vec![2]);
            assert_eq!(sol(&res, 7), vec![2]);
            assert_eq!(sol(&res, 8), vec![2]);
            assert_eq!(sol(&res, 9), vec![1]);
            assert_eq!(sol(&res, 10), vec![1]);
        },
    );
}

#[test]
fn test_cycle_propagate_deref_eq() {
    // _1 = const 0_i32
    // _2 = const 0_i32
    // _3 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _5 = &mut _3
    // _4 = &raw mut (*_5)
    // _6 = const 0_usize as *mut *mut i32 (PointerFromExposedAddress)
    // _7 = _4
    // _6 = move _7
    // _8 = _6
    // _4 = move _8
    // _10 = &mut _1
    // _9 = &raw mut (*_10)
    // (*_4) = move _9
    // _12 = &mut _2
    // _11 = &raw mut (*_12)
    // (*_6) = move _11
    analyze_fn(
        "
        let mut x0: libc::c_int = 0 as libc::c_int;
        let mut x1: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = 0 as *mut libc::c_int;
        let mut z: *mut *mut libc::c_int = &mut y;
        let mut w: *mut *mut libc::c_int = 0 as *mut *mut libc::c_int;
        w = z;
        z = w;
        *z = &mut x0;
        *w = &mut x1;
        ",
        |res, _| {
            assert_eq!(ends_to_vec(&res.ends), v(12));
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), e());
            assert_eq!(sol(&res, 3), vec![1, 2]);
            assert_eq!(sol(&res, 4), vec![3]);
            assert_eq!(sol(&res, 5), vec![3]);
            assert_eq!(sol(&res, 6), vec![3]);
            assert_eq!(sol(&res, 7), vec![3]);
            assert_eq!(sol(&res, 8), vec![3]);
            assert_eq!(sol(&res, 9), vec![1]);
            assert_eq!(sol(&res, 10), vec![1]);
            assert_eq!(sol(&res, 11), vec![2]);
            assert_eq!(sol(&res, 12), vec![2]);
        },
    );
}

#[test]
fn test_cycle_propagate_ref_deref() {
    // _1 = s { x: const 0_i32, y: const 0_i32 }
    // _3 = &mut _1
    // _2 = &raw mut (*_3)
    // _4 = const 0_usize as *mut s (PointerFromExposedAddress)
    // _5 = _4
    // _2 = move _5
    // _6 = _2
    // _4 = move _6
    // _8 = &mut ((*_2).1: i32)
    // _7 = &raw mut (*_8)
    // _10 = &mut ((*_4).1: i32)
    // _9 = &raw mut (*_10)
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
            pub y: libc::c_int,
        }
        ",
        "",
        "
        let mut s: s = s { x: 0, y: 0 };
        let mut x: *mut s = &mut s;
        let mut y: *mut s = 0 as *mut s;
        x = y;
        y = x;
        let mut z: *mut libc::c_int = &mut (*x).y;
        let mut w: *mut libc::c_int = &mut (*y).y;
        ",
        |res, _| {
            assert_eq!(
                ends_to_vec(&res.ends),
                vec![0, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
            );
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), e());
            assert_eq!(sol(&res, 3), vec![1]);
            assert_eq!(sol(&res, 4), vec![1]);
            assert_eq!(sol(&res, 5), vec![1]);
            assert_eq!(sol(&res, 6), vec![1]);
            assert_eq!(sol(&res, 7), vec![1]);
            assert_eq!(sol(&res, 8), vec![2]);
            assert_eq!(sol(&res, 9), vec![2]);
            assert_eq!(sol(&res, 10), vec![2]);
            assert_eq!(sol(&res, 11), vec![2]);
        },
    );
}

#[test]
fn test_cycle_twice() {
    // _1 = const 0_i32
    // _3 = &mut _1
    // _2 = &raw mut (*_3)
    // _4 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _5 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _7 = &mut _4
    // _6 = &raw mut (*_7)
    // _8 = _4
    // _2 = move _8
    // _9 = _2
    // _4 = move _9
    // _10 = _5
    // _4 = move _10
    // _11 = (*_6)
    // _5 = move _11
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = &mut x;
        let mut z: *mut libc::c_int = 0 as *mut libc::c_int;
        let mut w: *mut libc::c_int = 0 as *mut libc::c_int;
        let mut v: *mut *mut libc::c_int = &mut z;
        y = z;
        z = y;
        z = w;
        w = *v;
        ",
        |res, _| {
            assert_eq!(ends_to_vec(&res.ends), v(11));
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), vec![1]);
            assert_eq!(sol(&res, 3), vec![1]);
            assert_eq!(sol(&res, 4), vec![1]);
            assert_eq!(sol(&res, 5), vec![1]);
            assert_eq!(sol(&res, 6), vec![4]);
            assert_eq!(sol(&res, 7), vec![4]);
            assert_eq!(sol(&res, 8), vec![1]);
            assert_eq!(sol(&res, 9), vec![1]);
            assert_eq!(sol(&res, 10), vec![1]);
            assert_eq!(sol(&res, 11), vec![1]);
        },
    );
}

#[test]
fn test_call() {
    // _2 = const 0_i32
    // _4 = &mut _2
    // _3 = &raw mut (*_4)
    // _1 = move _3
    // _0 = _1
    //
    // _1 = const 0_i32
    // _3 = &mut _1
    // _2 = &raw mut (*_3)
    // _4 = g(_2)
    // _5 = const 0_i32
    // _7 = &mut _5
    // _6 = &raw mut (*_7)
    // _4 = move _6
    analyze_fn_with(
        "
        pub unsafe extern \"C\" fn g(mut x: *mut libc::c_int) -> *mut libc::c_int {
            let mut y: libc::c_int = 0 as libc::c_int;
            x = &mut y;
            return x;
        }
        ",
        "",
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = &mut x;
        let mut z: *mut libc::c_int = g(y);
        let mut w: libc::c_int = 0 as libc::c_int;
        z = &mut w;
        ",
        |res, _| {
            assert_eq!(ends_to_vec(&res.ends), v(12));
            assert_eq!(sol(&res, 0), vec![2, 6]);
            assert_eq!(sol(&res, 1), vec![2, 6]);
            assert_eq!(sol(&res, 2), e());
            assert_eq!(sol(&res, 3), vec![2]);
            assert_eq!(sol(&res, 4), vec![2]);
            assert_eq!(sol(&res, 5), e()); // _0
            assert_eq!(sol(&res, 6), e()); // _1
            assert_eq!(sol(&res, 7), vec![6]);
            assert_eq!(sol(&res, 8), vec![6]);
            assert_eq!(sol(&res, 9), vec![2, 6, 10]);
            assert_eq!(sol(&res, 10), e());
            assert_eq!(sol(&res, 11), vec![10]);
            assert_eq!(sol(&res, 12), vec![10]);
        },
    );
}

#[test]
fn test_call_struct() {
    // _4 = copy (_1.0: *mut i32)
    // _5 = copy (_1.1: *mut i32)
    // _0 = t { x: move _4, y: move _5, z: copy _3 }

    // _1 = const 0_i32
    // _2 = const 0_i32
    // _3 = const 0_i32
    // _6 = &mut _1
    // _5 = &raw mut (*_6)
    // _8 = &mut _2
    // _7 = &raw mut (*_8)
    // _4 = s { x: move _5, y: move _7 }
    // _11 = &mut _3
    // _10 = &raw mut (*_11)
    // _9 = g(copy _4, const 0_i32, move _10) -> [return: bb1, unwind unreachable]
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: *mut libc::c_int,
            pub y: *mut libc::c_int,
        }
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct t {
            pub x: *mut libc::c_int,
            pub y: *mut libc::c_int,
            pub z: *mut libc::c_int,
        }
        pub unsafe extern \"C\" fn g(mut x: s, mut y: libc::c_int, mut z: *mut libc::c_int) -> t {
            let mut w: t = {
                let mut init = t { x: x.x, y: x.y, z: z };
                init
            };
            return w;
        }
        ",
        "",
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut z: libc::c_int = 0 as libc::c_int;
        let mut w: s = {
            let mut init = s { x: &mut x, y: &mut y };
            init
        };
        let mut v: t = g(w, 0 as libc::c_int, &mut z);
        ",
        |res, _| {
            assert_eq!(
                ends_to_vec(&res.ends),
                vec![
                    1, 1, 2, 3, 6, 5, 6, 7, 8, 9, 10, 11, 12, 14, 14, 15, 16, 17, 18, 21, 20, 21,
                    22, 23
                ]
            );
            assert_eq!(sol(&res, 0), vec![10]);
            assert_eq!(sol(&res, 1), vec![11]);
            assert_eq!(sol(&res, 2), e());
            assert_eq!(sol(&res, 3), vec![12]);
            assert_eq!(sol(&res, 4), vec![10]);
            assert_eq!(sol(&res, 5), vec![11]);
            assert_eq!(sol(&res, 6), vec![12]);
            assert_eq!(sol(&res, 7), vec![10]);
            assert_eq!(sol(&res, 8), vec![11]);
            assert_eq!(sol(&res, 9), e());
            assert_eq!(sol(&res, 10), e());
            assert_eq!(sol(&res, 11), e());
            assert_eq!(sol(&res, 12), e());
            assert_eq!(sol(&res, 13), vec![10]);
            assert_eq!(sol(&res, 14), vec![11]);
            assert_eq!(sol(&res, 15), vec![10]);
            assert_eq!(sol(&res, 16), vec![10]);
            assert_eq!(sol(&res, 17), vec![11]);
            assert_eq!(sol(&res, 18), vec![11]);
            assert_eq!(sol(&res, 19), vec![10]);
            assert_eq!(sol(&res, 20), vec![11]);
            assert_eq!(sol(&res, 21), vec![12]);
            assert_eq!(sol(&res, 22), vec![12]);
            assert_eq!(sol(&res, 23), vec![12]);
        },
    );
}

#[test]
fn test_call_fn_ptr() {
    // _4 = copy (_1.0: *mut i32)
    // _5 = copy (_1.1: *mut i32)
    // _0 = t { x: move _4, y: move _5, z: copy _3 }

    // _1 = const 0_i32
    // _2 = const 0_i32
    // _3 = const 0_i32
    // _6 = &mut _1
    // _5 = &raw mut (*_6)
    // _8 = &mut _2
    // _7 = &raw mut (*_8)
    // _4 = s { x: move _5, y: move _7 }
    // _10 = g as unsafe extern "C" fn(s, i32, *mut i32) -> t (PointerCoercion(ReifyFnPointer, AsCast))
    // _9 = std::option::Option::<unsafe extern "C" fn(s, i32, *mut i32) -> t>::Some(move _10)
    // _12 = std::option::Option::<unsafe extern "C" fn(s, i32, *mut i32) -> t>::unwrap(copy _9) -> [return: bb1, unwind terminate(abi)]
    // _14 = &mut _3
    // _13 = &raw mut (*_14)
    // _11 = move _12(copy _4, const 0_i32, move _13) -> [return: bb2, unwind unreachable]
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: *mut libc::c_int,
            pub y: *mut libc::c_int,
        }
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct t {
            pub x: *mut libc::c_int,
            pub y: *mut libc::c_int,
            pub z: *mut libc::c_int,
        }
        pub unsafe extern \"C\" fn g(mut x: s, mut y: libc::c_int, mut z: *mut libc::c_int) -> t {
            let mut w: t = {
                let mut init = t { x: x.x, y: x.y, z: z };
                init
            };
            return w;
        }
        ",
        "",
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut z: libc::c_int = 0 as libc::c_int;
        let mut w: s = {
            let mut init = s { x: &mut x, y: &mut y };
            init
        };
        let mut h: Option::<unsafe extern \"C\" fn(s, libc::c_int, *mut libc::c_int) -> t> = Some(
            g as unsafe extern \"C\" fn(s, libc::c_int, *mut libc::c_int) -> t,
        );
        let mut v: t = h.unwrap()(w, 0 as libc::c_int, &mut z);
        ",
        |res, _| {
            assert_eq!(
                ends_to_vec(&res.ends),
                vec![
                    6, 1, 2, 3, 6, 5, 6, 7, 8, 9, 10, 11, 12, 14, 14, 15, 16, 17, 18, 19, 20, 23,
                    22, 23, 24, 25, 26
                ]
            );
            assert_eq!(sol(&res, 0), vec![10]);
            assert_eq!(sol(&res, 1), vec![11]);
            assert_eq!(sol(&res, 2), e());
            assert_eq!(sol(&res, 3), vec![12]);
            assert_eq!(sol(&res, 4), vec![10]);
            assert_eq!(sol(&res, 5), vec![11]);
            assert_eq!(sol(&res, 6), vec![12]);
            assert_eq!(sol(&res, 7), vec![10]);
            assert_eq!(sol(&res, 8), vec![11]);
            assert_eq!(sol(&res, 9), e());
            assert_eq!(sol(&res, 10), e());
            assert_eq!(sol(&res, 11), e());
            assert_eq!(sol(&res, 12), e());
            assert_eq!(sol(&res, 13), vec![10]);
            assert_eq!(sol(&res, 14), vec![11]);
            assert_eq!(sol(&res, 15), vec![10]);
            assert_eq!(sol(&res, 16), vec![10]);
            assert_eq!(sol(&res, 17), vec![11]);
            assert_eq!(sol(&res, 18), vec![11]);
            assert_eq!(sol(&res, 19), vec![0]);
            assert_eq!(sol(&res, 20), vec![0]);
            assert_eq!(sol(&res, 21), vec![10]);
            assert_eq!(sol(&res, 22), vec![11]);
            assert_eq!(sol(&res, 23), vec![12]);
            assert_eq!(sol(&res, 24), vec![0]);
            assert_eq!(sol(&res, 25), vec![12]);
            assert_eq!(sol(&res, 26), vec![12]);
        },
    );
}

#[test]
fn test_array_offset() {
    // _1 = [const 0_i32; 2]
    // _7 = &mut _1
    // _6 = move _7 as &mut [i32] (PointerCoercion(Unsize, Implicit))
    // _5 = core::slice::<impl [i32]>::as_mut_ptr(move _6) -> [return: bb1, unwind terminate(abi)]
    // _8 = const 1_i32 as isize (IntToInt)
    // _4 = std::ptr::mut_ptr::<impl *mut i32>::offset(move _5, move _8) -> [return: bb2, unwind terminate(abi)]
    // _3 = &mut (*_4)
    // _2 = &raw mut (*_3)
    analyze_fn(
        "
        let mut x: [libc::c_int; 2] = [0; 2];
        let mut y: *mut libc::c_int = &mut *x.as_mut_ptr().offset(1 as libc::c_int as isize)
            as *mut libc::c_int;
        ",
        |res, _| {
            assert_eq!(ends_to_vec(&res.ends), v(8));
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), vec![1]);
            assert_eq!(sol(&res, 3), vec![1]);
            assert_eq!(sol(&res, 4), vec![1]);
            assert_eq!(sol(&res, 5), vec![1]);
            assert_eq!(sol(&res, 6), vec![1]);
            assert_eq!(sol(&res, 7), vec![1]);
            assert_eq!(sol(&res, 8), e());
        },
    );
}

#[test]
fn test_malloc() {
    // _4 = std::mem::size_of::<i32>()
    // _3 = move _4 as u64 (IntToInt)
    // _2 = malloc(move _3)
    // _1 = move _2 as *mut i32 (PtrToPtr)
    analyze_fn(
        "
        let mut x: *mut libc::c_int = malloc(
            ::std::mem::size_of::<libc::c_int>() as libc::c_ulong,
        ) as *mut libc::c_int;
        ",
        |res, _| {
            assert_eq!(ends_to_vec(&res.ends), v(5));
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), vec![5]);
            assert_eq!(sol(&res, 2), vec![5]);
            assert_eq!(sol(&res, 3), e());
            assert_eq!(sol(&res, 4), e());
            assert_eq!(sol(&res, 5), e());
        },
    );
}

#[test]
fn test_malloc_struct() {
    // _1 = const 0_i32
    // _2 = const 0_i32
    // _3 = const 0_i32
    // _4 = const 0_i32
    // _8 = std::mem::size_of::<s>() -> [return: bb1, unwind continue]
    // _7 = move _8 as u64 (IntToInt)
    // _6 = malloc(move _7) -> [return: bb2, unwind continue]
    // _5 = move _6 as *mut s (PtrToPtr)
    // _10 = &mut _1
    // _9 = &raw mut (*_10)
    // ((*_5).0: *mut i32) = move _9
    // _12 = &mut _2
    // _11 = &raw mut (*_12)
    // ((*_5).1: *mut i32) = move _11
    // _14 = &mut _3
    // _13 = &raw mut (*_14)
    // ((*_5).2: *mut i32) = move _13
    // _18 = std::mem::size_of::<r>() -> [return: bb3, unwind continue]
    // _17 = move _18 as u64 (IntToInt)
    // _16 = malloc(move _17) -> [return: bb4, unwind continue]
    // _15 = move _16 as *mut r (PtrToPtr)
    // _20 = &mut _1
    // _19 = &raw mut (*_20)
    // (((*_15).0: t).0: *mut i32) = move _19
    // _22 = &mut _2
    // _21 = &raw mut (*_22)
    // (((*_15).0: t).1: *mut i32) = move _21
    // _24 = &mut ((*_15).1: t)
    // _23 = &raw mut (*_24)
    // _26 = &mut _3
    // _25 = &raw mut (*_26)
    // ((*_23).0: *mut i32) = move _25
    // _28 = &mut _4
    // _27 = &raw mut (*_28)
    // ((*_23).1: *mut i32) = move _27
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: *mut libc::c_int,
            pub y: *mut libc::c_int,
            pub z: *mut libc::c_int,
        }
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct t {
            pub x: *mut libc::c_int,
            pub y: *mut libc::c_int,
        }
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct r {
            pub x: t,
            pub y: t,
        }
        ",
        "",
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut z: libc::c_int = 0 as libc::c_int;
        let mut w: libc::c_int = 0 as libc::c_int;
        let mut s: *mut s = malloc(::std::mem::size_of::<s>() as libc::c_ulong) as *mut s;
        (*s).x = &mut x;
        (*s).y = &mut y;
        (*s).z = &mut z;
        let mut r: *mut r = malloc(::std::mem::size_of::<r>() as libc::c_ulong) as *mut r;
        (*r).x.x = &mut x;
        (*r).x.y = &mut y;
        let mut t: *mut t = &mut (*r).y;
        (*t).x = &mut z;
        (*t).y = &mut w;
        ",
        |res, _| {
            let mut v = v(28);
            v.extend([32, 30, 32, 32, 36, 34, 36, 36]);
            assert_eq!(ends_to_vec(&res.ends), v);
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), e());
            assert_eq!(sol(&res, 3), e());
            assert_eq!(sol(&res, 4), e());
            assert_eq!(sol(&res, 5), vec![29]);
            assert_eq!(sol(&res, 6), vec![29]);
            assert_eq!(sol(&res, 7), e());
            assert_eq!(sol(&res, 8), e());
            assert_eq!(sol(&res, 9), vec![1]);
            assert_eq!(sol(&res, 10), vec![1]);
            assert_eq!(sol(&res, 11), vec![2]);
            assert_eq!(sol(&res, 12), vec![2]);
            assert_eq!(sol(&res, 13), vec![3]);
            assert_eq!(sol(&res, 14), vec![3]);
            assert_eq!(sol(&res, 15), vec![33]);
            assert_eq!(sol(&res, 16), vec![33]);
            assert_eq!(sol(&res, 17), e());
            assert_eq!(sol(&res, 18), e());
            assert_eq!(sol(&res, 19), vec![1]);
            assert_eq!(sol(&res, 20), vec![1]);
            assert_eq!(sol(&res, 21), vec![2]);
            assert_eq!(sol(&res, 22), vec![2]);
            assert_eq!(sol(&res, 23), vec![35]);
            assert_eq!(sol(&res, 24), vec![35]);
            assert_eq!(sol(&res, 25), vec![3]);
            assert_eq!(sol(&res, 26), vec![3]);
            assert_eq!(sol(&res, 27), vec![4]);
            assert_eq!(sol(&res, 28), vec![4]);
            assert_eq!(sol(&res, 29), vec![1]);
            assert_eq!(sol(&res, 30), vec![2]);
            assert_eq!(sol(&res, 31), vec![3]);
            assert_eq!(sol(&res, 32), e());
            assert_eq!(sol(&res, 33), vec![1]);
            assert_eq!(sol(&res, 34), vec![2]);
            assert_eq!(sol(&res, 35), vec![3]);
            assert_eq!(sol(&res, 36), vec![4]);
        },
    );
}

#[test]
fn test_custom_malloc() {
    // _2 = _1 as u64 (IntToInt)
    // _0 = malloc(move _2) -> [return: bb1, unwind continue]
    //
    // _5 = std::mem::size_of::<i32>() -> [return: bb1, unwind continue]
    // _4 = move _5 as u64 (IntToInt)
    // _3 = move _4 as i32 (IntToInt)
    // _2 = g(move _3) -> [return: bb2, unwind continue]
    // _1 = move _2 as *mut i32 (PtrToPtr)
    // _10 = std::mem::size_of::<i32>() -> [return: bb3, unwind continue]
    // _9 = move _10 as u64 (IntToInt)
    // _8 = move _9 as i32 (IntToInt)
    // _7 = g(move _8) -> [return: bb4, unwind continue]
    // _6 = move _7 as *mut i32 (PtrToPtr)
    analyze_fn_with(
        "
        pub unsafe extern \"C\" fn g(mut x: libc::c_int) -> *mut libc::c_void {
            return malloc(x as libc::c_ulong);
        }
        ",
        "",
        "
        let mut x: *mut libc::c_int = g(
            ::std::mem::size_of::<libc::c_int>() as libc::c_ulong as libc::c_int,
        ) as *mut libc::c_int;
        let mut y: *mut libc::c_int = g(
            ::std::mem::size_of::<libc::c_int>() as libc::c_ulong as libc::c_int,
        ) as *mut libc::c_int;
        ",
        |res, _| {
            assert_eq!(ends_to_vec(&res.ends), v(16));
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), vec![14]);
            assert_eq!(sol(&res, 2), e());
            assert_eq!(sol(&res, 3), e());
            assert_eq!(sol(&res, 4), vec![15]);
            assert_eq!(sol(&res, 5), vec![15]);
            assert_eq!(sol(&res, 6), e());
            assert_eq!(sol(&res, 7), e());
            assert_eq!(sol(&res, 8), e());
            assert_eq!(sol(&res, 9), vec![16]);
            assert_eq!(sol(&res, 10), vec![16]);
            assert_eq!(sol(&res, 11), e());
            assert_eq!(sol(&res, 12), e());
            assert_eq!(sol(&res, 13), e());
            assert_eq!(sol(&res, 14), e());
            assert_eq!(sol(&res, 15), e());
            assert_eq!(sol(&res, 16), e());
        },
    );
}

fn l(block: usize, statement_index: usize) -> Location {
    Location {
        block: BasicBlock::new(block),
        statement_index,
    }
}

fn wg(
    writes: &FxHashMap<Location, ChunkedBitSet<Loc>>,
    block: usize,
    statement_index: usize,
) -> Vec<usize> {
    writes
        .get(&l(block, statement_index))
        .unwrap()
        .iter()
        .map(|loc| loc.index())
        .collect()
}

#[test]
fn test_writes_compound() {
    // _1 = const 0_i32
    // _2 = const 0_i32
    // _3 = const 0_i32
    // _7 = &mut _1
    // _6 = &raw mut (*_7)
    // _9 = &mut _2
    // _8 = &raw mut (*_9)
    // _5 = s { x: move _6, y: move _8 }
    // _12 = &mut _3
    // _11 = &raw mut (*_12)
    // _13 = const 0_usize as *mut i32 (PointerWithExposedProvenance)
    // _10 = [move _11, move _13]
    // _4 = t { x: copy _5, y: move _10 }
    // _1 = const 1_i32
    // _2 = const 1_i32
    // _3 = const 1_i32
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: *mut libc::c_int,
            pub y: *mut libc::c_int,
        }
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct t {
            pub x: s,
            pub y: [*mut libc::c_int; 2],
        }
        ",
        "",
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut z: libc::c_int = 0 as libc::c_int;
        let mut w: t = {
            let mut init = t {
                x: {
                    let mut init = s { x: &mut x, y: &mut y };
                    init
                },
                y: [&mut z, 0 as *mut libc::c_int],
            };
            init
        };
        x = 1 as libc::c_int;
        y = 1 as libc::c_int;
        z = 1 as libc::c_int;
        ",
        |mut res, tcx| {
            assert_eq!(
                ends_to_vec(&res.ends),
                vec![0, 1, 2, 3, 6, 5, 6, 8, 8, 9, 10, 11, 12, 13, 14, 15, 16]
            );
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), e());
            assert_eq!(sol(&res, 3), e());
            assert_eq!(sol(&res, 4), vec![1]);
            assert_eq!(sol(&res, 5), vec![2]);
            assert_eq!(sol(&res, 6), vec![3]);
            assert_eq!(sol(&res, 7), vec![1]);
            assert_eq!(sol(&res, 8), vec![2]);
            assert_eq!(sol(&res, 9), vec![1]);
            assert_eq!(sol(&res, 10), vec![1]);
            assert_eq!(sol(&res, 11), vec![2]);
            assert_eq!(sol(&res, 12), vec![2]);
            assert_eq!(sol(&res, 13), vec![3]);
            assert_eq!(sol(&res, 14), vec![3]);
            assert_eq!(sol(&res, 15), vec![3]);
            assert_eq!(sol(&res, 16), e());

            let def_id = find("f", tcx);
            let w = res.writes.remove(&def_id).unwrap();
            assert_eq!(wg(&w, 0, 0), vec![1]);
            assert_eq!(wg(&w, 0, 1), vec![2]);
            assert_eq!(wg(&w, 0, 2), vec![3]);
            assert_eq!(wg(&w, 0, 3), e());
            assert_eq!(wg(&w, 0, 4), e());
            assert_eq!(wg(&w, 0, 5), e());
            assert_eq!(wg(&w, 0, 6), e());
            assert_eq!(wg(&w, 0, 7), e());
            assert_eq!(wg(&w, 0, 8), e());
            assert_eq!(wg(&w, 0, 9), e());
            assert_eq!(wg(&w, 0, 10), e());
            assert_eq!(wg(&w, 0, 11), e());
            assert_eq!(wg(&w, 0, 12), e());
            assert_eq!(wg(&w, 0, 13), vec![1]);
            assert_eq!(wg(&w, 0, 14), vec![2]);
            assert_eq!(wg(&w, 0, 15), vec![3]);
        },
    );
}

#[test]
fn test_writes_multiple() {
    // _1 = const 0_i32
    // _3 = &mut _1
    // _2 = &raw mut (*_3)
    // _5 = &mut _1
    // _4 = &raw mut (*_5)
    // _7 = &mut _2
    // _6 = &raw mut (*_7)
    // _10 = &mut _6
    // _9 = &raw mut (*_10)
    // _8 = move _9 as *mut libc::c_void (PtrToPtr)
    // _12 = &mut _4
    // _11 = &raw mut (*_12)
    // _8 = move _11 as *mut libc::c_void (PtrToPtr)
    // _1 = const 1_i32
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = &mut x;
        let mut z: *mut libc::c_int = &mut x;
        let mut w: *mut *mut libc::c_int = &mut y;
        let mut v: *mut libc::c_void = &mut w as *mut *mut *mut libc::c_int
            as *mut libc::c_void;
        v = &mut z as *mut *mut libc::c_int as *mut libc::c_void;
        x = 1 as libc::c_int;
        ",
        |mut res, tcx| {
            assert_eq!(ends_to_vec(&res.ends), v(12));
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), vec![1]);
            assert_eq!(sol(&res, 3), vec![1]);
            assert_eq!(sol(&res, 4), vec![1]);
            assert_eq!(sol(&res, 5), vec![1]);
            assert_eq!(sol(&res, 6), vec![2]);
            assert_eq!(sol(&res, 7), vec![2]);
            assert_eq!(sol(&res, 8), vec![4, 6]);
            assert_eq!(sol(&res, 9), vec![6]);
            assert_eq!(sol(&res, 10), vec![6]);
            assert_eq!(sol(&res, 11), vec![4]);
            assert_eq!(sol(&res, 12), vec![4]);

            let def_id = find("f", tcx);
            let w = res.writes.remove(&def_id).unwrap();
            assert_eq!(wg(&w, 0, 0), vec![1]);
            assert_eq!(wg(&w, 0, 1), e());
            assert_eq!(wg(&w, 0, 2), vec![2]);
            assert_eq!(wg(&w, 0, 3), e());
            assert_eq!(wg(&w, 0, 4), vec![4]);
            assert_eq!(wg(&w, 0, 5), e());
            assert_eq!(wg(&w, 0, 6), vec![6]);
            assert_eq!(wg(&w, 0, 7), e());
            assert_eq!(wg(&w, 0, 8), e());
            assert_eq!(wg(&w, 0, 9), e());
            assert_eq!(wg(&w, 0, 10), e());
            assert_eq!(wg(&w, 0, 11), e());
            assert_eq!(wg(&w, 0, 12), e());
            assert_eq!(wg(&w, 0, 13), vec![1]);
        },
    );
}

#[test]
fn test_writes_ambiguous() {
    // _1 = const 0_i32
    // _5 = &mut _1
    // _4 = &raw mut (*_5)
    // _3 = s { x: move _4 }
    // _2 = _3
    // _7 = &mut (_2.0: *mut i32)
    // _6 = &raw mut (*_7)
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: *mut libc::c_int,
        }
        ",
        "",
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: s = {
            let mut init = s { x: &mut x };
            init
        };
        let mut z: *mut *mut libc::c_int = &mut y.x;
        ",
        |mut res, tcx| {
            assert_eq!(ends_to_vec(&res.ends), v(7));
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), vec![1]);
            assert_eq!(sol(&res, 3), vec![1]);
            assert_eq!(sol(&res, 4), vec![1]);
            assert_eq!(sol(&res, 5), vec![1]);
            assert_eq!(sol(&res, 6), vec![2]);
            assert_eq!(sol(&res, 7), vec![2]);

            let def_id = find("f", tcx);
            let w = res.writes.remove(&def_id).unwrap();
            assert_eq!(wg(&w, 0, 0), vec![1]);
            assert_eq!(wg(&w, 0, 1), e());
            assert_eq!(wg(&w, 0, 2), e());
            assert_eq!(wg(&w, 0, 3), e());
            assert_eq!(wg(&w, 0, 4), vec![2]);
            assert_eq!(wg(&w, 0, 5), e());
            assert_eq!(wg(&w, 0, 6), e());
        },
    );
}

#[test]
fn test_writes_double() {
    // _1 = const 0_i32
    // _2 = const 0_i32
    // _4 = &mut _1
    // _3 = &raw mut (*_4)
    // _6 = &mut _2
    // _5 = &raw mut (*_6)
    // _3 = move _5
    // (*_3) = const 1_i32
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut z: *mut libc::c_int = &mut x;
        z = &mut y;
        *z = 1 as libc::c_int;
        ",
        |mut res, tcx| {
            assert_eq!(ends_to_vec(&res.ends), v(6));
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), e());
            assert_eq!(sol(&res, 3), vec![1, 2]);
            assert_eq!(sol(&res, 4), vec![1]);
            assert_eq!(sol(&res, 5), vec![2]);
            assert_eq!(sol(&res, 6), vec![2]);

            let def_id = find("f", tcx);
            let w = res.writes.remove(&def_id).unwrap();
            assert_eq!(wg(&w, 0, 0), vec![1]);
            assert_eq!(wg(&w, 0, 1), vec![2]);
            assert_eq!(wg(&w, 0, 2), e());
            assert_eq!(wg(&w, 0, 3), e());
            assert_eq!(wg(&w, 0, 4), e());
            assert_eq!(wg(&w, 0, 5), e());
            assert_eq!(wg(&w, 0, 6), e());
            assert_eq!(wg(&w, 0, 7), vec![1, 2]);
        },
    );
}

#[test]
fn test_writes_malloc() {
    // _1 = const 0_i32
    // _3 = &mut _1
    // _2 = &raw mut (*_3)
    // _7 = std::mem::size_of::<*mut i32>() -> [return: bb1, unwind continue]
    // _6 = move _7 as u64 (IntToInt)
    // _5 = malloc(move _6) -> [return: bb2, unwind continue]
    // _4 = move _5 as *mut *mut i32 (PtrToPtr)
    // (*_4) = _2
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = &mut x;
        let mut z: *mut *mut libc::c_int = malloc(
            ::std::mem::size_of::<*mut libc::c_int>() as libc::c_ulong,
        ) as *mut *mut libc::c_int;
        *z = y;
        ",
        |mut res, tcx| {
            assert_eq!(ends_to_vec(&res.ends), v(8));
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), vec![1]);
            assert_eq!(sol(&res, 3), vec![1]);
            assert_eq!(sol(&res, 4), vec![8]);
            assert_eq!(sol(&res, 5), vec![8]);
            assert_eq!(sol(&res, 6), e());
            assert_eq!(sol(&res, 7), e());
            assert_eq!(sol(&res, 8), vec![1]);

            let def_id = find("f", tcx);
            let w = res.writes.remove(&def_id).unwrap();
            assert_eq!(wg(&w, 0, 0), vec![1]);
            assert_eq!(wg(&w, 0, 1), e());
            assert_eq!(wg(&w, 0, 2), e());
            assert_eq!(wg(&w, 0, 3), e());
            assert_eq!(wg(&w, 1, 0), e());
            assert_eq!(wg(&w, 1, 1), e());
            assert_eq!(wg(&w, 2, 0), e());
            assert_eq!(wg(&w, 2, 1), vec![8]);
        },
    );
}

#[test]
fn test_writes_field_taken() {
    // _1 = s { x: const 0_i32, y: const 0_i32 }
    // _3 = &mut _1
    // _2 = &raw mut (*_3)
    // (_1.1: i32) = const 1_i32
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
            pub y: libc::c_int,
        }
        ",
        "",
        "
        let mut x: s = s { x: 0, y: 0 };
        let mut y: *mut s = &mut x;
        x.y = 1 as libc::c_int;
        ",
        |mut res, tcx| {
            assert_eq!(ends_to_vec(&res.ends), vec![0, 2, 2, 3, 4]);
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), e());
            assert_eq!(sol(&res, 3), vec![1]);
            assert_eq!(sol(&res, 4), vec![1]);

            let def_id = find("f", tcx);
            let w = res.writes.remove(&def_id).unwrap();
            assert_eq!(wg(&w, 0, 0), vec![1, 2]);
            assert_eq!(wg(&w, 0, 1), e());
            assert_eq!(wg(&w, 0, 2), e());
            assert_eq!(wg(&w, 0, 3), vec![2]);
        },
    );
}

#[test]
fn test_writes_field_untaken() {
    // _1 = s { x: const 0_i32, y: const 0_i32 }
    // _3 = &mut (_1.1: i32)
    // _2 = &raw mut (*_3)
    // (_1.0: i32) = const 2_i32
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
            pub y: libc::c_int,
        }
        ",
        "",
        "
        let mut x: s = s { x: 0, y: 0 };
        let mut y: *mut libc::c_int = &mut x.y;
        x.x = 2 as libc::c_int;
        ",
        |mut res, tcx| {
            assert_eq!(ends_to_vec(&res.ends), vec![0, 2, 2, 3, 4]);
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), e());
            assert_eq!(sol(&res, 3), vec![2]);
            assert_eq!(sol(&res, 4), vec![2]);

            let def_id = find("f", tcx);
            let w = res.writes.remove(&def_id).unwrap();
            assert_eq!(wg(&w, 0, 0), vec![2]);
            assert_eq!(wg(&w, 0, 1), e());
            assert_eq!(wg(&w, 0, 2), e());
            assert_eq!(wg(&w, 0, 3), e());
        },
    );
}

#[test]
fn test_writes_bitfield() {
    // _2 = [const 0_u8]
    // _3 = [const 0_u8; 3]
    // _1 = s { x: const 0_i32, y_z: move _2, c2rust_padding: move _3 }
    // _4 = copy _1
    // (_4.0: i32) = const 1_i32
    // _6 = &mut _4
    // _5 = s::set_y(move _6, const 2_i32) -> [return: bb1, unwind terminate(abi)]
    // _8 = &mut _4
    // _7 = s::set_z(move _8, const 3_i32) -> [return: bb2, unwind terminate(abi)]
    analyze_fn_with(
        "
        #[derive(Copy, Clone, BitfieldStruct)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
            #[bitfield(name = \"y\", ty = \"libc::c_int\", bits = \"0..=2\")]
            #[bitfield(name = \"z\", ty = \"libc::c_int\", bits = \"3..=7\")]
            pub y_z: [u8; 1],
            #[bitfield(padding)]
            pub c2rust_padding: [u8; 3],
        }
        ",
        "",
        "
        let mut x: s = s {
            x: 0,
            y_z: [0; 1],
            c2rust_padding: [0; 3],
        };
        let mut y: s = x;
        y.x = 1 as libc::c_int;
        y.set_y(2 as libc::c_int);
        y.set_z(3 as libc::c_int);
        ",
        |mut res, tcx| {
            assert_eq!(
                ends_to_vec(&res.ends),
                vec![0, 5, 2, 3, 4, 5, 6, 7, 12, 9, 10, 11, 12, 13, 14, 15, 16]
            );
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), e());
            assert_eq!(sol(&res, 3), e());
            assert_eq!(sol(&res, 4), e());
            assert_eq!(sol(&res, 5), e());
            assert_eq!(sol(&res, 6), e());
            assert_eq!(sol(&res, 7), e());
            assert_eq!(sol(&res, 8), e());
            assert_eq!(sol(&res, 9), e());
            assert_eq!(sol(&res, 10), e());
            assert_eq!(sol(&res, 11), e());
            assert_eq!(sol(&res, 12), e());
            assert_eq!(sol(&res, 13), e());
            assert_eq!(sol(&res, 14), vec![8]);
            assert_eq!(sol(&res, 15), e());
            assert_eq!(sol(&res, 16), vec![8]);

            let def_id = find("f", tcx);
            let w = res.writes.remove(&def_id).unwrap();
            assert_eq!(wg(&w, 0, 0), e());
            assert_eq!(wg(&w, 0, 1), e());
            assert_eq!(wg(&w, 0, 2), e());
            assert_eq!(wg(&w, 0, 3), vec![8, 9, 10, 11, 12]);
            assert_eq!(wg(&w, 0, 4), vec![8]);
            assert_eq!(wg(&w, 0, 5), e());
            assert_eq!(wg(&w, 0, 6), e());
            assert_eq!(wg(&w, 1, 0), e());
            assert_eq!(wg(&w, 1, 1), e());
            let w = res.bitfield_writes.remove(&def_id).unwrap();
            assert_eq!(wg(&w, 0, 6), vec![11]);
            assert_eq!(wg(&w, 1, 1), vec![12]);
        },
    );
}

#[test]
fn test_writes_struct_bitfield() {
    // _2 = s { x: const 0_i32, y: const 0_i32 }
    // _3 = [const 0_u8]
    // _4 = [const 0_u8; 3]
    // _1 = t { x: move _2, y_z: move _3, c2rust_padding: move _4 }
    // _6 = &mut _1
    // _5 = t::set_y(move _6, const 1_i32) -> [return: bb1, unwind terminate(abi)]
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
            pub y: libc::c_int,
        }
        #[derive(Copy, Clone, BitfieldStruct)]
        #[repr(C)]
        pub struct t {
            pub x: s,
            #[bitfield(name = \"y\", ty = \"libc::c_int\", bits = \"0..=0\")]
            #[bitfield(name = \"z\", ty = \"libc::c_int\", bits = \"1..=1\")]
            pub y_z: [u8; 1],
            #[bitfield(padding)]
            pub c2rust_padding: [u8; 3],
        }
        ",
        "",
        "
        let mut x: t = t {
            x: s { x: 0, y: 0 },
            y_z: [0; 1],
            c2rust_padding: [0; 3],
        };
        x.set_y(1 as libc::c_int);
        ",
        |mut res, tcx| {
            assert_eq!(
                ends_to_vec(&res.ends),
                vec![0, 6, 2, 3, 4, 5, 6, 8, 8, 9, 10, 11, 12],
            );
            assert_eq!(sol(&res, 0), e());
            assert_eq!(sol(&res, 1), e());
            assert_eq!(sol(&res, 2), e());
            assert_eq!(sol(&res, 3), e());
            assert_eq!(sol(&res, 4), e());
            assert_eq!(sol(&res, 5), e());
            assert_eq!(sol(&res, 6), e());
            assert_eq!(sol(&res, 7), e());
            assert_eq!(sol(&res, 8), e());
            assert_eq!(sol(&res, 9), e());
            assert_eq!(sol(&res, 10), e());
            assert_eq!(sol(&res, 11), e());
            assert_eq!(sol(&res, 12), vec![1]);

            let def_id = find("f", tcx);
            let w = res.writes.remove(&def_id).unwrap();
            assert_eq!(wg(&w, 0, 0), e());
            assert_eq!(wg(&w, 0, 1), e());
            assert_eq!(wg(&w, 0, 2), e());
            assert_eq!(wg(&w, 0, 3), vec![1, 2, 3, 4, 5, 6]);
            assert_eq!(wg(&w, 0, 4), e());
            assert_eq!(wg(&w, 0, 5), e());
            let w = res.bitfield_writes.remove(&def_id).unwrap();
            assert_eq!(wg(&w, 0, 5), vec![5]);
        },
    );
}

#[test]
fn test_call_graph() {
    // _1 = g() -> [return: bb1, unwind continue]
    // _3 = _1
    // switchInt(move _3) -> [0: bb3, otherwise: bb2]
    // _4 = h as unsafe extern "C" fn() (PointerCoercion(ReifyFnPointer))
    // _2 = std::option::Option::<unsafe extern "C" fn()>::Some(move _4)
    // goto -> bb4
    // _5 = i as unsafe extern "C" fn() (PointerCoercion(ReifyFnPointer))
    // _2 = std::option::Option::<unsafe extern "C" fn()>::Some(move _5)
    // goto -> bb4
    // _9 = _2
    // _8 = std::option::Option::<unsafe extern "C" fn()>::unwrap(move _9) -> [return: bb5, unwind continue]
    // _7 = move _8 as fn() (Transmute)
    // _6 = move _7() -> [return: bb6, unwind continue]
    analyze_fn_with(
        "
        pub unsafe extern \"C\" fn g() -> libc::c_int {
            return 0 as libc::c_int;
        }
        pub unsafe extern \"C\" fn h() {}
        pub unsafe extern \"C\" fn i() {}
        ",
        "",
        "
            let mut x: libc::c_int = g();
            let mut y: Option::<unsafe extern \"C\" fn() -> ()> = if x != 0 {
                Some(
                    ::std::mem::transmute::<
                        unsafe extern \"C\" fn() -> (),
                        unsafe extern \"C\" fn() -> (),
                    >(h),
                )
            } else {
                Some(
                    ::std::mem::transmute::<
                        unsafe extern \"C\" fn() -> (),
                        unsafe extern \"C\" fn() -> (),
                    >(i),
                )
            };
            ::std::mem::transmute::<_, fn()>(y.unwrap())();
        ",
        |res, tcx| {
            let def_id = find("f", tcx);
            let indirect_calls = &res.indirect_calls[&def_id];
            assert_eq!(indirect_calls.len(), 1);
            let callees = &indirect_calls[&BasicBlock::new(5)];
            assert_eq!(callees.len(), 2);
            assert!(callees.contains(&find("h", tcx)));
            assert!(callees.contains(&find("i", tcx)));
        },
    );
}
