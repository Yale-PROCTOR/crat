use rustc_abi::FieldIdx;
use rustc_hash::FxHashMap;
use rustc_middle::{
    mir::{Local, Location, TerminatorKind},
    ty::TyCtxt,
};
use rustc_span::def_id::LocalDefId;
use utils::compilation;

use super::{
    analysis::{AnalysisResult, analyze},
    domains::*,
};

/// The indexing of locations in `must_analysis` is identical to the
/// `may_analysis` (see `src/may_analysis/mod.rs`).
///
/// Test cases use `urcrat::must_analysis::domains::Graph`. For example,
/// consider the following MIR code:
///
/// ```
/// _1 = s { x: const 0_i32, y: const 1_i32 }
/// _2 = copy (_1.0: i32)
/// _3 = copy (_1.1: i32)
/// ```
///
/// The resulting `Graph` would be:
///
/// ```
/// Graph {
///     nodes: {
///         0: @{0},
///         1: [0: 0, 1: 2],
///         2: @{1},
///         3: 0,
///         4: 2,
///     },
///     locals: {
///         _1: 1,
///         _2: 3,
///         _3: 4,
///     }
/// }
/// ```
///
/// `Graph.nodes` maps locations to values.
/// - Values prefixed with `@` are "imaginary" values-abstract,
///   analysis-specific values.
/// - For example, `0: @{0}` means that location `0` holds the abstract value
///   `0`. (literally 0).
///
/// `Graph.locals` maps local variables to their corresponding locations.
/// - You can extract this mapping using the `get_ids` function. For example:
///   `get_ids(g, 1..=3)` returns a map of local variables `_1`, `_2`, and `_3` to
///   their location indices.
///
/// To extract the values of local variables, use `get_nodes(g, 1..=3)`, which
/// returns a mapping from local variable to the values they hold.
///
/// To extract The "imaginary" value of a local variable (if it has one), use
/// `g.get_local_as_int(Local::from_usize(1))`, which returns the "imaginary" value held by `_1`,
/// if it is of the form `@{N}`
///
/// To extract the "imaginary" value at a specific field accessed via a pointer,
/// use `g.get_absloc_as_int(n[&1].field(0).as_ptr())`, which returns the
/// imaginary value pointed to by field `0` of `_1`.

fn run_compiler<F: FnOnce(TyCtxt<'_>) + Send>(code: &str, f: F) {
    compilation::run_compiler_on_str(code, f).unwrap_or_else(|e| e.raise());
}

fn find_fn(name: &str, tcx: TyCtxt<'_>) -> LocalDefId {
    tcx.hir_free_items()
        .find_map(|item_id| {
            let item = tcx.hir_item(item_id);
            if let rustc_hir::ItemKind::Fn { ident, .. } = item.kind
                && ident.name.as_str() == name
            {
                Some(item_id.owner_id.def_id)
            } else {
                None
            }
        })
        .unwrap()
}

fn find_return(def_id: LocalDefId, tcx: TyCtxt<'_>) -> Location {
    let body = tcx.optimized_mir(def_id);
    let (bb, bbd) = body
        .basic_blocks
        .iter_enumerated()
        .find(|(_, bbd)| bbd.terminator().kind == TerminatorKind::Return)
        .unwrap();
    Location {
        block: bb,
        statement_index: bbd.statements.len(),
    }
}

fn analyze_fn_with<F>(types: &str, params: &str, code: &str, f: F)
where F: FnOnce(Graph, AnalysisResult, TyCtxt<'_>) + Send {
    let name = "foo";
    let code = format!(
        "
        extern crate libc;
        #[macro_use]
        extern crate c2rust_bitfields;
        {}
        unsafe extern \"C\" fn {}({}) {{
            {}
        }}
    ",
        types, name, params, code
    );
    run_compiler(&code, |tcx| {
        let res = analyze(false, tcx);
        let def_id = find_fn(name, tcx);
        let loc = find_return(def_id, tcx);
        let state = res.functions[&def_id][&loc].clone();
        let AbsMem::Mem(graph) = state else { panic!() };
        // println!("{:?}", graph);
        f(graph, res, tcx);
    });
}

fn analyze_fn<F>(code: &str, f: F)
where F: FnOnce(Graph, AnalysisResult, TyCtxt<'_>) + Send {
    analyze_fn_with("", "", code, f);
}

fn get_nodes<'a>(g: &'a Graph, i: impl Iterator<Item = usize>) -> FxHashMap<usize, &'a Node> {
    i.map(|n| (n, g.get_local_node(Local::from_usize(n))))
        .collect()
}

fn get_ids(g: &Graph, i: impl Iterator<Item = usize>) -> FxHashMap<usize, NodeId> {
    i.map(|n| (n, g.get_local_id(Local::from_usize(n))))
        .collect()
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
        |g, _, _| {
            let n = get_nodes(&g, 1..=3);
            let i = get_ids(&g, 1..=3);
            assert_eq!(n[&2].as_ptr(), &AbsLoc::new_root(i[&1]));
            assert_eq!(n[&3].as_ptr(), &AbsLoc::new_root(i[&1]));

            assert_eq!(g.get_local_as_int(Local::from_usize(1)), Some(0));
        },
    );
}

#[test]
fn test_eq() {
    // _1 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _2 = _1
    // _4 = &mut _2
    // _3 = &raw mut (*_4)
    analyze_fn(
        "
        let mut x: *mut libc::c_int = 0 as *mut libc::c_int;
        let mut y: *mut libc::c_int = x;
        let mut z: *mut *mut libc::c_int = &mut y;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=4);
            let i = get_ids(&g, 1..=4);
            assert_eq!(n[&1].as_ptr(), n[&2].as_ptr());
            assert_eq!(n[&3].as_ptr(), &AbsLoc::new_root(i[&2]));
            assert_eq!(n[&4].as_ptr(), &AbsLoc::new_root(i[&2]));
        },
    );
}

#[test]
fn test_eq_deref() {
    // _1 = const 0_i32
    // _3 = &mut _1
    // _2 = &raw mut (*_3)
    // _4 = (*_2)
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = &mut x;
        let mut z: libc::c_int = *y;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=4);
            let i = get_ids(&g, 1..=4);
            assert_eq!(n[&1].as_ptr(), n[&4].as_ptr());
            assert_eq!(n[&2].as_ptr(), &AbsLoc::new_root(i[&1]));
            assert_eq!(n[&3].as_ptr(), &AbsLoc::new_root(i[&1]));

            assert_eq!(g.get_local_as_int(Local::from_usize(1)), Some(0));
        },
    );
}

#[test]
fn test_deref_eq() {
    // _1 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _2 = const 0_i32
    // (*_1) = _2
    analyze_fn(
        "
        let mut x: *mut libc::c_int = 0 as *mut libc::c_int;
        let mut y: libc::c_int = 0 as libc::c_int;
        *x = y;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=2);
            let dn1 = g.obj_at_location(n[&1].as_ptr()).unwrap();
            assert_eq!(dn1.as_ptr(), n[&2].as_ptr());

            assert_eq!(g.get_local_as_int(Local::from_usize(2)), Some(0));
        },
    );
}

#[test]
fn test_eq_struct() {
    // _1 = s { x: const 0_i32, y: const 1_i32 }
    // _2 = copy (_1.0: i32)
    // _3 = copy (_1.1: i32)
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
        let mut x: s = {
            let mut init = s {
                x: 0 as libc::c_int,
                y: 1 as libc::c_int,
            };
            init
        };
        let mut y: s = x;
        let mut z: libc::c_int = y.x;
        let mut w: libc::c_int = y.y;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=3);
            assert_eq!(n[&1].field(0).as_ptr(), n[&2].as_ptr());
            assert_eq!(n[&1].field(1).as_ptr(), n[&3].as_ptr());
        },
    );
}

#[test]
fn test_eq_struct_2() {
    // _2 = s { x: const 0_i32, y: const 1_i32 }
    // _3 = s { x: const 2_i32, y: const 3_i32 }
    // _1 = t { x: copy _2, y: copy _3 }
    // _4 = copy (_1.0: s)
    // _5 = copy (_1.1: s)
    // _6 = copy (_4.0: i32)
    // _7 = copy (_5.1: i32)
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
            pub y: libc::c_int,
        }
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct t {
            pub x: s,
            pub y: s,
        }
        ",
        "",
        "
        let mut x: t = {
            let mut init = t {
                x: {
                    let mut init = s {
                        x: 0 as libc::c_int,
                        y: 1 as libc::c_int,
                    };
                    init
                },
                y: {
                    let mut init = s {
                        x: 2 as libc::c_int,
                        y: 3 as libc::c_int,
                    };
                    init
                },
            };
            init
        };
        let mut y: s = x.x;
        let mut z: s = x.y;
        let mut w: libc::c_int = y.x;
        let mut v: libc::c_int = z.y;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=7);
            assert_eq!(g.get_absloc_as_int(n[&2].field(0).as_ptr()), Some(0));
            assert_eq!(g.get_absloc_as_int(n[&2].field(1).as_ptr()), Some(1));

            assert_eq!(g.get_absloc_as_int(n[&5].field(0).as_ptr()), Some(2));
            assert_eq!(g.get_absloc_as_int(n[&5].field(1).as_ptr()), Some(3));

            assert_eq!(
                g.get_absloc_as_int(n[&1].field(0).field(0).as_ptr()),
                Some(0)
            );
            assert_eq!(
                g.get_absloc_as_int(n[&1].field(0).field(1).as_ptr()),
                Some(1)
            );
            assert_eq!(
                g.get_absloc_as_int(n[&1].field(1).field(0).as_ptr()),
                Some(2)
            );
            assert_eq!(
                g.get_absloc_as_int(n[&1].field(1).field(1).as_ptr()),
                Some(3)
            );

            assert_eq!(g.get_absloc_as_int(n[&4].field(0).as_ptr()), Some(0));
            assert_eq!(g.get_absloc_as_int(n[&4].field(1).as_ptr()), Some(1));

            assert_eq!(g.get_absloc_as_int(n[&5].field(0).as_ptr()), Some(2));
            assert_eq!(g.get_absloc_as_int(n[&5].field(1).as_ptr()), Some(3));

            assert_eq!(g.get_local_as_int(Local::from_usize(6)), Some(0));
            assert_eq!(g.get_local_as_int(Local::from_usize(7)), Some(3));
        },
    );
}

#[test]
fn test_eq_ref_struct() {
    // _2 = s { x: const 0_i32, y: const 2_i32 }
    // _1 = copy _2
    // _4 = &mut (_1.0: i32)
    // _3 = &raw mut (*_4)
    // (*_3) = const 1_i32
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
        let mut x: s = {
            let mut init = s {
                x: 0 as libc::c_int,
                y: 2 as libc::c_int,
            };
            init
        };
        let mut y: *mut libc::c_int = &mut x.x;
        *y = 1 as libc::c_int;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=4);
            let i = get_ids(&g, 1..=4);

            assert_eq!(g.get_absloc_as_int(n[&2].field(0).as_ptr()), Some(0));

            assert_eq!(g.get_absloc_as_int(n[&1].field(1).as_ptr()), Some(2));
            assert_eq!(g.get_absloc_as_int(n[&2].field(1).as_ptr()), Some(2));

            assert_eq!(g.get_absloc_as_int(n[&1].field(0).as_ptr()), Some(1));

            assert_eq!(
                n[&3].as_ptr(),
                &AbsLoc::new(i[&1], vec![AccElem::Field(FieldIdx::from_u32(0), false)])
            );
            assert_eq!(
                n[&4].as_ptr(),
                &AbsLoc::new(i[&1], vec![AccElem::Field(FieldIdx::from_u32(0), false)])
            );
        },
    );
}

#[test]
fn test_eq_deref_struct() {
    // _2 = s { x: const 1_i32, y: const 2_i32 }
    // _1 = copy _2
    // _4 = &mut _1
    // _3 = &raw mut (*_4)
    // _5 = copy ((*_3).0: i32)
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
        let mut x: s = {
            let mut init = s {
                x: 1 as libc::c_int,
                y: 2 as libc::c_int,
            };
            init
        };
        let mut y: *mut s = &mut x;
        let mut z: libc::c_int = (*y).x;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=5);
            let i = get_ids(&g, 1..=5);

            assert_eq!(g.get_absloc_as_int(n[&1].field(0).as_ptr()), Some(1));
            assert_eq!(g.get_absloc_as_int(n[&2].field(0).as_ptr()), Some(1));
            assert_eq!(g.get_local_as_int(Local::from_usize(5)), Some(1));

            assert_eq!(g.get_absloc_as_int(n[&1].field(1).as_ptr()), Some(2));
            assert_eq!(g.get_absloc_as_int(n[&2].field(1).as_ptr()), Some(2));

            assert_eq!(n[&3].as_ptr(), &AbsLoc::new_root(i[&1]));
            assert_eq!(n[&4].as_ptr(), &AbsLoc::new_root(i[&1]));
        },
    );
}

#[test]
fn test_deref_struct_eq() {
    // _2 = s { x: const 0_i32, y: const 2_i32 }
    // _1 = copy _2
    // _4 = &mut _1
    // _3 = &raw mut (*_4)
    // ((*_3).0: i32) = const 1_i32
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
        let mut x: s = {
            let mut init = s {
                x: 0 as libc::c_int,
                y: 2 as libc::c_int,
            };
            init
        };
        let mut y: *mut s = &mut x;
        (*y).x = 1 as libc::c_int;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=4);
            let i = get_ids(&g, 1..=4);

            assert_eq!(g.get_absloc_as_int(n[&2].field(0).as_ptr()), Some(0));

            assert_eq!(g.get_absloc_as_int(n[&1].field(1).as_ptr()), Some(2));
            assert_eq!(g.get_absloc_as_int(n[&2].field(1).as_ptr()), Some(2));

            assert_eq!(g.get_absloc_as_int(n[&1].field(0).as_ptr()), Some(1));

            assert_eq!(n[&3].as_ptr(), &AbsLoc::new_root(i[&1]));
            assert_eq!(n[&4].as_ptr(), &AbsLoc::new_root(i[&1]));
        },
    );
}

#[test]
fn test_eq_ref_deref() {
    // _2 = s { x: const 0_i32, y: const 2_i32 }
    // _1 = copy _2
    // _4 = &mut _1
    // _3 = &raw mut (*_4)
    // _6 = &mut ((*_3).0: i32)
    // _5 = &raw mut (*_6)
    // (*_5) = const 1_i32
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
        let mut x: s = {
            let mut init = s {
                x: 0 as libc::c_int,
                y: 2 as libc::c_int,
            };
            init
        };
        let mut y: *mut s = &mut x;
        let mut z: *mut libc::c_int = &mut (*y).x;
        *z = 1 as libc::c_int;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=6);
            let i = get_ids(&g, 1..=6);
            println!("{:?}", n);
            println!("{:?}", i);

            assert_eq!(g.get_absloc_as_int(n[&2].field(0).as_ptr()), Some(0));

            assert_eq!(g.get_absloc_as_int(n[&1].field(1).as_ptr()), Some(2));
            assert_eq!(g.get_absloc_as_int(n[&2].field(1).as_ptr()), Some(2));

            assert_eq!(g.get_absloc_as_int(n[&1].field(0).as_ptr()), Some(1));

            assert_eq!(n[&3].as_ptr(), &AbsLoc::new_root(i[&1]));
            assert_eq!(n[&4].as_ptr(), &AbsLoc::new_root(i[&1]));

            assert_eq!(
                n[&5].as_ptr(),
                &AbsLoc::new(i[&1], vec![AccElem::Field(FieldIdx::from_u32(0), false)])
            );
            assert_eq!(
                n[&6].as_ptr(),
                &AbsLoc::new(i[&1], vec![AccElem::Field(FieldIdx::from_u32(0), false)])
            );
        },
    );
}

#[test]
fn test_eq_union_first() {
    // _1 = u { x: const 0_i32 }
    // _2 = copy (_1.0: i32)
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub union u {
            pub x: libc::c_int,
            pub y: libc::c_int,
        }
        ",
        "",
        "
        let mut x: u = u { x: 0 as libc::c_int };
        let mut y: libc::c_int = x.x;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=2);
            let Obj::Struct(fs, is_union) = &n[&1].obj else { unreachable!() };
            assert!(is_union);
            assert_eq!(fs.len(), 1);
            assert_eq!(
                g.get_absloc_as_int(fs.get(&FieldIdx::from_u32(0)).unwrap().as_ptr()),
                Some(0)
            );
            assert_eq!(
                fs.get(&FieldIdx::from_u32(0)).unwrap().as_ptr(),
                n[&2].as_ptr()
            );
            assert_eq!(fs.get(&FieldIdx::from_u32(1)), None);
        },
    );
}

#[test]
fn test_eq_union_second() {
    // _2 = const 0_i32
    // _1 = u { x: move _2 }
    // _3 = copy (_1.1: i32)
    // _5 = &mut _3
    // _4 = &raw mut (*_5)
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub union u {
            pub x: libc::c_int,
            pub y: libc::c_int,
        }
        ",
        "",
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: u = u { y: x };
        let mut z: libc::c_int = y.y;
        let mut w: *mut libc::c_int = &mut z;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=3);
            let Obj::Struct(fs, is_union) = &n[&1].obj else { unreachable!() };
            assert!(is_union);
            assert_eq!(fs.len(), 1);
            assert_eq!(fs.get(&FieldIdx::from_u32(0)), None);
            assert_eq!(
                fs.get(&FieldIdx::from_u32(1)).unwrap().as_ptr(),
                n[&2].as_ptr()
            );
            assert_eq!(
                fs.get(&FieldIdx::from_u32(1)).unwrap().as_ptr(),
                n[&3].as_ptr()
            );
        },
    );
}

#[test]
fn test_union_field_eq() {
    // _1 = u { x: const 0_i32 }
    // (_1.1: i32) = const 1_i32
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub union u {
            pub x: libc::c_int,
            pub y: libc::c_int,
        }
        ",
        "",
        "
        let mut x: u = u { x: 0 as libc::c_int };
        x.y = 1 as libc::c_int;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=1);
            let Obj::Struct(fs, is_union) = &n[&1].obj else { unreachable!() };
            assert!(is_union);
            assert_eq!(fs.len(), 1);
            assert_eq!(fs.get(&FieldIdx::from_u32(0)), None);
            assert_eq!(
                g.get_absloc_as_int(fs.get(&FieldIdx::from_u32(1)).unwrap().as_ptr()),
                Some(1)
            );
        },
    );
}

#[test]
fn test_union_eq_first() {
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
            pub y: libc::c_int,
        }
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub union u {
            pub x: s,
            pub y: s,
        }
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct t {
            pub x: libc::c_int,
            pub y: u,
        }
        ",
        "",
        "
        let mut x: t = t {
            x: 0,
            y: u { x: s { x: 0, y: 0 } },
        };
        let mut y: t = x;
        let mut z: *mut t = &mut y;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=4);
            let Obj::Struct(fs, is_union) = n[&4].field(1) else { unreachable!() };
            assert!(is_union);
            assert_eq!(fs.len(), 1);
            assert_eq!(
                n[&4].field(1).field(0).field(0).as_ptr(),
                n[&1].field(1).field(0).field(0).as_ptr()
            );
            assert_eq!(
                n[&4].field(1).field(0).field(1).as_ptr(),
                n[&1].field(1).field(0).field(1).as_ptr()
            );
        },
    );
}

#[test]
fn test_union_eq_second() {
    // _3 = s { x: const 0_i32, y: const 0_i32 }
    // _2 = u { x: copy _3 }
    // _1 = t { x: const 0_i32, y: move _2 }
    // _4 = copy _1
    // _6 = &mut _4
    // _5 = &raw mut (*_6)
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
            pub y: libc::c_int,
        }
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub union u {
            pub x: s,
            pub y: s,
        }
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct t {
            pub x: libc::c_int,
            pub y: u,
        }
        ",
        "",
        "
        let mut x: t = {
            let mut init = t {
                x: 0 as libc::c_int,
                y: u {
                    y: {
                        let mut init = s {
                            x: 0 as libc::c_int,
                            y: 0 as libc::c_int,
                        };
                        init
                    },
                },
            };
            init
        };
        let mut y: t = x;
        let mut z: *mut t = &mut y;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=6);
            let Obj::Struct(fs, is_union) = n[&4].field(1) else { unreachable!() };
            assert!(is_union);
            assert_eq!(fs.len(), 1);
            assert_eq!(
                n[&4].field(1).field(1).field(0).as_ptr(),
                n[&1].field(1).field(1).field(0).as_ptr()
            );
            assert_eq!(
                n[&4].field(1).field(1).field(1).as_ptr(),
                n[&1].field(1).field(1).field(1).as_ptr()
            );
        },
    );
}

#[test]
fn test_eq_array() {
    // _1 = [const 0_i32; 2]
    // _4 = const 0_i32
    // _3 = move _4 as usize (IntToInt)
    // _5 = const 2_usize
    // _6 = Lt(_3, _5)
    // _2 = _1[_3]
    // _9 = const 1_i32
    // _8 = move _9 as usize (IntToInt)
    // _10 = const 2_usize
    // _11 = Lt(_8, _10)
    // _7 = _1[_8]

    // bb0:
    //     _1 = [const 0_i32; 2]
    //     _3 = const 0_i32 as usize (IntToInt)
    //     _4 = Lt(copy _3, const 2_usize)
    // bb1:
    //     _2 = copy _1[_3]
    //     _6 = const 1_i32 as usize (IntToInt)
    //     _7 = Lt(copy _6, const 2_usize)
    // bb2:
    //     _5 = copy _1[_6]
    analyze_fn(
        "
        let mut x: [libc::c_int; 2] = [0; 2];
        let mut y: libc::c_int = x[0 as libc::c_int as usize];
        let mut z: libc::c_int = x[1 as libc::c_int as usize];
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=7);
            assert_eq!(n[&1].index(0).as_ptr(), n[&2].as_ptr());
            assert_eq!(n[&1].index(1).as_ptr(), n[&2].as_ptr());
            assert_eq!(n[&3].as_ptr(), n[&2].as_ptr());
            assert_eq!(n[&5].as_ptr(), n[&2].as_ptr());
            assert_eq!(n[&6].as_ptr(), n[&4].as_ptr());
            assert_eq!(n[&7].as_ptr(), n[&4].as_ptr());

            assert_eq!(g.get_local_as_int(Local::from_usize(2)), Some(0));
            assert_eq!(g.get_local_as_int(Local::from_usize(4)), Some(1));
        },
    );
}

#[test]
fn test_eq_array_symbolic() {
    // bb0:
    //     _2 = [const 0_i32]
    //     _3 = copy _1 as usize (IntToInt)
    //     _4 = Lt(copy _3, const 1_usize)
    // bb1:
    //     _2[_3] = const 1_i32
    analyze_fn_with(
        "",
        "mut x: libc::c_int",
        "
        let mut y: [libc::c_int; 1] = [0; 1];
        y[x as usize] = 1 as libc::c_int;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=4);
            assert_eq!(n[&1].as_ptr(), n[&3].as_ptr());
            assert_eq!(
                g.get_absloc_as_int(
                    n[&2]
                        .symbolic(&[Local::from_usize(1), Local::from_usize(3)])
                        .unwrap()
                        .as_ptr()
                ),
                Some(1)
            );
            assert_eq!(g.get_local_as_int(Local::from_usize(4)), None);
        },
    );
}

#[test]
fn test_eq_array_symbolic_struct() {
    // _2 = ((*_1).0: i32)
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
            pub y: libc::c_int,
        }
        ",
        "mut x: *mut s",
        "
        let mut y: libc::c_int = (*x).x;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=2);
            let dn1 = g.obj_at_location(n[&1].as_ptr()).unwrap();
            assert_eq!(dn1.field(0).as_ptr(), n[&2].as_ptr());
        },
    );
}

#[test]
fn test_eq_array_symbolic_invalidated() {
    // bb0:
    //     _2 = [const 0_i32]
    //     _4 = copy _1
    //     _3 = move _4 as usize (IntToInt)
    //     _5 = Lt(copy _3, const 1_usize)
    // bb1:
    //     _2[_3] = const 1_i32
    //     _1 = const 2_i32
    analyze_fn_with(
        "",
        "mut x: libc::c_int",
        "
        let mut y: [libc::c_int; 1] = [0; 1];
        y[x as usize] = 1 as libc::c_int;
        x = 2 as libc::c_int;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=5);
            assert_eq!(
                g.get_absloc_as_int(
                    n[&2]
                        .symbolic(&[Local::from_usize(3), Local::from_usize(4)])
                        .unwrap()
                        .as_ptr()
                ),
                Some(1)
            );
            assert_eq!(n[&3].as_ptr(), n[&4].as_ptr());

            assert_eq!(g.get_local_as_int(Local::from_usize(1)), Some(2));
            assert_eq!(g.get_local_as_int(Local::from_usize(3)), None);
            assert_eq!(g.get_local_as_int(Local::from_usize(5)), None);
        },
    );
}

#[test]
fn test_join_int() {
    // _2 = const 0_i32
    // _3 = const 0_i32
    // switchInt(move _1) -> [0: bb2, otherwise: bb1]
    // _4 = const 1_i32
    // _2 = move _4
    // _5 = const 1_i32
    // _3 = move _5
    // goto -> bb2
    analyze_fn_with(
        "",
        "mut x: libc::c_int",
        "
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut z: libc::c_int = 0 as libc::c_int;
        if x != 0 {
            y = 1 as libc::c_int;
            z = 1 as libc::c_int;
        }
        ",
        |g, _, _| {
            let n = get_nodes(&g, 2..=3);
            assert_eq!(n[&2].as_ptr(), n[&3].as_ptr());
            assert_eq!(g.get_local_as_int(Local::from_usize(2)), None);
        },
    );
}

#[test]
fn test_filter() {
    // _2 = const 1_i32
    // _3 = const 2_i32
    // _4 = const 3_i32
    // switchInt(copy _1) -> [1: bb3, 2: bb2, otherwise: bb1]
    // _4 = copy _1
    // goto -> bb4
    // _3 = copy _1
    // goto -> bb4
    // _2 = copy _1
    // goto -> bb4
    analyze_fn_with(
        "",
        "mut x: libc::c_int",
        "
        let mut y: libc::c_int = 1 as libc::c_int;
        let mut z: libc::c_int = 2 as libc::c_int;
        let mut w: libc::c_int = 3 as libc::c_int;
        match x {
            1 => y = x,
            2 => z = x,
            _ => w = x,
        };
        ",
        |g, _, _| {
            assert_eq!(g.get_local_as_int(Local::from_usize(2)), Some(1));
            assert_eq!(g.get_local_as_int(Local::from_usize(3)), Some(2));
            assert_eq!(g.get_local_as_int(Local::from_usize(4)), None);
        },
    );
}

#[test]
fn test_filter_if_eq() {
    // _2 = const 0_i32
    // _4 = const 0_i32
    // _3 = Eq(_1, move _4)
    // switchInt(move _3) -> [0: bb2, otherwise: bb1]
    // _2 = _1
    analyze_fn_with(
        "",
        "mut x: libc::c_int",
        "
        let mut y: libc::c_int = 0 as libc::c_int;
        if x == 0 as libc::c_int {
            y = x;
        }
        ",
        |g, _, _| {
            assert_eq!(g.get_local_as_int(Local::from_usize(2)), Some(0));
        },
    );
}

#[test]
fn test_filter_if_ne() {
    // _2 = const 1_i32
    // _4 = const 0_i32
    // _3 = Ne(_1, move _4)
    // switchInt(move _3) -> [0: bb2, otherwise: bb1]
    // _5 = const 0_i32
    // _2 = move _5
    // _2 = _1
    analyze_fn_with(
        "",
        "mut x: libc::c_int",
        "
        let mut y: libc::c_int = 1 as libc::c_int;
        if x != 0 as libc::c_int {
            y = 0 as libc::c_int;
        } else {
            y = x;
        };
        ",
        |g, _, _| {
            assert_eq!(g.get_local_as_int(Local::from_usize(2)), Some(0));
        },
    );
}

#[test]
fn test_filter_twice() {
    analyze_fn_with(
        "",
        "mut x: libc::c_int",
        "
        let mut y: libc::c_int = 0 as libc::c_int;
        if x == 0 as libc::c_int || x == 1 as libc::c_int {
            if x == 1 as libc::c_int {
                y = 0 as libc::c_int;
            } else {
                y = x;
            }
        }
        ",
        |g, _, _| {
            assert_eq!(g.get_local_as_int(Local::from_usize(2)), Some(0));
        },
    );
}

#[test]
fn test_join_same() {
    // bb0:
    //     _2 = const 0_i32
    //     _4 = &mut _2
    //     _3 = &raw mut (*_4)
    //     switchInt(copy _1) -> [0: bb2, otherwise: bb1]
    // bb1:
    //     _3 = const 0_usize as *mut i32 (PointerWithExposedProvenance)
    //     goto -> bb2
    // bb2:
    analyze_fn_with(
        "",
        "mut x: libc::c_int",
        "
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut z: libc::c_int = y;
        let mut w: *mut libc::c_int = &mut z;
        if x != 0 {
            w = 0 as *mut libc::c_int;
        }
        ",
        |g, _, _| {
            let n = get_nodes(&g, 3..=3);
            assert_eq!(n[&3].obj, Obj::Top);
        },
    );
}

#[test]
fn test_join_diff() {
    // _2 = const 0_i32
    // _3 = _2
    // _4 = _2
    // _6 = &mut _3
    // _5 = &raw mut (*_6)
    // switchInt(move _1) -> [0: bb2, otherwise: bb1]
    // _7 = const 1_i32
    // _4 = move _7
    // _9 = &mut _4
    // _8 = &raw mut (*_9)
    // _5 = move _8
    // goto -> bb2
    analyze_fn_with(
        "",
        "mut x: libc::c_int",
        "
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut z: libc::c_int = y;
        let mut w: libc::c_int = y;
        let mut v: *mut libc::c_int = &mut z;
        if x != 0 {
            w = 1 as libc::c_int;
            v = &mut w;
        }
        ",
        |g, _, _| {
            let n = get_nodes(&g, 2..=4);
            assert_eq!(n[&2].as_ptr(), n[&3].as_ptr());
            assert_ne!(n[&2].as_ptr(), n[&4].as_ptr());
        },
    );
}

#[test]
fn test_join_loop() {
    // _1 = const 0_i32
    // _2 = const 0_i32
    // goto -> bb1
    // _4 = _1
    // _5 = const 10_i32
    // _3 = Lt(move _4, move _5)
    // switchInt(move _3) -> [0: bb3, otherwise: bb2]
    // _6 = const 1_i32
    // _1 = Add(_1, move _6)
    // _7 = _1
    // _2 = move _7
    // goto -> bb1
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: libc::c_int = 0 as libc::c_int;
        while x < 10 as libc::c_int {
            x += 1 as libc::c_int;
            y = x;
        }
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=2);
            assert_eq!(n[&1].as_ptr(), n[&2].as_ptr());
            assert_eq!(g.get_local_as_int(Local::from_usize(1)), None);
        },
    );
}

#[test]
fn test_eq_invalidate() {
    // _2 = const 0_i32
    // _3 = const 0_i32
    // switchInt(move _1) -> [0: bb2, otherwise: bb1]
    // _5 = &mut _2
    // _4 = &raw mut (*_5)
    // goto -> bb3
    // _6 = &mut _3
    // _4 = &raw mut (*_6)
    // goto -> bb3
    // _7 = const 1_i32
    // _2 = move _7
    analyze_fn_with(
        "",
        "mut x: libc::c_int",
        "
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut z: libc::c_int = 0 as libc::c_int;
        let mut w: *mut libc::c_int = if x != 0 { &mut y } else { &mut z };
        y = 1 as libc::c_int;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 4..=4);
            let dn4 = g.obj_at_location(n[&4].as_ptr()).unwrap();
            assert_eq!(dn4, &Obj::Top);
            assert_eq!(g.get_local_as_int(Local::from_usize(2)), Some(1));
            assert_eq!(g.get_local_as_int(Local::from_usize(3)), Some(0));
        },
    );
}

#[test]
fn test_struct_eq_invalidate() {
    // bb0:
    //     _3 = s { x: const 1_i32, y: const 2_i32 }
    //     _2 = copy _3
    //     _4 = copy _2
    //     switchInt(copy _1) -> [0: bb2, otherwise: bb1]
    // bb1:
    //     _6 = &mut _2
    //     _5 = &raw mut (*_6)
    //     goto -> bb3
    // bb2:
    //     _7 = &mut _4
    //     _5 = &raw mut (*_7)
    //     goto -> bb3
    // bb3:
    //     (_4.0: i32) = const 3_i32
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
            pub y: libc::c_int,
        }
        ",
        "mut x: libc::c_int",
        "
        let mut y: s = {
            let mut init = s {
                x: 1 as libc::c_int,
                y: 2 as libc::c_int,
            };
            init
        };
        let mut z: s = y;
        let mut w: *mut s = if x != 0 { &mut y } else { &mut z };
        z.x = 3 as libc::c_int;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 2..=5);
            assert_eq!(g.get_absloc_as_int(n[&2].field(0).as_ptr()), Some(1));
            assert_eq!(g.get_absloc_as_int(n[&2].field(1).as_ptr()), Some(2));
            assert_ne!(n[&2].field(0).as_ptr(), n[&4].field(0).as_ptr());
            assert_eq!(n[&2].field(1).as_ptr(), n[&4].field(1).as_ptr());
            let dn5 = g.obj_at_location(n[&5].as_ptr()).unwrap();
            assert_eq!(dn5.field(0), &Obj::Top);
            assert_eq!(n[&2].field(1).as_ptr(), dn5.field(1).as_ptr());
        },
    );
}

#[test]
fn test_struct_eq_field_invalidate() {
    // bb0:
    //     _3 = s { x: const 1_i32, y: const 1_i32 }
    //     _2 = copy _3
    //     _4 = copy _2
    //     switchInt(copy _1) -> [0: bb2, otherwise: bb1]
    // bb1:
    //     _6 = &mut (_2.0: i32)
    //     _5 = &raw mut (*_6)
    //     goto -> bb3
    // bb2:
    //     _7 = &mut (_4.0: i32)
    //     _5 = &raw mut (*_7)
    //     goto -> bb3
    // bb3:
    //     switchInt(copy _1) -> [0: bb5, otherwise: bb4]
    // bb4:
    //     _9 = &mut (_2.1: i32)
    //     _8 = &raw mut (*_9)
    //     goto -> bb6
    // bb5:
    //     _10 = &mut (_4.1: i32)
    //     _8 = &raw mut (*_10)
    //     goto -> bb6
    // bb6:
    //     (_4.0: i32) = const 2_i32
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
            pub y: libc::c_int,
        }
        ",
        "mut x: libc::c_int",
        "
        let mut y: s = {
            let mut init = s {
                x: 1 as libc::c_int,
                y: 1 as libc::c_int,
            };
            init
        };
        let mut z: s = y;
        let mut w: *mut libc::c_int = if x != 0 { &mut y.x } else { &mut z.x };
        let mut v: *mut libc::c_int = if x != 0 { &mut y.y } else { &mut z.y };
        z.x = 2 as libc::c_int;
        ",
        |g, _, _| {
            let n = get_nodes(&g, (1..=5).chain(8..=8));
            assert_eq!(n[&2].field(0).as_ptr(), n[&2].field(1).as_ptr());
            assert_eq!(n[&2].field(0).as_ptr(), n[&3].field(0).as_ptr());
            assert_eq!(n[&2].field(0).as_ptr(), n[&3].field(1).as_ptr());
            assert_ne!(n[&2].field(0).as_ptr(), n[&4].field(0).as_ptr());
            assert_eq!(n[&2].field(0).as_ptr(), n[&4].field(1).as_ptr());
            let dn5 = g.obj_at_location(n[&5].as_ptr()).unwrap();
            assert_eq!(dn5, &Obj::Top);
            let dn8 = g.obj_at_location(n[&8].as_ptr()).unwrap();
            assert_eq!(dn8.as_ptr(), n[&2].field(0).as_ptr());
        },
    );
}

#[test]
fn test_deref_eq_invalidate() {
    // _2 = const 0_i32
    // _3 = const 0_i32
    // switchInt(move _1) -> [0: bb2, otherwise: bb1]
    // _5 = &mut _2
    // _4 = &raw mut (*_5)
    // goto -> bb3
    // _6 = &mut _3
    // _4 = &raw mut (*_6)
    // goto -> bb3
    // _7 = const 1_i32
    // (*_4) = move _7
    analyze_fn_with(
        "",
        "mut x: libc::c_int",
        "
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut z: libc::c_int = 0 as libc::c_int;
        let mut w: *mut libc::c_int = if x != 0 { &mut y } else { &mut z };
        *w = 1 as libc::c_int;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 2..=3);
            assert_eq!(n[&2].obj, Obj::Top);
            assert_eq!(n[&3].obj, Obj::Top);
        },
    );
}

#[test]
fn test_deref_struct_eq_invalidate() {
    // bb0:
    //     _3 = s { x: const 1_i32, y: const 2_i32 }
    //     _2 = copy _3
    //     _4 = copy _2
    //     switchInt(copy _1) -> [0: bb2, otherwise: bb1]
    // bb1:
    //     _6 = &mut _2
    //     _5 = &raw mut (*_6)
    //     goto -> bb3
    // bb2:
    //     _7 = &mut _4
    //     _5 = &raw mut (*_7)
    //     goto -> bb3
    // bb3:
    //     _8 = const 3_i32
    //     ((*_5).0: i32) = move _8
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
            pub y: libc::c_int,
        }
        ",
        "mut x: libc::c_int",
        "
        let mut y: s = {
            let mut init = s {
                x: 1 as libc::c_int,
                y: 2 as libc::c_int,
            };
            init
        };
        let mut z: s = y;
        let mut w: libc::c_int = 3 as libc::c_int;
        let mut v: *mut s = if x != 0 { &mut y } else { &mut z };
        (*v).x = w;
        ",
        |g, _, _| {
            let n = get_nodes(&g, (2..=5).chain(8..=8));
            assert_eq!(n[&2].field(0), &Obj::Top);
            assert_eq!(g.get_absloc_as_int(n[&3].field(0).as_ptr()), Some(1));
            assert_eq!(n[&4].field(0), &Obj::Top);
            assert_eq!(n[&2].field(1).as_ptr(), n[&3].field(1).as_ptr());
            assert_eq!(n[&2].field(1).as_ptr(), n[&4].field(1).as_ptr());
            let dn8 = g.obj_at_location(n[&5].as_ptr()).unwrap();
            assert_eq!(g.get_absloc_as_int(dn8.field(0).as_ptr()), Some(3));
            assert_eq!(dn8.field(1).as_ptr(), n[&2].field(1).as_ptr());
        },
    );
}

#[test]
fn test_deref_struct_eq_field_invalidate() {
    // bb0:
    //     _3 = s { x: const 1_i32, y: const 2_i32 }
    //     _2 = copy _3
    //     _4 = copy _2
    //     switchInt(copy _1) -> [0: bb2, otherwise: bb1]
    // bb1:
    //     _6 = &mut (_2.0: i32)
    //     _5 = &raw mut (*_6)
    //     goto -> bb3
    // bb2:
    //     _7 = &mut (_4.1: i32)
    //     _5 = &raw mut (*_7)
    //     goto -> bb3
    // bb3:
    //     _8 = const 3_i32
    //     (*_5) = move _8
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
            pub y: libc::c_int,
        }
        ",
        "mut x: libc::c_int",
        "
        let mut y: s = {
            let mut init = s {
                x: 1 as libc::c_int,
                y: 2 as libc::c_int,
            };
            init
        };
        let mut z: s = y;
        let mut w: libc::c_int = 3 as libc::c_int;
        let mut v: *mut libc::c_int = if x != 0 { &mut y.x } else { &mut z.y };
        *v = w;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 2..=5);
            assert_eq!(n[&2].field(0), &Obj::Top);
            assert_eq!(g.get_absloc_as_int(n[&2].field(1).as_ptr()), Some(2));
            assert_eq!(g.get_absloc_as_int(n[&3].field(0).as_ptr()), Some(1));
            assert_eq!(g.get_absloc_as_int(n[&3].field(1).as_ptr()), Some(2));
            assert_eq!(g.get_absloc_as_int(n[&4].field(0).as_ptr()), Some(1));
            assert_eq!(n[&4].field(1), &Obj::Top);
            let dn5 = g.obj_at_location(n[&5].as_ptr()).unwrap();
            assert_eq!(g.get_absloc_as_int(dn5.as_ptr()), Some(3));
        },
    );
}

#[test]
fn test_call_invalidate() {
    // _2 = const 0_i32
    // (*_1) = move _2
    //
    // _1 = const 0_i32
    // _3 = &mut _1
    // _2 = &raw mut (*_3)
    // _4 = foo::f(_2)
    analyze_fn(
        "
        unsafe fn f(mut x: *mut libc::c_int) {
            *x = 0 as libc::c_int;
        }
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = &mut x;
        f(y);
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=3);
            let i = get_ids(&g, 1..=3);
            assert_eq!(n[&2].as_ptr(), &AbsLoc::new_root(i[&1]));
            assert_eq!(n[&3].as_ptr(), &AbsLoc::new_root(i[&1]));

            assert_eq!(g.get_local_as_int(Local::from_usize(1)), None);
        },
    );
}

#[test]
fn test_indirect_call_invalidate() {
    // switchInt(move _1) -> [0: bb2, otherwise: bb1]
    // _3 = foo::f as unsafe fn(*mut i32) (PointerCoercion(ReifyFnPointer))
    // _2 = std::option::Option::<unsafe fn(*mut i32)>::Some(move _3)
    // goto -> bb3
    // _4 = foo::g as unsafe fn(*mut i32) (PointerCoercion(ReifyFnPointer))
    // _2 = std::option::Option::<unsafe fn(*mut i32)>::Some(move _4)
    // goto -> bb3
    // _5 = const 0_i32
    // _7 = &mut _5
    // _6 = &raw mut (*_7)
    // _10 = _2
    // _9 = std::option::Option::<unsafe fn(*mut i32)>::unwrap(move _10)
    // _8 = move _9(_6)
    analyze_fn_with(
        "",
        "mut x: libc::c_int",
        "
        unsafe fn f(mut x: *mut libc::c_int) {
            *x = 0 as libc::c_int;
        }
        unsafe fn g(mut x: *mut libc::c_int) {}
        let mut h: Option::<unsafe fn(*mut libc::c_int) -> ()> = if x != 0 {
            Some(f as unsafe fn(*mut libc::c_int) -> ())
        } else {
            Some(g as unsafe fn(*mut libc::c_int) -> ())
        };
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut z: *mut libc::c_int = &mut y;
        h.unwrap()(z);
        ",
        |g, _, _| {
            let n = get_nodes(&g, 5..=7);
            let i = get_ids(&g, 5..=7);
            assert_eq!(n[&6].as_ptr(), &AbsLoc::new_root(i[&5]));
            assert_eq!(n[&7].as_ptr(), &AbsLoc::new_root(i[&5]));

            assert_eq!(g.get_local_as_int(Local::from_usize(5)), None);
        },
    );
}

#[test]
fn test_memcpy_invalidate() {
    // _1 = const 0_i32
    // _2 = const 0_i32
    // _6 = &mut _1
    // _5 = &raw mut (*_6)
    // _4 = move _5 as *mut libc::c_void (PtrToPtr)
    // _9 = &mut _2
    // _8 = &raw mut (*_9)
    // _7 = move _8 as *const libc::c_void (PtrToPtr)
    // _11 = std::mem::size_of::<i32>()
    // _10 = move _11 as u64 (IntToInt)
    // _3 = foo::memcpy(move _4, move _7, move _10)
    analyze_fn_with(
        "
        extern \"C\" {
            fn memcpy(
                _: *mut libc::c_void,
                _: *const libc::c_void,
                _: libc::c_ulong,
            ) -> *mut libc::c_void;
        }
        ",
        "",
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: libc::c_int = 0 as libc::c_int;
        memcpy(
            &mut x as *mut libc::c_int as *mut libc::c_void,
            &mut y as *mut libc::c_int as *const libc::c_void,
            ::std::mem::size_of::<libc::c_int>() as libc::c_ulong,
        );
        ",
        |g, _, _| {
            assert_eq!(g.get_local_as_int(Local::from_usize(1)), None);
            assert_eq!(g.get_local_as_int(Local::from_usize(2)), Some(0));
        },
    );
}

#[test]
fn test_as_mut_ptr() {
    // bb0:
    //     _1 = [const 0_i32]
    //     _4 = &mut _1
    //     _3 = move _4 as &mut [i32] (PointerCoercion(Unsize, Implicit))
    //     _2 = core::slice::<impl [i32]>::as_mut_ptr(move _3) -> [return: bb1, unwind terminate(abi)]
    // bb1:
    //     (*_2) = const 1_i32
    analyze_fn(
        "
        let mut x: [libc::c_int; 1] = [0; 1];
        let mut y: *mut libc::c_int = x.as_mut_ptr();
        *y = 1 as libc::c_int;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=4);
            assert_eq!(g.get_absloc_as_int(n[&1].index(0).as_ptr()), Some(1));
        },
    );
}

#[test]
fn test_offset_array() {
    // bb0:
    //     _1 = [const 0_i32; 2]
    //     _4 = &mut _1
    //     _3 = move _4 as &mut [i32] (PointerCoercion(Unsize, Implicit))
    //     _2 = core::slice::<impl [i32]>::as_mut_ptr(move _3) -> [return: bb1, unwind terminate(abi)]
    // bb1:
    //     _6 = const 1_i32 as isize (IntToInt)
    //     _5 = std::ptr::mut_ptr::<impl *mut i32>::offset(copy _2, move _6) -> [return: bb2, unwind terminate(abi)]
    // bb2:
    //     (*_5) = const 1_i32
    analyze_fn(
        "
        let mut x: [libc::c_int; 2] = [0; 2];
        let mut y: *mut libc::c_int = x.as_mut_ptr();
        *y.offset(1 as libc::c_int as isize) = 1 as libc::c_int;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=1);
            assert_eq!(g.get_absloc_as_int(n[&1].index(1).as_ptr()), Some(1));
        },
    );
}

#[test]
fn test_offset_array_symbolic() {
    // bb0:
    //     _2 = [const 0_i32]
    //     _5 = &mut _2
    //     _4 = move _5 as &mut [i32] (PointerCoercion(Unsize, Implicit))
    //     _3 = core::slice::<impl [i32]>::as_mut_ptr(move _4) -> [return: bb1, unwind terminate(abi)]
    // bb1:
    //     _7 = copy _1 as isize (IntToInt)
    //     _6 = std::ptr::mut_ptr::<impl *mut i32>::offset(copy _3, move _7) -> [return: bb2, unwind terminate(abi)]
    // bb2:
    //     (*_6) = const 1_i32
    analyze_fn_with(
        "",
        "mut x: libc::c_int",
        "
        let mut y: [libc::c_int; 1] = [0; 1];
        let mut z: *mut libc::c_int = y.as_mut_ptr();
        *z.offset(x as isize) = 1 as libc::c_int;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 2..=2);
            assert_eq!(
                g.get_absloc_as_int(
                    n[&2]
                        .symbolic(&[Local::from_usize(1), Local::from_usize(7)])
                        .unwrap()
                        .as_ptr()
                ),
                Some(1)
            );
        },
    );
}

#[test]
fn test_offset() {
    // _3 = const 1_i32 as isize (IntToInt)
    // _2 = std::ptr::mut_ptr::<impl *mut i32>::offset(copy _1, move _3) -> [return: bb1, unwind terminate(abi)]
    // (*_2) = const 0_i32
    analyze_fn_with(
        "",
        "mut x: *mut libc::c_int",
        "
        *x.offset(1 as libc::c_int as isize) = 0 as libc::c_int;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=3);
            println!("{:?}", g);
            println!("{:?}", n);
            assert_eq!(n[&1].as_ptr().root(), n[&2].as_ptr().root());
            assert_eq!(n[&1].as_ptr().projection()[0], AccElem::num_index(0));
            assert_eq!(n[&2].as_ptr().projection()[0], AccElem::num_index(1));

            let n11 = &g.nodes[n[&2].as_ptr().root()].index(1);
            assert_eq!(g.get_absloc_as_int(n11.as_ptr()), Some(0));
        },
    );
}

#[test]
fn test_offset_twice() {
    // _2 = const 0_usize as *mut s (PointerFromExposedAddress)
    // _5 = _1 as isize (IntToInt)
    // _4 = std::ptr::mut_ptr::<impl *mut s>::offset(_2, move _5)
    // _3 = ((*_4).0: i32)
    // _8 = _1 as isize (IntToInt)
    // _7 = std::ptr::mut_ptr::<impl *mut s>::offset(_2, move _8)
    // _6 = ((*_7).0: i32)
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
        }
        ",
        "mut x: libc::c_int",
        "
        let mut s: *mut s = 0 as *mut s;
        let mut y: libc::c_int = (*s.offset(x as isize)).x;
        let mut z: libc::c_int = (*s.offset(x as isize)).x;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 3..=6);
            assert_eq!(n[&3].as_ptr().root(), n[&6].as_ptr().root());
        },
    );
}

#[test]
fn test_offset_twice_struct() {
    // _3 = const 0_usize as *mut s (PointerFromExposedAddress)
    // _2 = t { s: move _3 }
    // _6 = (_2.0: *mut s)
    // _8 = ((*_1).0: i32)
    // _7 = move _8 as isize (IntToInt)
    // _5 = std::ptr::mut_ptr::<impl *mut s>::offset(move _6, move _7)
    // _4 = ((*_5).0: i32)
    // _11 = (_2.0: *mut s)
    // _13 = ((*_1).0: i32)
    // _12 = move _13 as isize (IntToInt)
    // _10 = std::ptr::mut_ptr::<impl *mut s>::offset(move _11, move _12)
    // _9 = ((*_10).0: i32)
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
        }
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct t {
            pub s: *mut s,
        }
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct r {
            pub x: libc::c_int,
        }
        ",
        "mut r: *mut r",
        "
        let mut t: t = t { s: 0 as *mut s };
        let mut x: libc::c_int = (*(t.s).offset((*r).x as isize)).x;
        let mut y: libc::c_int = (*(t.s).offset((*r).x as isize)).x;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 4..=9);
            assert_eq!(n[&4].as_ptr().root(), n[&9].as_ptr().root());
        },
    );
}

#[test]
fn test_offset_switch() {
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
        }
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct t {
            pub s: *mut s,
        }
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct r {
            pub x: libc::c_int,
        }
        ",
        "mut r: *mut r",
        "
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut t: t = t { s: 0 as *mut s };
        let mut x: libc::c_int = (*(t.s).offset((*r).x as isize)).x;
        match x {
            0 => {
                y = (*(t.s).offset((*r).x as isize)).x;
            }
            1 => {
                y = (*(t.s).offset((*r).x as isize)).x - 1 as libc::c_int;
            }
            _ => {}
        };
        ",
        |g, _, _| {
            assert_eq!(g.get_local_as_int(Local::from_usize(2)), Some(0));
        },
    );
}

#[test]
fn test_offset_twice_2() {
    // _3 = const 0_usize as *mut s (PointerFromExposedAddress)
    // _6 = _1 as isize (IntToInt)
    // _5 = std::ptr::mut_ptr::<impl *mut s>::offset(_3, move _6)
    // _4 = ((*_5).0: i32)
    // _9 = _2 as isize (IntToInt)
    // _8 = std::ptr::mut_ptr::<impl *mut s>::offset(_3, move _9)
    // _7 = ((*_8).0: i32)
    // _12 = _1 as isize (IntToInt)
    // _11 = std::ptr::mut_ptr::<impl *mut s>::offset(_3, move _12)
    // _10 = ((*_11).0: i32)
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
        }
        ",
        "mut x: libc::c_int, mut y: libc::c_int",
        "
        let mut s: *mut s = 0 as *mut s;
        let mut a: libc::c_int = (*s.offset(x as isize)).x;
        let mut b: libc::c_int = (*s.offset(y as isize)).x;
        let mut c: libc::c_int = (*s.offset(x as isize)).x;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 4..=10);
            assert_eq!(n[&4].as_ptr().root(), n[&10].as_ptr().root(),);
            assert_ne!(n[&4].as_ptr().root(), n[&7].as_ptr().root(),);
        },
    );
}

#[test]
fn test_write_twice() {
    // bb0:
    //     _3 = [const 0_i32; 2]
    //     _4 = copy _1 as usize (IntToInt)
    //     _5 = Lt(copy _4, const 2_usize)
    // bb1:
    //     _3[_4] = const 0_i32
    //     _6 = copy _2 as usize (IntToInt)
    //     _7 = Lt(copy _6, const 2_usize)
    // bb2:
    //     _3[_6] = const 1_i32
    analyze_fn_with(
        "",
        "mut x: libc::c_int, mut y: libc::c_int",
        "
        let mut z: [libc::c_int; 2] = [0; 2];
        z[x as usize] = 0 as libc::c_int;
        z[y as usize] = 1 as libc::c_int;
        ",
        |g, _, _| {
            let n = get_nodes(&g, [3, 5].into_iter());
            assert_eq!(
                g.get_absloc_as_int(
                    n[&3]
                        .symbolic(&[Local::from_usize(2), Local::from_usize(6)])
                        .unwrap()
                        .as_ptr()
                ),
                Some(1)
            );
            assert_eq!(
                n[&3].symbolic(&[Local::from_usize(1), Local::from_usize(4)]),
                None
            );
        },
    );
}

#[test]
fn test_for_switch() {
    // _2 = const 0_usize as *mut s (PointerFromExposedAddress)
    // _3 = const 0_i32
    // goto -> bb1
    // switchInt(_1) -> [0: bb4, otherwise: bb2]
    // switchInt(((*_2).0: i32)) -> [0: bb3, otherwise: bb1]
    // _4 = ((*_2).0: i32)
    // _3 = move _4
    // goto -> bb1
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
        }
        ",
        "b: bool",
        "
        let mut s: *mut s = 0 as *mut s;
        let mut x: libc::c_int = 0 as libc::c_int;
        while b {
            match (*s).x {
                0 => x = (*s).x,
                _ => {}
            }
        }
        ",
        |g, _, _| {
            assert_eq!(g.get_local_as_int(Local::from_usize(3)), Some(0));
        },
    );
}

#[test]
fn test_loop_offset() {
    // _2 = const 0_i32
    // _3 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _4 = _3
    // goto -> bb1
    // switchInt(_1) -> [0: bb6, otherwise: bb2]
    // switchInt((*_4)) -> [0: bb3, otherwise: bb4]
    // _5 = (*_4)
    // _2 = move _5
    // goto -> bb4
    // _7 = _4
    // _6 = std::ptr::mut_ptr::<impl *mut i32>::offset(move _7, const 1_isize)
    // _4 = move _6
    // goto -> bb1
    analyze_fn_with(
        "",
        "b: bool",
        "
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut w: *mut libc::c_int = 0 as *mut libc::c_int;
        let mut z: *mut libc::c_int = w;
        while b {
            match *z {
                0 => y = *z,
                _ => {}
            }
            z = z.offset(1);
        }
        ",
        |g, _, _| {
            assert_eq!(g.get_local_as_int(Local::from_usize(2)), Some(0));
        },
    );
}

#[test]
fn test_loop_offset_struct() {
    // _2 = const 0_i32
    // _3 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _4 = _3
    // goto -> bb1
    // switchInt(_1) -> [0: bb6, otherwise: bb2]
    // switchInt((*_4)) -> [0: bb3, otherwise: bb4]
    // _5 = (*_4)
    // _2 = move _5
    // goto -> bb4
    // _7 = _4
    // _6 = std::ptr::mut_ptr::<impl *mut i32>::offset(move _7, const 1_isize)
    // _4 = move _6
    // goto -> bb1
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
        }
        ",
        "b: bool",
        "
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut w: *mut s = 0 as *mut s;
        let mut z: *mut s = w;
        while b {
            match (*z).x {
                0 => y = (*z).x,
                _ => {}
            }
            z = z.offset(1);
        }
        ",
        |g, _, _| {
            assert_eq!(g.get_local_as_int(Local::from_usize(2)), Some(0));
        },
    );
}

#[test]
fn test_bitfield_write() {
    // bb0:
    //     _2 = [const 0_u8]
    //     _3 = [const 0_u8; 3]
    //     _1 = s { x: const 0_i32, y_z: move _2, c2rust_padding: move _3 }
    //     (_1.0: i32) = const 0_i32
    //     _5 = &mut _1
    //     _4 = s::set_y(move _5, const 1_i32) -> [return: bb1, unwind terminate(abi)]
    // bb1:
    //     _7 = &mut _1
    //     _6 = s::set_z(move _7, const 2_i32) -> [return: bb2, unwind terminate(abi)]
    // bb2:
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
        x.x = 0 as libc::c_int;
        x.set_y(1 as libc::c_int);
        x.set_z(2 as libc::c_int);
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=1);
            assert_eq!(g.get_absloc_as_int(n[&1].field(0).as_ptr()), Some(0));
            assert_eq!(g.get_absloc_as_int(n[&1].field(3).as_ptr()), Some(1));
            assert_eq!(g.get_absloc_as_int(n[&1].field(4).as_ptr()), Some(2));
        },
    );
}

#[test]
fn test_bitfield_read() {
    // bb0:
    //     _3 = [const 0_u8]
    //     _4 = [const 0_u8; 3]
    //     _2 = s { x: const 0_i32, y_z: move _3, c2rust_padding: move _4 }
    //     _6 = &mut _2
    //     _5 = s::set_y(move _6, const 1_i32) -> [return: bb1, unwind terminate(abi)]
    // bb1:
    //     _8 = &mut _2
    //     _7 = s::set_z(move _8, const 2_i32) -> [return: bb2, unwind terminate(abi)]
    // bb2:
    //     _1 = copy _2
    //     _9 = copy (_1.0: i32)
    //     _11 = &_1
    //     _10 = s::y(move _11) -> [return: bb3, unwind terminate(abi)]
    // bb3:
    //     _13 = &_1
    //     _12 = s::z(move _13) -> [return: bb4, unwind terminate(abi)]
    // bb4:
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
        let mut x: s = {
            let mut init = s {
                y_z: [0; 1],
                c2rust_padding: [0; 3],
                x: 0 as libc::c_int,
            };
            init.set_y(1 as libc::c_int);
            init.set_z(2 as libc::c_int);
            init
        };
        let mut y: libc::c_int = x.x;
        let mut z: libc::c_int = x.y();
        let mut w: libc::c_int = x.z();
        ",
        |g, _, _| {
            // let n = get_nodes(&g, [1, 2, 5, 8, 11, 12, 13, 15].into_iter());
            let n = get_nodes(&g, [1, 2, 9, 10, 12].into_iter());
            assert_eq!(g.get_absloc_as_int(n[&1].field(0).as_ptr()), Some(0));
            assert_eq!(g.get_absloc_as_int(n[&1].field(3).as_ptr()), Some(1));
            assert_eq!(g.get_absloc_as_int(n[&1].field(4).as_ptr()), Some(2));
            assert_eq!(g.get_absloc_as_int(n[&2].field(0).as_ptr()), Some(0));
            assert_eq!(g.get_absloc_as_int(n[&2].field(3).as_ptr()), Some(1));
            assert_eq!(g.get_absloc_as_int(n[&2].field(4).as_ptr()), Some(2));
            assert_eq!(g.get_local_as_int(Local::from_usize(9)), Some(0));
            assert_eq!(g.get_local_as_int(Local::from_usize(10)), Some(1));
            assert_eq!(g.get_local_as_int(Local::from_usize(12)), Some(2));
        },
    );
}

#[test]
fn test_bitfield_eq_invalidate() {
    // bb0:
    //     _4 = [const 0_u8]
    //     _5 = [const 0_u8; 3]
    //     _3 = s { x: const 0_i32, y_z: move _4, c2rust_padding: move _5 }
    //     _7 = &mut _3
    //     _6 = s::set_y(move _7, const 0_i32) -> [return: bb1, unwind terminate(abi)]
    // bb1:
    //     _9 = &mut _3
    //     _8 = s::set_z(move _9, const 0_i32) -> [return: bb2, unwind terminate(abi)]
    // bb2:
    //     _2 = copy _3
    //     _12 = [const 0_u8]
    //     _13 = [const 0_u8; 3]
    //     _11 = s { x: const 0_i32, y_z: move _12, c2rust_padding: move _13 }
    //     _15 = &mut _11
    //     _14 = s::set_y(move _15, const 0_i32) -> [return: bb3, unwind terminate(abi)]
    // bb3:
    //     _17 = &mut _11
    //     _16 = s::set_z(move _17, const 0_i32) -> [return: bb4, unwind terminate(abi)]
    // bb4:
    //     _10 = copy _11
    //     switchInt(copy _1) -> [0: bb6, otherwise: bb5]
    // bb5:
    //     _19 = &mut _2
    //     _18 = &raw mut (*_19)
    //     goto -> bb7
    // bb6:
    //     _20 = &mut _10
    //     _18 = &raw mut (*_20)
    //     goto -> bb7
    // bb7:
    //     _22 = &mut _2
    //     _21 = s::set_y(move _22, const 1_i32) -> [return: bb8, unwind terminate(abi)]
    // bb8:
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
        "mut x: libc::c_int",
        "
        let mut y: s = {
            let mut init = s {
                y_z: [0; 1],
                c2rust_padding: [0; 3],
                x: 0 as libc::c_int,
            };
            init.set_y(0 as libc::c_int);
            init.set_z(0 as libc::c_int);
            init
        };
        let mut z: s = {
            let mut init = s {
                y_z: [0; 1],
                c2rust_padding: [0; 3],
                x: 0 as libc::c_int,
            };
            init.set_y(0 as libc::c_int);
            init.set_z(0 as libc::c_int);
            init
        };
        let mut w: *mut s = if x != 0 { &mut y } else { &mut z };
        y.set_y(1 as libc::c_int);
        ",
        |g, _, _| {
            let n = get_nodes(&g, [2, 3, 10, 11, 18].into_iter());
            assert_eq!(g.get_absloc_as_int(n[&2].field(0).as_ptr()), Some(0));
            assert_eq!(g.get_absloc_as_int(n[&2].field(3).as_ptr()), Some(1));
            assert_eq!(g.get_absloc_as_int(n[&2].field(4).as_ptr()), Some(0));
            assert_eq!(g.get_absloc_as_int(n[&3].field(0).as_ptr()), Some(0));
            assert_eq!(g.get_absloc_as_int(n[&3].field(3).as_ptr()), Some(0));
            assert_eq!(g.get_absloc_as_int(n[&3].field(4).as_ptr()), Some(0));
            assert_eq!(g.get_absloc_as_int(n[&10].field(0).as_ptr()), Some(0));
            assert_eq!(g.get_absloc_as_int(n[&10].field(3).as_ptr()), Some(0));
            assert_eq!(g.get_absloc_as_int(n[&10].field(4).as_ptr()), Some(0));
            assert_eq!(g.get_absloc_as_int(n[&11].field(0).as_ptr()), Some(0));
            assert_eq!(g.get_absloc_as_int(n[&11].field(3).as_ptr()), Some(0));
            assert_eq!(g.get_absloc_as_int(n[&11].field(4).as_ptr()), Some(0));
            let dn18 = g.obj_at_location(n[&18].as_ptr()).unwrap();
            assert_eq!(g.get_absloc_as_int(dn18.field(0).as_ptr()), Some(0));
            assert_eq!(dn18.field(3), &Obj::Top);
            assert_eq!(g.get_absloc_as_int(dn18.field(4).as_ptr()), Some(0));
        },
    );
}

#[test]
fn test_bitfield_deref_eq_invalidate() {
    // bb0:
    //     _4 = [const 0_u8]
    //     _5 = [const 0_u8; 3]
    //     _3 = s { x: const 0_i32, y_z: move _4, c2rust_padding: move _5 }
    //     _7 = &mut _3
    //     _6 = s::set_y(move _7, const 0_i32) -> [return: bb1, unwind terminate(abi)]
    // bb1:
    //     _9 = &mut _3
    //     _8 = s::set_z(move _9, const 0_i32) -> [return: bb2, unwind terminate(abi)]
    // bb2:
    //     _2 = copy _3
    //     _12 = [const 0_u8]
    //     _13 = [const 0_u8; 3]
    //     _11 = s { x: const 0_i32, y_z: move _12, c2rust_padding: move _13 }
    //     _15 = &mut _11
    //     _14 = s::set_y(move _15, const 0_i32) -> [return: bb3, unwind terminate(abi)]
    // bb3:
    //     _17 = &mut _11
    //     _16 = s::set_z(move _17, const 0_i32) -> [return: bb4, unwind terminate(abi)]
    // bb4:
    //     _10 = copy _11
    //     switchInt(copy _1) -> [0: bb6, otherwise: bb5]
    // bb5:
    //     _19 = &mut _2
    //     _18 = &raw mut (*_19)
    //     goto -> bb7
    // bb6:
    //     _20 = &mut _10
    //     _18 = &raw mut (*_20)
    //     goto -> bb7
    // bb7:
    //     _22 = &mut (*_18)
    //     _21 = s::set_y(move _22, const 1_i32) -> [return: bb8, unwind terminate(abi)]
    // bb8:
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
        "mut x: libc::c_int",
        "
        let mut y: s = {
            let mut init = s {
                y_z: [0; 1],
                c2rust_padding: [0; 3],
                x: 0 as libc::c_int,
            };
            init.set_y(0 as libc::c_int);
            init.set_z(0 as libc::c_int);
            init
        };
        let mut z: s = {
            let mut init = s {
                y_z: [0; 1],
                c2rust_padding: [0; 3],
                x: 0 as libc::c_int,
            };
            init.set_y(0 as libc::c_int);
            init.set_z(0 as libc::c_int);
            init
        };
        let mut w: *mut s = if x != 0 { &mut y } else { &mut z };
        (*w).set_y(1 as libc::c_int);
        ",
        |g, _, _| {
            let n = get_nodes(&g, [2, 3, 10, 11, 18].into_iter());
            assert_eq!(g.get_absloc_as_int(n[&2].field(0).as_ptr()), Some(0));
            assert_eq!(n[&2].field(3), &Obj::Top);
            assert_eq!(g.get_absloc_as_int(n[&2].field(4).as_ptr()), Some(0));
            assert_eq!(g.get_absloc_as_int(n[&3].field(0).as_ptr()), Some(0));
            assert_eq!(g.get_absloc_as_int(n[&3].field(3).as_ptr()), Some(0));
            assert_eq!(g.get_absloc_as_int(n[&3].field(4).as_ptr()), Some(0));
            assert_eq!(g.get_absloc_as_int(n[&10].field(0).as_ptr()), Some(0));
            assert_eq!(n[&10].field(3), &Obj::Top);
            assert_eq!(g.get_absloc_as_int(n[&10].field(4).as_ptr()), Some(0));
            assert_eq!(g.get_absloc_as_int(n[&11].field(0).as_ptr()), Some(0));
            assert_eq!(g.get_absloc_as_int(n[&11].field(3).as_ptr()), Some(0));
            assert_eq!(g.get_absloc_as_int(n[&11].field(4).as_ptr()), Some(0));
            let dn18 = g.obj_at_location(n[&18].as_ptr()).unwrap();
            assert_eq!(g.get_absloc_as_int(dn18.field(0).as_ptr()), Some(0));
            assert_eq!(g.get_absloc_as_int(dn18.field(3).as_ptr()), Some(1));
            assert_eq!(g.get_absloc_as_int(dn18.field(4).as_ptr()), Some(0));
        },
    );
}

#[test]
fn test_union_invalidate() {
    // _2 = u { x: const 0_i32 }
    // _1 = s { x: const 0_i32, y: move _2 }
    // _5 = &mut _1
    // _4 = &raw mut (*_5)
    // _3 = g(move _4) -> [return: bb1, unwind continue]
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub union u {
            pub x: libc::c_int,
            pub y: libc::c_int,
        }
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
            pub y: u,
        }
        pub unsafe extern \"C\" fn g(mut x: *mut s) {
            let mut y: u = u { x: 0 as libc::c_int };
            (*x).y = y;
        }
        ",
        "",
        "
        let mut x: s = s { x: 0, y: u { x: 0 } };
        g(&mut x);
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=1);
            let Obj::Struct(fs, is_union) = &n[&1].field(1) else { unreachable!() };
            assert!(is_union);
            assert_eq!(fs.len(), 0);
        },
    );
}

#[test]
fn test_union_field_invalidate() {
    // _2 = u { x: const 0_i32 }
    // _1 = s { x: const 0_i32, y: move _2 }
    // _5 = &mut _1
    // _4 = &raw mut (*_5)
    // _3 = g(move _4) -> [return: bb1, unwind continue]
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub union u {
            pub x: libc::c_int,
            pub y: libc::c_int,
        }
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
            pub y: u,
        }
        pub unsafe extern \"C\" fn g(mut x: *mut s) {
            (*x).y.y = 0 as libc::c_int;
        }
        ",
        "",
        "
        let mut x: s = s { x: 0, y: u { x: 0 } };
        g(&mut x);
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=1);
            let Obj::Struct(fs, is_union) = &n[&1].field(1) else { unreachable!() };
            assert!(is_union);
            assert_eq!(fs.len(), 0);
        },
    );
}

#[test]
fn test_eq_static() {
    // DefId(0:5 ~ rust_out[8cf0]::x) {
    //     bb0:
    //         _0 = const 0_i32
    // }

    // DefId(0:6 ~ rust_out[8cf0]::foo) {
    //     bb0:
    //         _1 = const {alloc1: *mut i32}
    //         (*_1) = const 1_i32
    //         _3 = const {alloc1: *mut i32}
    //         _2 = copy (*_3)
    // }
    analyze_fn_with(
        "
        pub static mut x: libc::c_int = 0 as libc::c_int;
        ",
        "",
        "
        x = 1 as libc::c_int;
        let mut y: libc::c_int = x;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=3);
            assert_eq!(n[&1].as_ptr(), n[&3].as_ptr());
            assert_eq!(g.get_local_as_int(Local::from_usize(2)), Some(1));
        },
    );
}

#[test]
fn test_static_invalidate() {
    // DefId(0:5 ~ rust_out[8cf0]::x) {
    //     bb0:
    //         _0 = const 0_i32
    // }

    // DefId(0:6 ~ rust_out[8cf0]::g) {
    //     bb0:
    //         _1 = const {alloc1: *mut i32}
    //         (*_1) = const 2_i32
    // }

    // DefId(0:7 ~ rust_out[8cf0]::foo) {
    //     bb0:
    //         _1 = const {alloc1: *mut i32}
    //         (*_1) = const 1_i32
    //         _2 = g() -> [return: bb1, unwind unreachable]
    //     bb1:
    //         _4 = const {alloc1: *mut i32}
    //         _3 = copy (*_4)
    // }
    analyze_fn_with(
        "
        pub static mut x: libc::c_int = 0 as libc::c_int;
        pub unsafe extern \"C\" fn g() {
            x = 2 as libc::c_int;
        }
        ",
        "",
        "
        x = 1 as libc::c_int;
        g();
        let mut y: libc::c_int = x;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=4);
            println!("{:?}", n);
            assert_ne!(g.get_local_as_int(Local::from_usize(4)), Some(1));
            assert_eq!(n[&1].as_ptr(), n[&4].as_ptr());
        },
    );
}

#[test]
fn test_switch_filter() {
    // _2 = const 0_i32
    // switchInt(copy _1) -> [1: bb3, 2: bb2, otherwise: bb1]
    // _2 = const 3_i32
    // goto -> bb4
    // _2 = const 2_i32
    // goto -> bb4
    // _2 = const 1_i32
    // goto -> bb4
    // _3 = const 0_i32
    // switchInt(copy _2) -> [1: bb6, 2: bb6, otherwise: bb5]
    // _4 = copy _2
    // _3 = move _4
    // goto -> bb7
    // _3 = const 3_i32
    // goto -> bb7
    analyze_fn_with(
        "
        ",
        "mut x: libc::c_int",
        "
        let mut y: libc::c_int = 0 as libc::c_int;
        match x {
            1 => {
                y = 1 as libc::c_int;
            }
            2 => {
                y = 2 as libc::c_int;
            }
            _ => {
                y = 3 as libc::c_int;
            }
        }
        let mut z: libc::c_int = 0 as libc::c_int;
        match y {
            1 | 2 => {
                z = 3 as libc::c_int;
            }
            _ => {
                z = y;
            }
        };
        ",
        |g, _, _| {
            assert_eq!(g.get_local_as_int(Local::from_usize(3)), Some(3));
        },
    );
}
