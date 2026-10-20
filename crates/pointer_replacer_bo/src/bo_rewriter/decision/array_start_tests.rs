//! W-C6 controls on the idiom classifier itself.
use rustc_hir::intravisit::{self, Visitor};

fn first_sink_argument(input: &str) -> (bool, Option<bool>) {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        struct Find<'tcx> {
            tcx: rustc_middle::ty::TyCtxt<'tcx>,
            found: Option<(bool, Option<bool>)>,
        }
        impl<'tcx> Visitor<'tcx> for Find<'tcx> {
            fn visit_expr(&mut self, e: &'tcx rustc_hir::Expr<'tcx>) {
                if let rustc_hir::ExprKind::Call(callee, [arg, ..]) = e.kind
                    && let rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) =
                        callee.kind
                    && path
                        .segments
                        .last()
                        .is_some_and(|s| s.ident.name.as_str() == "sink")
                {
                    let idiom = super::array_start::idiom(self.tcx, arg);
                    let raw = matches!(
                        super::emitability::classify_arg(self.tcx, arg),
                        super::emitability::ArgShape::RawExpr { .. }
                    );
                    self.found = Some((raw, idiom.map(|i| i.blind)));
                }
                intravisit::walk_expr(self, e);
            }
        }
        let mut find = Find { tcx, found: None };
        for owner in tcx.hir_body_owners() {
            find.visit_body(tcx.hir_body_owned_by(owner));
        }
        find.found.expect("a call to sink")
    })
    .unwrap()
}

const HDR: &str = "#![allow(dead_code,unused_unsafe,unused_mut,unused_variables)]\nunsafe fn sink(p: *mut u32, n: usize) {}\n";

#[test]
fn w5c_array_start_local_array_is_a_visible_raw_start() {
    let input = format!(
        "{HDR}pub unsafe fn f() {{ let mut a: [u32; 8] = [0; 8]; sink(&mut *a.as_mut_ptr().offset(0), 8); }}"
    );
    assert_eq!(first_sink_argument(&input), (true, Some(false)));
    let nested = format!(
        "{HDR}pub unsafe fn f() {{ let mut a: [[u32; 8]; 3] = [[0; 8]; 3]; let i = 1usize; sink(&mut *(*a.as_mut_ptr().offset(i as isize)).as_mut_ptr().offset(0 as i32 as isize), 8); }}"
    );
    assert_eq!(first_sink_argument(&nested), (true, Some(false)));
}

#[test]
fn w5c_array_start_through_a_raw_pointer_is_blind() {
    let input = format!(
        "{HDR}#[repr(C)] pub struct S {{ pub data_: [u32; 8] }}\npub unsafe fn f(s: *mut S) {{ sink(&mut *((*s).data_).as_mut_ptr().offset(0), 8); }}"
    );
    assert_eq!(first_sink_argument(&input), (true, Some(true)));
}

#[test]
fn w5c_array_start_not_an_array_or_not_the_start_stays_a_borrow() {
    let pointer = format!("{HDR}pub unsafe fn f(p: *mut u32) {{ sink(&mut *p.offset(0), 8); }}");
    assert_eq!(first_sink_argument(&pointer), (false, None));
    let second = format!(
        "{HDR}pub unsafe fn f() {{ let mut a: [u32; 8] = [0; 8]; sink(&mut *a.as_mut_ptr().offset(1), 7); }}"
    );
    assert_eq!(first_sink_argument(&second), (false, None));
    let element =
        format!("{HDR}pub unsafe fn f() {{ let mut a: [u32; 8] = [0; 8]; sink(&mut a[0], 8); }}");
    assert_eq!(first_sink_argument(&element), (false, None));
}
