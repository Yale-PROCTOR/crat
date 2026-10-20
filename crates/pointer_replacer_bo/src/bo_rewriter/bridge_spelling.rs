//! **R1128-1 (USER; main relay 332): the spelling of a NON-NULL raw-to-reference bridge.**
//!
//! `CRAT_BRIDGE_SPELLING=deref|as-ref-unwrap` (fail-loud; absent = `deref`, the spelling every census
//! before batch 61 emitted). `deref` writes `&*p` / `&mut *p`; `as-ref-unwrap` writes
//! `p.as_ref().unwrap()` / `p.as_mut().unwrap()`. For a non-null pointer the two are the same reference;
//! for a null one the second panics at the `unwrap` where the first is undefined behaviour. Emission
//! only: no decision, plan or receipt reads the switch, so the delivered set cannot move with it.
//!
//! Every renderer of such a bridge goes through [`text`] (or [`expr_kind`] on the AST side) and hands in
//! its own `deref` text, which is returned verbatim when the switch is off. The `Option` forms (already
//! `as_ref()` / `as_mut()`), the slice constructions, `Box::from_raw` and the reference-to-raw direction
//! do not come here.

use std::cell::Cell;

use rustc_ast::{ExprKind, MethodCall, PathSegment, ptr::P};
use rustc_span::{DUMMY_SP, symbol::Ident};
use thin_vec::ThinVec;

thread_local! {
    static OVERRIDE: Cell<Option<bool>> = const { Cell::new(None) };
}

/// Whether the switch is on.
pub(crate) fn as_ref_unwrap() -> bool {
    if let Some(on) = OVERRIDE.with(Cell::get) {
        return on;
    }
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(
        || match std::env::var("CRAT_BRIDGE_SPELLING").ok().as_deref() {
            None | Some("deref") => false,
            Some("as-ref-unwrap") => true,
            Some(other) => {
                panic!("CRAT_BRIDGE_SPELLING must be `deref` or `as-ref-unwrap`, got {other:?}")
            }
        },
    )
}

/// Run `f` with the spelling forced on this thread (tests: one process renders both spellings).
#[cfg(test)]
pub(crate) fn with_spelling<R>(as_ref_unwrap: bool, f: impl FnOnce() -> R) -> R {
    let previous = OVERRIDE.with(|cell| cell.replace(Some(as_ref_unwrap)));
    let result = f();
    OVERRIDE.with(|cell| cell.set(previous));
    result
}

fn method(mutable: bool) -> &'static str {
    if mutable { "as_mut" } else { "as_ref" }
}

/// The bridge's text: `deref` (the caller's own `&*…` / `&mut *…` spelling) when the switch is off,
/// else `OPERAND.as_mut().unwrap()` / `OPERAND.as_ref().unwrap()`, the operand parenthesized when it is
/// not a postfix expression (`*pp`, a cast, a binary operation).
pub(crate) fn text(operand: &str, mutable: bool, deref: String) -> String {
    if !as_ref_unwrap() {
        return deref;
    }
    let operand = operand.trim();
    let receiver = if postfix_expression(operand) {
        operand.to_owned()
    } else {
        format!("({operand})")
    };
    format!("{receiver}.{}().unwrap()", method(mutable))
}

/// The AST form of [`text`] for a renderer that builds nodes: `None` when the switch is off (the
/// caller keeps its `&*` / `&mut *` node).
pub(crate) fn expr_kind(arg: P<rustc_ast::Expr>, mutable: bool) -> Option<ExprKind> {
    if !as_ref_unwrap() {
        return None;
    }
    let receiver = if matches!(
        arg.kind,
        ExprKind::Path(..)
            | ExprKind::Field(..)
            | ExprKind::MethodCall(..)
            | ExprKind::Call(..)
            | ExprKind::Index(..)
            | ExprKind::Paren(..)
            | ExprKind::MacCall(..)
    ) {
        arg
    } else {
        P(rustc_ast::Expr {
            id: rustc_ast::DUMMY_NODE_ID,
            kind: ExprKind::Paren(arg),
            span: DUMMY_SP,
            attrs: Default::default(),
            tokens: None,
        })
    };
    let call = |receiver: P<rustc_ast::Expr>, name: &str| {
        P(rustc_ast::Expr {
            id: rustc_ast::DUMMY_NODE_ID,
            kind: ExprKind::MethodCall(Box::new(MethodCall {
                seg: PathSegment::from_ident(Ident::from_str(name)),
                receiver,
                args: ThinVec::new(),
                span: DUMMY_SP,
            })),
            span: DUMMY_SP,
            attrs: Default::default(),
            tokens: None,
        })
    };
    let as_ref = call(receiver, method(mutable));
    Some(ExprKind::MethodCall(Box::new(MethodCall {
        seg: PathSegment::from_ident(Ident::from_str("unwrap")),
        receiver: as_ref,
        args: ThinVec::new(),
        span: DUMMY_SP,
    })))
}

/// A path, a parenthesized group, or either followed by `.field`, `.method::<…>(…)`, `[…]` or `(…)`
/// suffixes, and nothing else: an expression a method call can be appended to without parentheses.
fn postfix_expression(text: &str) -> bool {
    let bytes = text.as_bytes();
    let mut i = 0;
    let group = |i: usize| -> Option<usize> {
        let (open, close) = match bytes.get(i)? {
            b'(' => (b'(', b')'),
            b'[' => (b'[', b']'),
            b'<' => (b'<', b'>'),
            _ => return None,
        };
        let mut depth = 0usize;
        for (j, &b) in bytes.iter().enumerate().skip(i) {
            if b == open {
                depth += 1;
            } else if b == close {
                depth -= 1;
                if depth == 0 {
                    return Some(j + 1);
                }
            }
        }
        None
    };
    let ident = |mut i: usize| -> Option<usize> {
        let start = i;
        while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
            i += 1;
        }
        (i > start && !bytes[start].is_ascii_digit()).then_some(i)
    };
    // The head: a path (`a`, `a::b`, `::core::x`) or a parenthesized group.
    if bytes.first() == Some(&b'(') {
        let Some(end) = group(0) else { return false };
        i = end;
    } else {
        if text.starts_with("::") {
            i = 2;
        }
        loop {
            let Some(end) = ident(i) else { return false };
            i = end;
            if text[i..].starts_with("::<") {
                let Some(end) = group(i + 2) else { return false };
                i = end;
            }
            if text[i..].starts_with("::") {
                i += 2;
            } else {
                break;
            }
        }
    }
    // The suffixes.
    while i < bytes.len() {
        match bytes[i] {
            b'.' => {
                let Some(end) = ident(i + 1) else { return false };
                i = end;
                if text[i..].starts_with("::<") {
                    let Some(end) = group(i + 2) else { return false };
                    i = end;
                }
            }
            b'(' | b'[' => {
                let Some(end) = group(i) else { return false };
                i = end;
            }
            _ => return false,
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::{postfix_expression, text, with_spelling};

    #[test]
    fn the_switch_off_returns_the_callers_own_spelling() {
        with_spelling(false, || {
            assert_eq!(text("p", true, "&mut *p".to_owned()), "&mut *p");
            assert_eq!(
                text("(*s).ptr", false, "&*(*s).ptr".to_owned()),
                "&*(*s).ptr"
            );
            assert_eq!(text("x", true, "&mut *(x)".to_owned()), "&mut *(x)");
        });
    }

    #[test]
    fn the_switch_on_spells_as_ref_unwrap_parenthesizing_only_a_non_postfix_operand() {
        with_spelling(true, || {
            for (operand, mutable, want) in [
                ("p", true, "p.as_mut().unwrap()"),
                ("p", false, "p.as_ref().unwrap()"),
                ("(*s).ptr", true, "(*s).ptr.as_mut().unwrap()"),
                ("*pp", true, "(*pp).as_mut().unwrap()"),
                (
                    "arr.as_mut_ptr()",
                    true,
                    "arr.as_mut_ptr().as_mut().unwrap()",
                ),
                (
                    "(t[i as usize]).as_mut_ptr()",
                    false,
                    "(t[i as usize]).as_mut_ptr().as_ref().unwrap()",
                ),
                ("q as *mut T", true, "(q as *mut T).as_mut().unwrap()"),
                (
                    "p.offset(4 as isize)",
                    false,
                    "p.offset(4 as isize).as_ref().unwrap()",
                ),
                (
                    "::core::ptr::null_mut::<T>()",
                    true,
                    "::core::ptr::null_mut::<T>().as_mut().unwrap()",
                ),
                ("a + b", false, "(a + b).as_ref().unwrap()"),
            ] {
                assert_eq!(text(operand, mutable, String::new()), want, "{operand}");
            }
        });
    }

    /// The AST form (the seam graft's) prints exactly as the text form (the span layer's), so the two
    /// emission paths cannot disagree on a bridge; off, it builds nothing and the caller keeps its node.
    #[test]
    fn the_ast_form_prints_as_the_text_form() {
        rustc_span::create_default_session_globals_then(|| {
            let print = |source: &str, mutable: bool| {
                super::expr_kind(
                    rustc_ast::ptr::P(::utils::ast::parse_expr(source.to_owned())),
                    mutable,
                )
                .map(|kind| {
                    rustc_ast_pretty::pprust::expr_to_string(&rustc_ast::Expr {
                        id: rustc_ast::DUMMY_NODE_ID,
                        kind,
                        span: rustc_span::DUMMY_SP,
                        attrs: Default::default(),
                        tokens: None,
                    })
                })
            };
            with_spelling(false, || assert_eq!(print("p", true), None));
            with_spelling(true, || {
                for (source, mutable) in [
                    ("(*s).ptr", true),
                    ("(*s).ptr", false),
                    ("*pp", true),
                    ("arr.as_mut_ptr()", false),
                    ("q as *mut T", true),
                    ("p", false),
                ] {
                    assert_eq!(
                        print(source, mutable).as_deref(),
                        Some(text(source, mutable, String::new()).as_str()),
                        "{source}"
                    );
                }
            });
        });
    }

    #[test]
    fn a_postfix_expression_is_a_path_or_a_group_with_suffixes_only() {
        for yes in [
            "p",
            "a::b",
            "(*s).ptr",
            "x.y.z()",
            "v[0]",
            "f(a, b)[1].g::<T>()",
            "(x)",
        ] {
            assert!(postfix_expression(yes), "{yes}");
        }
        for no in [
            "*p",
            "&x",
            "p as *mut T",
            "a + b",
            "-x",
            "",
            "1x",
            "(a) + (b)",
        ] {
            assert!(!postfix_expression(no), "{no}");
        }
    }
}
