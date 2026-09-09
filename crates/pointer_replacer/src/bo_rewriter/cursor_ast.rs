//! Structural cursor vocabulary for later W3B integration. The caller must
//! carry admission, full-base formation/schedule and terminal-use obligations.
//! This module neither manufactures that evidence nor installs source edits.

use rustc_ast::{
    AngleBracketedArg, AngleBracketedArgs, Block, BlockCheckMode, BorrowKind, DUMMY_NODE_ID, Expr,
    ExprKind, GenericArg, GenericArgs, MethodCall, MutTy, Mutability, Path, PathSegment, Stmt,
    StmtKind, Ty, TyKind, UnsafeSource, ptr::P,
};
use rustc_span::{DUMMY_SP, Ident, Symbol, symbol::kw};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Movement {
    Offset,
    Add,
    Sub,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum UnsafeContext {
    SafeBody,
    UnsafeBody,
}

/// Produces Option<usize>; the surrounding plan must handle arithmetic failure
/// and validate the carried window before a raw view or pointee access.
pub(crate) fn checked_step(movement: Movement, index: P<Expr>, delta: P<Expr>) -> P<Expr> {
    let method = match movement {
        Movement::Offset => "checked_add_signed",
        Movement::Add => "checked_add",
        Movement::Sub => "checked_sub",
    };
    method_call(index, method, vec![delta])
}

pub(crate) fn tuple(base: P<Expr>, index: P<Expr>) -> P<Expr> {
    expr(ExprKind::Tup([base, index].into_iter().collect()))
}

pub(crate) fn element(base: P<Expr>, index: P<Expr>, mutable: bool) -> P<Expr> {
    expr(ExprKind::AddrOf(
        BorrowKind::Ref,
        mutability(mutable),
        expr(ExprKind::Index(base, index, DUMMY_SP)),
    ))
}

pub(crate) fn raw_view(
    base: P<Expr>,
    index: P<Expr>,
    mutable: bool,
    context: UnsafeContext,
) -> P<Expr> {
    let method = if mutable { "as_mut_ptr" } else { "as_ptr" };
    // SAFETY: the integrating plan must establish a live initialized base and
    // index <= its carried extent, with the applicable extent-waiver receipt.
    // Pointer derivation retains the base's permission; the complete raw-use
    // interval, retention and shared-derived-write checks remain caller duties.
    // No element reference is formed, including at a one-past endpoint.
    let view = method_call(method_call(base, method, vec![]), "add", vec![index]);
    match context {
        UnsafeContext::UnsafeBody => view,
        UnsafeContext::SafeBody => expr(ExprKind::Block(
            P(Block {
                stmts: [Stmt {
                    id: DUMMY_NODE_ID,
                    kind: StmtKind::Expr(view),
                    span: DUMMY_SP,
                }]
                .into_iter()
                .collect(),
                id: DUMMY_NODE_ID,
                rules: BlockCheckMode::Unsafe(UnsafeSource::CompilerGenerated),
                span: DUMMY_SP,
                tokens: None,
            }),
            None,
        )),
    }
}

pub(crate) fn declaration(pointee: P<Ty>, mutable: bool, nullable: bool) -> P<Ty> {
    let slice = ty(TyKind::Slice(pointee));
    let reference = ty(TyKind::Ref(
        None,
        MutTy {
            ty: slice,
            mutbl: mutability(mutable),
        },
    ));
    let mut root = segment("core");
    root.ident = Ident::new(kw::PathRoot, DUMMY_SP);
    let index = ty(TyKind::Path(
        None,
        path(vec![
            root.clone(),
            segment("core"),
            segment("primitive"),
            segment("usize"),
        ]),
    ));
    let tuple = ty(TyKind::Tup([reference, index].into_iter().collect()));
    if !nullable {
        return tuple;
    }
    let mut option = segment("Option");
    option.args = Some(P(GenericArgs::AngleBracketed(AngleBracketedArgs {
        span: DUMMY_SP,
        args: [AngleBracketedArg::Arg(GenericArg::Type(tuple))]
            .into_iter()
            .collect(),
    })));
    ty(TyKind::Path(
        None,
        path(vec![root, segment("core"), segment("option"), option]),
    ))
}

fn mutability(mutable: bool) -> Mutability {
    if mutable {
        Mutability::Mut
    } else {
        Mutability::Not
    }
}

fn segment(name: &str) -> PathSegment {
    PathSegment {
        ident: Ident::new(Symbol::intern(name), DUMMY_SP),
        id: DUMMY_NODE_ID,
        args: None,
    }
}

fn path(segments: Vec<PathSegment>) -> Path {
    Path {
        span: DUMMY_SP,
        segments: segments.into_iter().collect(),
        tokens: None,
    }
}

fn method_call(receiver: P<Expr>, name: &str, args: Vec<P<Expr>>) -> P<Expr> {
    expr(ExprKind::MethodCall(Box::new(MethodCall {
        seg: segment(name),
        receiver,
        args: args.into_iter().collect(),
        span: DUMMY_SP,
    })))
}

fn expr(kind: ExprKind) -> P<Expr> {
    P(Expr {
        id: DUMMY_NODE_ID,
        kind,
        span: DUMMY_SP,
        attrs: Default::default(),
        tokens: None,
    })
}

fn ty(kind: TyKind) -> P<Ty> {
    P(Ty {
        id: DUMMY_NODE_ID,
        kind,
        span: DUMMY_SP,
        tokens: None,
    })
}
