use rustc_ast::*;
use rustc_span::Symbol;

use super::{stream_ty::*, visitor::TransformVisitor};

impl TransformVisitor<'_, '_, '_> {
    #[inline]
    pub(super) fn transform_flockfile<S: StreamExpr>(
        &self,
        stream: &S,
        name: Symbol,
    ) -> (Expr, bool) {
        let (expr, is_file) = expr_to_lock(stream);
        if is_file {
            (expr!("{}.lock().unwrap()", expr), false)
        } else if stream.ty().get_dyn_bound().is_some() {
            (expr!("{}_guard = (&*{}).lock()", name, expr), true)
        } else {
            (expr!("{}_guard = {}.lock()", name, expr), true)
        }
    }

    #[inline]
    pub(super) fn transform_funlockfile<S: StreamExpr>(&self, stream: &S, name: Symbol) -> Expr {
        let (expr, is_file) = expr_to_lock(stream);
        if is_file {
            expr!("{}.unlock().unwrap()", expr)
        } else {
            expr!("drop({}_guard)", name)
        }
    }
}

fn expr_to_lock<S: StreamExpr>(stream: &S) -> (String, bool) {
    let ty = stream.ty();
    let (ty, unwrap) = if let StreamType::Option(ty) = ty {
        (*ty, ".as_ref().unwrap()")
    } else {
        (ty, "")
    };
    let (ty, get_ref) = if let StreamType::BufWriter(ty) | StreamType::BufReader(ty) = ty {
        (*ty, ".get_ref()")
    } else {
        (ty, "")
    };
    let (ty, deref) = if let StreamType::Ptr(ty) = ty {
        (*ty, "*")
    } else {
        (ty, "")
    };
    (
        format!("({}({}){}{})", deref, stream.expr(), unwrap, get_ref),
        ty == StreamType::File,
    )
}

pub(super) const LOCK: &str = r#"
pub trait Lock {
    fn lock(&self) -> Box<dyn Guard>;
}
impl Lock for std::io::Stdin {
    fn lock(&self) -> Box<dyn Guard> {
        Box::new(self.lock())
    }
}
impl Lock for std::io::Stdout {
    fn lock(&self) -> Box<dyn Guard> {
        Box::new(self.lock())
    }
}
impl Lock for std::io::Stderr {
    fn lock(&self) -> Box<dyn Guard> {
        Box::new(self.lock())
    }
}
pub trait Guard {}
impl Guard for std::io::StdinLock<'_> {}
impl Guard for std::io::StdoutLock<'_> {}
impl Guard for std::io::StderrLock<'_> {}
"#;
