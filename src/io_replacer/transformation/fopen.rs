use rustc_ast::*;
use rustc_ast_pretty::pprust;
use rustc_span::Symbol;
use utils::expr;

use super::{likely_lit::LikelyLit, transform::LibItem, visitor::TransformVisitor};

impl TransformVisitor<'_, '_, '_> {
    pub(super) fn transform_fopen(&self, path: &Expr, mode_expr: &Expr) -> Expr {
        let mode = LikelyLit::from_expr(mode_expr);
        match mode {
            LikelyLit::Lit(mode) => {
                let mode = OpenMode::from_lit(mode);
                self.make_open_expr(mode, path, mode_expr)
            }
            LikelyLit::If(c, t, f) => {
                let t = OpenMode::from_likely_lit(&t);
                let f = OpenMode::from_likely_lit(&f);
                if t == f {
                    self.make_open_expr(t, path, mode_expr)
                } else {
                    let t = self.make_open_expr(t, path, mode_expr);
                    let f = self.make_open_expr(f, path, mode_expr);
                    let c = pprust::expr_to_string(c);
                    let t = pprust::expr_to_string(&t);
                    let f = pprust::expr_to_string(&f);
                    expr!("if {} {{ {} }} else {{ {} }}", c, t, f)
                }
            }
            LikelyLit::Path(_, _) => self.make_open_expr(OpenMode::Unknown, path, mode_expr),
            LikelyLit::Other(_) => todo!(),
        }
    }

    #[inline]
    pub(super) fn transform_fdopen(&self, fd: &Expr) -> Expr {
        let fd = pprust::expr_to_string(fd);
        expr!("std::os::fd::FromRawFd::from_raw_fd({})", fd)
    }

    #[inline]
    pub(super) fn transform_tmpfile(&self) -> Expr {
        expr!("tempfile::tempfile().ok()")
    }

    fn make_open_expr(&self, open_mode: OpenMode, path: &Expr, mode: &Expr) -> Expr {
        let path = pprust::expr_to_string(path);
        let path_str = format!("std::ffi::CStr::from_ptr(({path}) as _).to_str().unwrap()");
        match open_mode {
            OpenMode::Read(plus) => {
                if plus {
                    expr!(
                        "std::fs::OpenOptions::new()
                            .read(true)
                            .write(true)
                            .open({})
                            .ok()",
                        path_str,
                    )
                } else {
                    expr!("std::fs::File::open({}).ok()", path_str)
                }
            }
            OpenMode::Write(plus) => {
                if plus {
                    expr!(
                        "std::fs::OpenOptions::new()
                            .write(true)
                            .create(true)
                            .truncate(true)
                            .read(true)
                            .open({})
                            .ok()",
                        path_str,
                    )
                } else {
                    expr!("std::fs::File::create({}).ok()", path_str)
                }
            }
            OpenMode::Append(plus) => {
                if plus {
                    expr!(
                        "std::fs::OpenOptions::new()
                            .append(true)
                            .create(true)
                            .read(true)
                            .open({})
                            .ok()",
                        path_str,
                    )
                } else {
                    expr!(
                        "std::fs::OpenOptions::new()
                            .append(true)
                            .create(true)
                            .open({})
                            .ok()",
                        path_str,
                    )
                }
            }
            OpenMode::Unknown => {
                self.lib_items.borrow_mut().push(LibItem::Fopen);
                expr!(
                    "crate::stdio::rs_fopen({}, {})",
                    path,
                    pprust::expr_to_string(mode),
                )
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OpenMode {
    Read(bool),
    Write(bool),
    Append(bool),
    Unknown,
}

impl OpenMode {
    fn from_lit(mode: Symbol) -> Self {
        let (prefix, suffix) = mode.as_str().split_at(1);
        let plus = suffix.contains('+');
        match prefix {
            "r" => Self::Read(plus),
            "w" => Self::Write(plus),
            "a" => Self::Append(plus),
            _ => panic!("{mode:?}"),
        }
    }

    fn from_likely_lit(mode: &LikelyLit<'_>) -> Self {
        match mode {
            LikelyLit::Lit(mode) => Self::from_lit(*mode),
            LikelyLit::If(_, t, f) => {
                let t = Self::from_likely_lit(t);
                let f = Self::from_likely_lit(f);
                if t == f { t } else { Self::Unknown }
            }
            LikelyLit::Path(_, _) => Self::Unknown,
            LikelyLit::Other(_) => todo!(),
        }
    }
}

pub(super) static FOPEN: &str = r#"
pub(crate) unsafe fn rs_fopen(pathname: *const i8, mode: *const i8) -> Option<std::fs::File> {
    let pathname = std::ffi::CStr::from_ptr(pathname as _).to_str().unwrap();
    let mode = std::ffi::CStr::from_ptr(mode as _).to_str().unwrap();
    let (prefix, suffix) = mode.split_at(1);
    match prefix {
        "r" => {
            if suffix.contains('+') {
                std::fs::OpenOptions::new()
                    .read(true)
                    .write(true)
                    .open(pathname)
            } else {
                std::fs::File::open(pathname)
            }
        }
        "w" => {
            if suffix.contains('+') {
                std::fs::OpenOptions::new()
                    .write(true)
                    .create(true)
                    .truncate(true)
                    .read(true)
                    .open(pathname)
            } else {
                std::fs::File::create(pathname)
            }
        }
        "a" => {
            if suffix.contains('+') {
                std::fs::OpenOptions::new()
                    .append(true)
                    .create(true)
                    .read(true)
                    .open(pathname)
            } else {
                std::fs::OpenOptions::new()
                    .append(true)
                    .create(true)
                    .open(pathname)
            }
        }
        _ => panic!(),
    }
    .ok()
}
"#;
