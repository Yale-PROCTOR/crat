use rustc_ast::*;
use rustc_ast_pretty::pprust;
use utils::expr;

use super::{likely_lit::LikelyLit, transform::LibItem, visitor::TransformVisitor};

impl TransformVisitor<'_, '_, '_> {
    pub(super) fn transform_popen(&self, command: &Expr, mode: &Expr) -> Expr {
        let command = pprust::expr_to_string(command);
        let command = format!("std::ffi::CStr::from_ptr(({command}) as _).to_str().unwrap()");
        let mode = LikelyLit::from_expr(mode);
        self.lib_items.borrow_mut().insert(LibItem::Child);
        match is_popen_read(&mode) {
            Some(read) => {
                let field = if read { "stdout" } else { "stdin" };
                expr!(
                    r#"std::process::Command::new("sh")
                .arg("-c")
                .arg("--")
                .arg({})
                .{1}(std::process::Stdio::piped())
                .spawn()
                .ok()
                .map(|c| crate::c_lib::Child::new(c))"#,
                    command,
                    field
                )
            }
            None => todo!("{:?}", mode),
        }
    }
}

fn is_popen_read(arg: &LikelyLit<'_>) -> Option<bool> {
    match arg {
        LikelyLit::Lit(lit) => match &lit.as_str()[..1] {
            "r" => Some(true),
            "w" => Some(false),
            _ => panic!("{lit:?}"),
        },
        LikelyLit::If(_, t, f) => {
            let t = is_popen_read(t);
            let f = is_popen_read(f);
            if t == f { t } else { None }
        }
        LikelyLit::Path(_, _) | LikelyLit::Other(_) => None,
    }
}

pub(super) const CHILD: &str = r#"
pub struct Child {
    child: std::process::Child,
    stdout: Option<std::io::BufReader<std::process::ChildStdout>>,
    stdin: Option<std::io::BufWriter<std::process::ChildStdin>>,
}
impl Child {
    #[inline]
    pub fn new(mut child: std::process::Child) -> Self {
        let stdout = child.stdout.take().map(std::io::BufReader::new);
        let stdin = child.stdin.take().map(std::io::BufWriter::new);
        Self {
            child,
            stdout,
            stdin,
        }
    }
}
impl std::io::Read for Child {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        self.stdout.as_mut().unwrap().read(buf)
    }
}
impl std::io::Write for Child {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.stdin.as_mut().unwrap().write(buf)
    }

    fn flush(&mut self) -> std::io::Result<()> {
        self.stdin.as_mut().unwrap().flush()
    }
}
"#;

pub(super) const CHILD_AS_RAW_FD: &str = r#"
impl AsRawFd for Child {
    fn as_raw_fd(&self) -> i32 {
        self.stdout
            .as_ref()
            .map(AsRawFd::as_raw_fd)
            .or_else(|| self.stdin.as_ref().map(AsRawFd::as_raw_fd))
            .unwrap()
    }
}
"#;

pub(super) const CHILD_CLOSE: &str = r#"
impl Close for Child {
    fn close(&mut self) -> i32 {
        drop(self.stdout.take());
        drop(self.stdin.take());
        self.child.wait().ok().and_then(|e| e.code()).unwrap_or(-1)
    }
}
"#;
