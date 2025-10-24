use rustc_ast::*;
use utils::expr;

use super::{stream_ty::*, transform::LibItem, visitor::TransformVisitor};

impl TransformVisitor<'_, '_, '_> {
    #[inline]
    pub(super) fn transform_fileno<S: StreamExpr>(&self, stream: &S) -> Expr {
        let stream = stream.borrow_for(StreamTrait::AsRawFd);
        self.lib_items.borrow_mut().push(LibItem::AsRawFd);
        expr!("crate::stdio::AsRawFd::as_raw_fd({})", stream)
    }
}

pub(super) const AS_RAW_FD: &str = r#"
pub trait AsRawFd {
    fn as_raw_fd(&self) -> i32;
}
impl AsRawFd for std::fs::File {
    fn as_raw_fd(&self) -> i32 {
        std::os::unix::io::AsRawFd::as_raw_fd(self)
    }
}
impl AsRawFd for std::io::Stdin {
    fn as_raw_fd(&self) -> i32 {
        std::os::unix::io::AsRawFd::as_raw_fd(self)
    }
}
impl AsRawFd for std::io::StdinLock<'_> {
    fn as_raw_fd(&self) -> i32 {
        std::os::unix::io::AsRawFd::as_raw_fd(self)
    }
}
impl AsRawFd for std::io::Stdout {
    fn as_raw_fd(&self) -> i32 {
        std::os::unix::io::AsRawFd::as_raw_fd(self)
    }
}
impl AsRawFd for std::io::Stderr {
    fn as_raw_fd(&self) -> i32 {
        std::os::unix::io::AsRawFd::as_raw_fd(self)
    }
}
impl<T: AsRawFd + ?Sized> AsRawFd for &T {
    fn as_raw_fd(&self) -> i32 {
        (*self).as_raw_fd()
    }
}
impl<T: AsRawFd + ?Sized> AsRawFd for &mut T {
    fn as_raw_fd(&self) -> i32 {
        (**self).as_raw_fd()
    }
}
impl<T: AsRawFd + ?Sized> AsRawFd for Box<T> {
    fn as_raw_fd(&self) -> i32 {
        (**self).as_raw_fd()
    }
}
impl<T: AsRawFd> AsRawFd for std::io::BufReader<T> {
    fn as_raw_fd(&self) -> i32 {
        self.get_ref().as_raw_fd()
    }
}
impl<T: AsRawFd + std::io::Write> AsRawFd for std::io::BufWriter<T> {
    fn as_raw_fd(&self) -> i32 {
        self.get_ref().as_raw_fd()
    }
}
impl AsRawFd for std::process::ChildStdin {
    fn as_raw_fd(&self) -> i32 {
        std::os::unix::io::AsRawFd::as_raw_fd(self)
    }
}
impl AsRawFd for std::process::ChildStdout {
    fn as_raw_fd(&self) -> i32 {
        std::os::unix::io::AsRawFd::as_raw_fd(self)
    }
}
"#;
