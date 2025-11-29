use std::ops::{Deref, DerefMut};

use etrace::some_or;
use rustc_ast::*;
use rustc_ast_pretty::pprust;
use rustc_index::Idx;
use rustc_middle::ty::TyCtxt;
use typed_arena::Arena;
use utils::{
    bit_set::BitSet8,
    file::api_list::{Origin, Permission},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct Pot<'a> {
    pub(super) permissions: BitSet8<Permission>,
    #[allow(unused)]
    pub(super) origins: BitSet8<Origin>,
    pub(super) ty: &'a StreamType<'a>,
    pub(super) file_param_index: Option<usize>,
}

#[derive(Debug, Clone, Copy)]
pub(super) struct LocCtx<'tcx> {
    pub is_generic: bool,
    pub is_union: bool,
    pub is_non_local_assign: bool,
    pub is_param_without_assign: bool,
    pub is_recursive: bool,
    pub ty: rustc_middle::ty::Ty<'tcx>,
}

impl<'tcx> LocCtx<'tcx> {
    #[inline]
    pub(super) fn new(ty: rustc_middle::ty::Ty<'tcx>) -> Self {
        Self {
            is_generic: false,
            is_union: false,
            is_non_local_assign: false,
            is_param_without_assign: false,
            is_recursive: false,
            ty,
        }
    }
}

pub(super) struct TypeArena<'a> {
    arena: &'a Arena<StreamType<'a>>,
    std_write_error: bool,
}

impl<'a> TypeArena<'a> {
    #[inline]
    pub(super) fn new(arena: &'a Arena<StreamType<'a>>, std_write_error: bool) -> Self {
        Self {
            arena,
            std_write_error,
        }
    }

    #[inline]
    fn alloc(&self, ty: StreamType<'a>) -> &'a StreamType<'a> {
        self.arena.alloc(ty)
    }

    #[inline]
    fn buf_writer(&self, ty: &'a StreamType<'a>) -> &'a StreamType<'a> {
        self.arena.alloc(StreamType::BufWriter(ty))
    }

    #[inline]
    fn buf_reader(&self, ty: &'a StreamType<'a>) -> &'a StreamType<'a> {
        self.arena.alloc(StreamType::BufReader(ty))
    }

    #[inline]
    fn option(&self, ty: &'a StreamType<'a>) -> &'a StreamType<'a> {
        self.arena.alloc(StreamType::Option(ty))
    }

    #[inline]
    fn ptr(&self, ty: &'a StreamType<'a>) -> &'a StreamType<'a> {
        self.arena.alloc(StreamType::Ptr(ty))
    }

    #[inline]
    pub(super) fn ref_(&self, ty: &'a StreamType<'a>) -> &'a StreamType<'a> {
        self.arena.alloc(StreamType::Ref(ty))
    }

    #[inline]
    fn box_(&self, ty: &'a StreamType<'a>) -> &'a StreamType<'a> {
        self.arena.alloc(StreamType::Box(ty))
    }

    #[inline]
    fn manually_drop(&self, ty: &'a StreamType<'a>) -> &'a StreamType<'a> {
        self.arena.alloc(StreamType::ManuallyDrop(ty))
    }

    pub(super) fn make_ty<'tcx>(
        &self,
        permissions: BitSet8<Permission>,
        origins: BitSet8<Origin>,
        ctx: LocCtx<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> &'a StreamType<'a> {
        let ty = if ctx.is_generic {
            let mut traits = BitSet8::new_empty();
            for p in permissions.iter() {
                traits.insert(some_or!(StreamTrait::from_permission(p), continue));
            }
            if traits.contains(StreamTrait::BufRead) {
                traits.remove(StreamTrait::Read);
            }
            if permissions.contains(Permission::Close) && origins.contains(Origin::Pipe) {
                traits.insert(StreamTrait::Close);
            }
            if self.std_write_error && traits.contains(StreamTrait::Write) {
                traits.insert(StreamTrait::AsRawFd);
            }
            let mut ty = self.alloc(StreamType::Impl(TraitBound(traits)));
            if ctx.is_recursive && !permissions.contains(Permission::Close) {
                ty = self.ptr(ty);
            }
            self.option(ty)
        } else if origins.is_empty() {
            let ty = if !permissions.contains(Permission::Lock) {
                &FILE_TY
            } else if permissions.contains(Permission::Read) {
                &STDIN_TY
            } else {
                &STDOUT_TY
            };
            self.option(ty)
        } else if origins.count() == 1 {
            let origin = origins.iter().next().unwrap();
            let ty = match origin {
                Origin::Stdin => &STDIN_TY,
                Origin::Stdout => &STDOUT_TY,
                Origin::Stderr => &STDERR_TY,
                Origin::File => {
                    if (permissions.contains(Permission::Read)
                        || permissions.contains(Permission::BufRead))
                        && permissions.contains(Permission::Write)
                    {
                        &FILE_TY
                    } else if permissions.contains(Permission::Write) {
                        self.buf_writer(&FILE_TY)
                    } else if permissions.contains(Permission::Read)
                        || permissions.contains(Permission::BufRead)
                    {
                        self.buf_reader(&FILE_TY)
                    } else {
                        &FILE_TY
                    }
                }
                Origin::Pipe => &CHILD_TY,
                Origin::Buffer => todo!(),
            };
            if permissions.contains(Permission::Close)
                || ((origins.contains(Origin::Stdin)
                    || origins.contains(Origin::Stdout)
                    || origins.contains(Origin::Stderr))
                    && !ctx.is_non_local_assign
                    && !ctx.is_param_without_assign)
            {
                self.option(ty)
            } else {
                self.ptr(ty)
            }
        } else {
            let mut traits = BitSet8::new_empty();
            for p in permissions.iter() {
                traits.insert(some_or!(StreamTrait::from_permission(p), continue));
            }
            if traits.is_empty() || self.std_write_error && traits.contains(StreamTrait::Write) {
                traits.insert(StreamTrait::AsRawFd);
            }
            if traits.contains(StreamTrait::BufRead) {
                traits.remove(StreamTrait::Read);
            }
            if permissions.contains(Permission::Close) && origins.contains(Origin::Pipe) {
                traits.insert(StreamTrait::Close);
            }
            if permissions.contains(Permission::Lock) {
                traits.insert(StreamTrait::Lock);
            }
            let ty = self.alloc(StreamType::Dyn(TraitBound(traits)));
            let ty = if permissions.contains(Permission::Close) {
                self.box_(ty)
            } else {
                self.ptr(ty)
            };
            self.option(ty)
        };
        let ty = if utils::file::is_file_ptr_ptr(ctx.ty, tcx) {
            self.ptr(ty)
        } else {
            ty
        };
        if ctx.is_union && !ty.is_copyable() {
            self.manually_drop(ty)
        } else {
            ty
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum StreamType<'a> {
    File,
    Stdin,
    Stdout,
    Stderr,
    Child,
    Option(&'a StreamType<'a>),
    BufWriter(&'a StreamType<'a>),
    BufReader(&'a StreamType<'a>),
    Ptr(&'a StreamType<'a>),
    Ref(&'a StreamType<'a>),
    Box(&'a StreamType<'a>),
    ManuallyDrop(&'a StreamType<'a>),
    Dyn(TraitBound),
    Impl(TraitBound),
}

pub(super) static STDIN_TY: StreamType<'static> = StreamType::Stdin;
pub(super) static STDOUT_TY: StreamType<'static> = StreamType::Stdout;
pub(super) static STDERR_TY: StreamType<'static> = StreamType::Stderr;
pub(super) static FILE_TY: StreamType<'static> = StreamType::File;
pub(super) static CHILD_TY: StreamType<'static> = StreamType::Child;

impl std::fmt::Display for StreamType<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::File => write!(f, "std::fs::File"),
            Self::Stdin => write!(f, "std::io::Stdin"),
            Self::Stdout => write!(f, "std::io::Stdout"),
            Self::Stderr => write!(f, "std::io::Stderr"),
            Self::Child => write!(f, "crate::c_lib::Child"),
            Self::Option(t) => write!(f, "Option<{t}>"),
            Self::BufWriter(t) => write!(f, "std::io::BufWriter<{t}>"),
            Self::BufReader(t) => write!(f, "std::io::BufReader<{t}>"),
            Self::Ptr(t) => write!(f, "*mut {t}"),
            Self::Ref(t) => write!(f, "&mut {t}"),
            Self::Box(t) => write!(f, "Box<{t}>"),
            Self::ManuallyDrop(t) => write!(f, "std::mem::ManuallyDrop<{t}>"),
            Self::Dyn(traits) => {
                if traits.count() == 1 {
                    write!(f, "dyn {traits}")
                } else {
                    write!(f, "dyn crate::c_lib::{}", traits.trait_name())
                }
            }
            Self::Impl(traits) => write!(f, "impl {traits}"),
        }
    }
}

impl StreamType<'_> {
    pub(super) fn is_copyable(self) -> bool {
        match self {
            Self::File
            | Self::Stdin
            | Self::Stdout
            | Self::Stderr
            | Self::Child
            | Self::BufWriter(_)
            | Self::BufReader(_)
            | Self::Box(_)
            | Self::Dyn(_)
            | Self::Impl(_)
            | Self::Ref(_) => false,
            Self::Ptr(_) => true,
            Self::Option(t) | Self::ManuallyDrop(t) => t.is_copyable(),
        }
    }

    pub(super) fn contains_impl(self) -> bool {
        match self {
            Self::File | Self::Stdin | Self::Stdout | Self::Stderr | Self::Child | Self::Dyn(_) => {
                false
            }
            Self::Impl(_) => true,
            Self::Option(t)
            | Self::BufWriter(t)
            | Self::BufReader(t)
            | Self::Ptr(t)
            | Self::Ref(t)
            | Self::Box(t)
            | Self::ManuallyDrop(t) => t.contains_impl(),
        }
    }

    pub(super) fn get_dyn_bound(self) -> Option<TraitBound> {
        match self {
            Self::File
            | Self::Stdin
            | Self::Stdout
            | Self::Stderr
            | Self::Child
            | Self::Impl(_) => None,
            Self::Option(t)
            | Self::BufWriter(t)
            | Self::BufReader(t)
            | Self::Ptr(t)
            | Self::Ref(t)
            | Self::Box(t)
            | Self::ManuallyDrop(t) => t.get_dyn_bound(),
            Self::Dyn(traits) => Some(traits),
        }
    }

    pub(super) fn can_flush(self) -> bool {
        match self {
            Self::File | Self::Stdout | Self::Stderr | Self::BufWriter(_) => true,
            Self::Stdin | Self::Child | Self::BufReader(_) => false,
            Self::Option(t)
            | Self::Ptr(t)
            | Self::Ref(t)
            | Self::Box(t)
            | Self::ManuallyDrop(t) => t.can_flush(),
            Self::Dyn(traits) | Self::Impl(traits) => traits.contains(StreamTrait::Write),
        }
    }

    pub(super) fn must_stdout(self) -> bool {
        match self {
            Self::File
            | Self::Stdin
            | Self::Stderr
            | Self::Child
            | Self::Dyn(_)
            | Self::Impl(_) => false,
            Self::Stdout => true,
            Self::BufWriter(t)
            | Self::BufReader(t)
            | Self::Option(t)
            | Self::Ptr(t)
            | Self::Ref(t)
            | Self::Box(t)
            | Self::ManuallyDrop(t) => t.must_stdout(),
        }
    }

    pub(super) fn must_stderr(self) -> bool {
        match self {
            Self::File
            | Self::Stdin
            | Self::Stdout
            | Self::Child
            | Self::Dyn(_)
            | Self::Impl(_) => false,
            Self::Stderr => true,
            Self::BufWriter(t)
            | Self::BufReader(t)
            | Self::Option(t)
            | Self::Ptr(t)
            | Self::Ref(t)
            | Self::Box(t)
            | Self::ManuallyDrop(t) => t.must_stderr(),
        }
    }

    pub(super) fn may_std(self) -> bool {
        match self {
            Self::File | Self::Child => false,
            Self::Stdin | Self::Stdout | Self::Stderr | Self::Dyn(_) | Self::Impl(_) => true,
            Self::BufWriter(t)
            | Self::BufReader(t)
            | Self::Option(t)
            | Self::Ptr(t)
            | Self::Ref(t)
            | Self::Box(t)
            | Self::ManuallyDrop(t) => t.may_std(),
        }
    }

    pub(super) fn must_std(self) -> bool {
        match self {
            Self::File | Self::Child | Self::Dyn(_) | Self::Impl(_) => false,
            Self::Stdin | Self::Stdout | Self::Stderr => true,
            Self::BufWriter(t)
            | Self::BufReader(t)
            | Self::Option(t)
            | Self::Ptr(t)
            | Self::Ref(t)
            | Self::Box(t)
            | Self::ManuallyDrop(t) => t.must_std(),
        }
    }
}

pub(super) fn convert_expr(
    to: StreamType<'_>,
    from: StreamType<'_>,
    expr: &str,
    consume: bool,
    is_non_local: bool,
) -> String {
    tracing::info!("{} := {} // {}", to, from, consume);
    use StreamType::*;
    if to == from && (from.is_copyable() || consume && (!is_non_local || !matches!(to, Option(_))))
    {
        return expr.to_string();
    }
    match (to, from) {
        (Option(to), Option(from)) => {
            if from.is_copyable() {
                let body = convert_expr(*to, *from, "x", true, false);
                if to.contains_impl() {
                    format!("({expr}).map(|mut x| {body})")
                } else {
                    format!("({expr}).map::<{to}, _>(|mut x| {body})")
                }
            } else if consume {
                let body = convert_expr(*to, *from, "x", true, false);
                if is_non_local {
                    if to.contains_impl() {
                        format!("({expr}).take().map(|mut x| {body})")
                    } else {
                        format!("({expr}).take().map::<{to}, _>(|mut x| {body})")
                    }
                } else if to.contains_impl() {
                    format!("({expr}).map(|mut x| {body})")
                } else {
                    format!("({expr}).map::<{to}, _>(|mut x| {body})")
                }
            } else {
                let body = convert_expr(*to, Ref(from), "x", true, false);
                if to.contains_impl() {
                    format!("({expr}).as_mut().map(|mut x| {body})")
                } else {
                    format!("({expr}).as_mut().map::<{to}, _>(|mut x| {body})")
                }
            }
        }
        (Ptr(to), Option(from)) if to == from => {
            format!("({expr}).as_ref().map_or(std::ptr::null_mut(), |r| r as *const _ as *mut _)")
        }
        (Ptr(BufReader(File)), Option(File)) => {
            if consume {
                format!(
                    "Box::leak(Box::new(({expr}).map(std::io::BufReader::new))).as_mut().map_or(std::ptr::null_mut(), |x| x as _)"
                )
            } else {
                panic!()
            }
        }
        (Ptr(BufWriter(File)), Option(File)) => {
            if consume {
                format!(
                    "Box::leak(Box::new(({expr}).map(std::io::BufWriter::new))).as_mut().map_or(std::ptr::null_mut(), |x| x as _)"
                )
            } else {
                panic!()
            }
        }
        (Ptr(to), Ref(from)) if to == from => {
            format!("&mut *({expr}) as *mut _")
        }
        (to, Option(from)) => {
            if consume || from.is_copyable() {
                let unwrapped = if is_non_local {
                    format!("({expr}).take().unwrap()")
                } else {
                    format!("({expr}).unwrap()")
                };
                convert_expr(to, *from, &unwrapped, true, false)
            } else {
                let unwrapped = format!("({expr}).as_mut().unwrap()");
                convert_expr(to, Ref(from), &unwrapped, true, false)
            }
        }
        (to, Ref(Option(from))) => {
            let unwrapped = format!("({expr}).as_mut().unwrap()");
            convert_expr(to, Ref(from), &unwrapped, true, false)
        }
        (to, ManuallyDrop(from)) => {
            if consume {
                let unwrapped = format!("({expr}).take()");
                convert_expr(to, *from, &unwrapped, true, false)
            } else {
                let unwrapped = format!("std::ops::DerefMut::deref_mut(&mut ({expr}))");
                convert_expr(to, Ref(from), &unwrapped, true, false)
            }
        }
        (Option(to), from) => {
            let converted = convert_expr(*to, from, expr, consume, is_non_local);
            format!("Some({converted})")
        }
        (ManuallyDrop(to), from) => {
            let converted = convert_expr(*to, from, expr, consume, is_non_local);
            format!("std::mem::ManuallyDrop::new({converted})")
        }
        (Impl(_), File | Stdout | Stderr | Child | BufWriter(_) | BufReader(_) | Box(Dyn(_))) => {
            if consume {
                expr.to_string()
            } else {
                format!("&mut ({expr})")
            }
        }
        (
            Impl(_),
            Ref(File) | Ref(Stdout) | Ref(Stderr) | Ref(Child) | Ref(BufWriter(_))
            | Ref(BufReader(_)),
        ) => expr.to_string(),
        (Impl(traits), Stdin) => {
            if traits.contains(StreamTrait::BufRead) {
                format!("({expr}).lock()")
            } else if consume {
                expr.to_string()
            } else {
                format!("&mut ({expr})")
            }
        }
        (Impl(traits), Ref(Stdin)) => {
            if traits.contains(StreamTrait::BufRead) {
                format!("({expr}).lock()")
            } else if consume {
                expr.to_string()
            } else {
                format!("&mut *({expr})")
            }
        }
        (Impl(_), Ref(Impl(_))) => {
            if consume {
                expr.to_string()
            } else {
                format!("&mut *({expr})")
            }
        }
        (Impl(_), Ref(Box(Dyn(_)))) => {
            if consume {
                expr.to_string()
            } else {
                format!("&mut *({expr})")
            }
        }
        (Impl(_), Ptr(Dyn(_))) => format!("&mut *({expr})"),
        (Impl(_), Ptr(from)) => {
            let r = format!("({expr}).as_mut()");
            let from = Ref(from);
            convert_expr(to, Option(&from), &r, true, false)
        }
        (
            Box(Dyn(traits)),
            File | Stdin | Stdout | Stderr | Child | BufWriter(_) | BufReader(_),
        ) => {
            assert!(consume);
            match from {
                File => {
                    if traits.contains(StreamTrait::Read) || traits.contains(StreamTrait::BufRead) {
                        return format!(
                            "{{ let stream: {to} = Box::new(std::io::BufReader::new({expr})); stream }}"
                        );
                    }
                    if traits.contains(StreamTrait::Write) {
                        return format!(
                            "{{ let stream: {to} = Box::new(std::io::BufWriter::new({expr})); stream }}"
                        );
                    }
                }
                Stdin => {
                    if traits.contains(StreamTrait::BufRead) {
                        return format!(
                            "{{ let stream: {to} = Box::new(({expr}).lock()); stream }}"
                        );
                    }
                }
                _ => {}
            }
            format!("{{ let stream: {to} = Box::new({expr}); stream }}")
        }
        (
            Ref(Dyn(_)),
            Ref(File | Stdin | Stdout | Stderr | Child | BufWriter(_) | BufReader(_)),
        ) => {
            format!("&mut *({expr})")
        }
        (
            Ptr(Dyn(_)),
            Ref(File | Stdin | Stdout | Stderr | Child | BufWriter(_) | BufReader(_)),
        ) => {
            format!("&mut *({expr}) as *mut _")
        }
        (Ptr(Dyn(_)), Box(Dyn(_))) => {
            format!("&mut ({expr}) as *mut _")
        }
        (Ptr(Dyn(_)), Ref(Box(Dyn(_)))) => {
            format!("&mut *({expr}) as *mut _")
        }
        (Ptr(Dyn(_)), Ptr(Dyn(_))) => {
            format!("&mut *({expr}) as *mut _")
        }
        (
            Ptr(Impl(_) | Dyn(_)),
            Ptr(File | Stdin | Stdout | Stderr | Child | BufWriter(_) | BufReader(_)),
        ) => {
            format!("&mut *({expr}) as *mut _")
        }
        (
            Ref(Dyn(traits)),
            File | Stdin | Stdout | Stderr | Child | BufWriter(_) | BufReader(_),
        ) => {
            if consume {
                let expr = convert_expr(Box(&Dyn(*traits)), from, expr, true, is_non_local);
                format!("Box::leak({expr})")
            } else {
                format!("&mut ({expr})")
            }
        }
        (
            Ptr(Dyn(traits)),
            File | Stdin | Stdout | Stderr | Child | BufWriter(_) | BufReader(_),
        ) => {
            let expr = convert_expr(Ref(&Dyn(*traits)), from, expr, consume, is_non_local);
            format!("({expr}) as *mut _")
        }
        (BufWriter(to), from) if *to == from => {
            assert!(consume);
            format!("std::io::BufWriter::new({expr})")
        }
        (BufReader(to), from) if *to == from => {
            assert!(consume);
            format!("std::io::BufReader::new({expr})")
        }
        (Ptr(to), from) => {
            if consume {
                let converted = convert_expr(*to, from, expr, true, is_non_local);
                format!("Box::leak(Box::new({converted})) as *mut _")
            } else {
                let borrowed = format!("&mut ({expr})");
                convert_expr(Ptr(to), Ref(&from), &borrowed, true, false)
            }
        }
        _ => panic!("{to} := {from} // {consume}"),
    }
}

pub(super) trait StreamExpr {
    fn expr(&self) -> String;
    fn ty(&self) -> StreamType<'_>;

    #[inline]
    fn borrow_for(&self, tr: StreamTrait) -> String {
        let to = StreamType::Impl(TraitBound::new([tr]));
        convert_expr(to, self.ty(), &self.expr(), false, false)
    }
}

#[derive(Debug, Clone, Copy)]
pub(super) struct TypedExpr<'a> {
    expr: &'a Expr,
    ty: &'a StreamType<'a>,
}

impl<'a> TypedExpr<'a> {
    #[inline]
    pub(super) fn new(expr: &'a Expr, ty: &'a StreamType<'a>) -> Self {
        Self { expr, ty }
    }
}

impl StreamExpr for TypedExpr<'_> {
    #[inline]
    fn expr(&self) -> String {
        pprust::expr_to_string(self.expr)
    }

    #[inline]
    fn ty(&self) -> StreamType<'_> {
        *self.ty
    }
}

#[derive(Debug, Clone, Copy)]
pub(super) enum StdStream {
    Stdin,
    Stdout,
    #[allow(unused)]
    Stderr,
}

#[derive(Debug, Clone, Copy)]
pub(super) struct StdExpr(StdStream);

impl StdExpr {
    #[inline]
    pub(super) fn stdin() -> Self {
        Self(StdStream::Stdin)
    }

    #[inline]
    pub(super) fn stdout() -> Self {
        Self(StdStream::Stdout)
    }

    #[allow(unused)]
    #[inline]
    pub(super) fn stderr() -> Self {
        Self(StdStream::Stderr)
    }
}

impl StreamExpr for StdExpr {
    #[inline]
    fn expr(&self) -> String {
        match self.0 {
            StdStream::Stdin => "std::io::stdin()".to_string(),
            StdStream::Stdout => "std::io::stdout()".to_string(),
            StdStream::Stderr => "std::io::stderr()".to_string(),
        }
    }

    #[inline]
    fn ty(&self) -> StreamType<'_> {
        match self.0 {
            StdStream::Stdin => STDIN_TY,
            StdStream::Stdout => STDOUT_TY,
            StdStream::Stderr => STDERR_TY,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub(super) enum StreamTrait {
    Read = 0,
    BufRead = 1,
    Write = 2,
    Seek = 3,
    AsRawFd = 4,
    Close = 5,
    Lock = 6,
}

impl std::fmt::Display for StreamTrait {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Read => write!(f, "std::io::Read"),
            Self::BufRead => write!(f, "std::io::BufRead"),
            Self::Write => write!(f, "std::io::Write"),
            Self::Seek => write!(f, "std::io::Seek"),
            Self::AsRawFd => write!(f, "crate::c_lib::AsRawFd"),
            Self::Close => write!(f, "crate::c_lib::Close"),
            Self::Lock => write!(f, "crate::c_lib::Lock"),
        }
    }
}

impl StreamTrait {
    const NUM: usize = 7;

    pub(super) fn from_permission(p: Permission) -> Option<Self> {
        match p {
            Permission::Read => Some(Self::Read),
            Permission::BufRead => Some(Self::BufRead),
            Permission::Write => Some(Self::Write),
            Permission::Seek => Some(Self::Seek),
            Permission::AsRawFd => Some(Self::AsRawFd),
            Permission::Lock | Permission::Close => None,
        }
    }

    fn short_name(self) -> &'static str {
        match self {
            Self::Read => "Read",
            Self::BufRead => "BufRead",
            Self::Write => "Write",
            Self::Seek => "Seek",
            Self::AsRawFd => "AsRawFd",
            Self::Close => "Close",
            Self::Lock => "Lock",
        }
    }
}

impl Idx for StreamTrait {
    #[inline]
    fn new(idx: usize) -> Self {
        if idx >= Self::NUM {
            panic!()
        }
        unsafe { std::mem::transmute(idx as u8) }
    }

    #[inline]
    fn index(self) -> usize {
        self as _
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) struct TraitBound(BitSet8<StreamTrait>);

impl std::fmt::Display for TraitBound {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, t) in self.0.iter().enumerate() {
            if i != 0 {
                write!(f, " + ")?;
            }
            write!(f, "{t}")?;
        }
        Ok(())
    }
}

impl Deref for TraitBound {
    type Target = BitSet8<StreamTrait>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for TraitBound {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl TraitBound {
    #[inline]
    fn new<I: IntoIterator<Item = StreamTrait>>(traits: I) -> Self {
        Self(BitSet8::new(traits))
    }

    pub(super) fn trait_name(self) -> String {
        let mut name = String::new();
        for t in self.iter() {
            name.push_str(t.short_name());
        }
        name
    }
}
