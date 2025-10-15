use ApiKind::*;
use Origin::*;
use Permission::*;
use etrace::some_or;
use lazy_static::lazy_static;
use rustc_data_structures::fx::FxHashMap;
use rustc_index::Idx;
use rustc_middle::{query::IntoQueryParam, ty::TyCtxt};
use rustc_span::{Symbol, def_id::DefId};

use crate::ir_utils;

#[inline]
pub fn symbol_api_kind(name: Symbol) -> Option<ApiKind> {
    API_MAP
        .get(normalize_api_name(name.as_str()))
        .copied()
        .map(|info| info.kind)
}

#[inline]
pub fn def_id_api_kind(id: impl IntoQueryParam<DefId>, tcx: TyCtxt<'_>) -> Option<ApiKind> {
    symbol_api_kind(ir_utils::def_id_to_symbol(id, tcx)?)
}

#[inline]
pub fn is_symbol_api(name: Symbol) -> bool {
    API_MAP.contains_key(normalize_api_name(name.as_str()))
}

#[inline]
pub fn is_def_id_api(id: impl IntoQueryParam<DefId>, tcx: TyCtxt<'_>) -> bool {
    is_symbol_api(some_or!(ir_utils::def_id_to_symbol(id, tcx), return false))
}

#[inline]
pub fn normalize_api_name(name: &str) -> &str {
    if name == "__printf__" {
        return "printf";
    }
    let name = name.strip_suffix("_unlocked").unwrap_or(name);
    name.strip_prefix("rpl_").unwrap_or(name)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum Permission {
    Read = 0,
    BufRead = 1,
    Write = 2,
    Seek = 3,
    AsRawFd = 4,
    Lock = 5,
    Close = 6,
}

impl Permission {
    pub const NUM: usize = 7;
}

impl Idx for Permission {
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
#[repr(u8)]
pub enum Origin {
    Stdin = 0,
    Stdout = 1,
    Stderr = 2,
    File = 3,
    Pipe = 4,
    Buffer = 7,
}

impl Origin {
    pub const NUM: usize = 8;
}

impl Idx for Origin {
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

#[derive(Debug, Clone, Copy)]
pub enum ApiKind {
    Open(Origin),
    Operation(Option<Permission>),
    StdioOperation,
    Unsupported,
    FileSysOperation,
    FileDescrOperation,
    StringOperation,
    NonPosixOpen,
    NonPosix,
}

impl ApiKind {
    #[inline]
    pub fn is_operation(self) -> bool {
        matches!(self, Operation(_))
    }

    #[inline]
    pub fn is_unsupported(self) -> bool {
        matches!(self, Unsupported)
    }

    #[inline]
    pub fn is_posix_high_level_io(self) -> bool {
        match self {
            Open(_) | Operation(_) | StdioOperation | FileSysOperation | Unsupported => true,
            FileDescrOperation | StringOperation | NonPosixOpen | NonPosix => false,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct ApiInfo {
    pub kind: ApiKind,
    pub is_byte: bool,
}

impl ApiInfo {
    #[inline]
    const fn new(kind: ApiKind, is_byte: bool) -> Self {
        Self { kind, is_byte }
    }
}

lazy_static! {
    pub static ref API_MAP: FxHashMap<&'static str, ApiInfo> = API_LIST.iter().copied().collect();
}

pub static API_LIST: [(&str, ApiInfo); 102] = [
    // stdio.h
    // Open (6)
    ("fopen", ApiInfo::new(Open(File), true)),
    ("fdopen", ApiInfo::new(Open(File), true)),
    ("tmpfile", ApiInfo::new(Open(File), true)),
    ("popen", ApiInfo::new(Open(Pipe), true)),
    ("fmemopen", ApiInfo::new(Open(Buffer), true)),
    ("open_memstream", ApiInfo::new(Open(Buffer), true)),
    // Close (2)
    ("fclose", ApiInfo::new(Operation(Some(Close)), true)),
    ("pclose", ApiInfo::new(Operation(Some(Close)), true)),
    // Read (10)
    ("fscanf", ApiInfo::new(Operation(Some(BufRead)), true)),
    ("vfscanf", ApiInfo::new(Operation(Some(BufRead)), true)),
    ("getc", ApiInfo::new(Operation(Some(Read)), true)), // unlocked
    ("fgetc", ApiInfo::new(Operation(Some(Read)), true)),
    ("fgets", ApiInfo::new(Operation(Some(BufRead)), true)),
    ("fread", ApiInfo::new(Operation(Some(Read)), true)),
    ("ungetc", ApiInfo::new(Unsupported, true)),
    ("getline", ApiInfo::new(Operation(Some(BufRead)), true)),
    ("getdelim", ApiInfo::new(Operation(Some(BufRead)), true)),
    // Read stdin (5)
    ("scanf", ApiInfo::new(StdioOperation, true)),
    ("vscanf", ApiInfo::new(StdioOperation, true)),
    ("getchar", ApiInfo::new(StdioOperation, true)), // unlocked
    ("gets", ApiInfo::new(StdioOperation, true)),    // removed
    // Read string (2)
    ("sscanf", ApiInfo::new(StringOperation, true)),
    ("vsscanf", ApiInfo::new(StringOperation, true)),
    // Write (8)
    ("fprintf", ApiInfo::new(Operation(Some(Write)), true)),
    ("vfprintf", ApiInfo::new(Operation(Some(Write)), true)),
    ("putc", ApiInfo::new(Operation(Some(Write)), true)), // unlocked
    ("fputc", ApiInfo::new(Operation(Some(Write)), true)),
    ("fputs", ApiInfo::new(Operation(Some(Write)), true)),
    ("fwrite", ApiInfo::new(Operation(Some(Write)), true)),
    ("fflush", ApiInfo::new(Operation(Some(Write)), true)),
    // Write stdout/stderr (6)
    ("printf", ApiInfo::new(StdioOperation, true)),
    ("vprintf", ApiInfo::new(StdioOperation, true)),
    ("putchar", ApiInfo::new(StdioOperation, true)), // unlocked
    ("puts", ApiInfo::new(StdioOperation, true)),
    ("perror", ApiInfo::new(StdioOperation, true)),
    // Write fd (2)
    ("dprintf", ApiInfo::new(FileDescrOperation, true)),
    ("vdprintf", ApiInfo::new(FileDescrOperation, true)),
    // Write string (4)
    ("sprintf", ApiInfo::new(StringOperation, true)),
    ("vsprintf", ApiInfo::new(StringOperation, true)),
    ("snprintf", ApiInfo::new(StringOperation, true)),
    ("vsnprintf", ApiInfo::new(StringOperation, true)),
    // Positioning (7)
    ("fseek", ApiInfo::new(Operation(Some(Seek)), true)),
    ("fseeko", ApiInfo::new(Operation(Some(Seek)), true)),
    ("ftell", ApiInfo::new(Operation(Some(Seek)), true)),
    ("ftello", ApiInfo::new(Operation(Some(Seek)), true)),
    ("rewind", ApiInfo::new(Operation(Some(Seek)), true)),
    ("fgetpos", ApiInfo::new(Operation(Some(Seek)), true)),
    ("fsetpos", ApiInfo::new(Operation(Some(Seek)), true)),
    // Error (3)
    ("clearerr", ApiInfo::new(Operation(None), true)),
    ("feof", ApiInfo::new(Operation(None), true)),
    ("ferror", ApiInfo::new(Operation(None), true)),
    // Locking (3)
    ("flockfile", ApiInfo::new(Operation(Some(Lock)), true)),
    ("ftrylockfile", ApiInfo::new(Operation(Some(Lock)), true)),
    ("funlockfile", ApiInfo::new(Operation(Some(Lock)), true)),
    // Buffering (2)
    ("setvbuf", ApiInfo::new(Unsupported, true)),
    ("setbuf", ApiInfo::new(Unsupported, true)),
    // Other (2)
    ("freopen", ApiInfo::new(Unsupported, true)),
    ("fileno", ApiInfo::new(Operation(Some(AsRawFd)), true)),
    // File system (6)
    ("rename", ApiInfo::new(FileSysOperation, true)),
    ("renameat", ApiInfo::new(FileDescrOperation, true)),
    ("remove", ApiInfo::new(FileSysOperation, true)),
    ("tmpnam", ApiInfo::new(FileSysOperation, true)),
    ("tempnam", ApiInfo::new(FileSysOperation, true)), // removed
    ("ctermid", ApiInfo::new(FileSysOperation, true)),
    // GNU libc / Linux / 3rd-party
    ("__fpending", ApiInfo::new(NonPosix, true)),
    ("__freading", ApiInfo::new(NonPosix, true)),
    ("__fwriting", ApiInfo::new(NonPosix, true)),
    ("fpurge", ApiInfo::new(NonPosix, true)),
    ("setmntent", ApiInfo::new(NonPosixOpen, true)),
    ("getmntent", ApiInfo::new(NonPosix, true)),
    ("addmntent", ApiInfo::new(NonPosix, true)),
    ("endmntent", ApiInfo::new(NonPosix, true)),
    ("setlinebuf", ApiInfo::new(NonPosix, true)),
    ("setbuffer", ApiInfo::new(NonPosix, true)),
    ("__gmpz_out_str", ApiInfo::new(NonPosix, true)),
    ("newterm", ApiInfo::new(NonPosix, true)),
    ("pg_fprintf", ApiInfo::new(NonPosix, true)),
    ("ERR_print_errors_fp", ApiInfo::new(NonPosix, true)),
    ("fopencookie", ApiInfo::new(NonPosixOpen, true)),
    // wchar.h
    // Open (1)
    ("open_wmemstream", ApiInfo::new(Open(Buffer), false)),
    // Read (6)
    ("fwscanf", ApiInfo::new(Operation(Some(BufRead)), false)),
    ("vfwscanf", ApiInfo::new(Unsupported, false)),
    ("getwc", ApiInfo::new(Operation(Some(Read)), false)),
    ("fgetwc", ApiInfo::new(Operation(Some(Read)), false)),
    ("fgetws", ApiInfo::new(Operation(Some(BufRead)), false)),
    ("ungetwc", ApiInfo::new(Unsupported, false)),
    // Read stdin (3)
    ("wscanf", ApiInfo::new(StdioOperation, false)),
    ("vwscanf", ApiInfo::new(StdioOperation, false)),
    ("getwchar", ApiInfo::new(StdioOperation, false)),
    // Read string (2)
    ("swscanf", ApiInfo::new(StringOperation, false)),
    ("vswscanf", ApiInfo::new(StringOperation, false)),
    // Write (5)
    ("fwprintf", ApiInfo::new(Operation(Some(Write)), false)),
    ("vfwprintf", ApiInfo::new(Operation(Some(Write)), false)),
    ("putwc", ApiInfo::new(Operation(Some(Write)), false)),
    ("fputwc", ApiInfo::new(Operation(Some(Write)), false)),
    ("fputws", ApiInfo::new(Operation(Some(Write)), false)),
    // Write stdout/stderr (3)
    ("wprintf", ApiInfo::new(StdioOperation, false)),
    ("vwprintf", ApiInfo::new(StdioOperation, false)),
    ("putwchar", ApiInfo::new(StdioOperation, false)),
    // Write string (2)
    ("swprintf", ApiInfo::new(StringOperation, false)),
    ("vswprintf", ApiInfo::new(StringOperation, false)),
    // Orientation (1)
    ("fwide", ApiInfo::new(Unsupported, false)),
];
