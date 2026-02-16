use ::libc;
extern "C" {
    pub type _IO_wide_data;
    pub type _IO_codecvt;
    pub type _IO_marker;
    fn __assert_fail(
        __assertion: *const libc::c_char,
        __file: *const libc::c_char,
        __line: libc::c_uint,
        __function: *const libc::c_char,
    ) -> !;
    fn __ctype_b_loc() -> *mut *const libc::c_ushort;
    static mut stdin: *mut FILE;
    static mut stderr: *mut FILE;
    fn fprintf(_: *mut FILE, _: *const libc::c_char, _: ...) -> libc::c_int;
    fn printf(_: *const libc::c_char, _: ...) -> libc::c_int;
    fn vfprintf(
        _: *mut FILE,
        _: *const libc::c_char,
        _: ::std::ffi::VaList,
    ) -> libc::c_int;
    fn snprintf(
        _: *mut libc::c_char,
        _: libc::c_ulong,
        _: *const libc::c_char,
        _: ...
    ) -> libc::c_int;
    fn getc(__stream: *mut FILE) -> libc::c_int;
    fn ungetc(__c: libc::c_int, __stream: *mut FILE) -> libc::c_int;
    fn exit(_: libc::c_int) -> !;
    fn getenv(__name: *const libc::c_char) -> *mut libc::c_char;
    fn memcpy(
        _: *mut libc::c_void,
        _: *const libc::c_void,
        _: libc::c_ulong,
    ) -> *mut libc::c_void;
    fn strcmp(_: *const libc::c_char, _: *const libc::c_char) -> libc::c_int;
    fn strchr(_: *const libc::c_char, _: libc::c_int) -> *mut libc::c_char;
    fn strlen(_: *const libc::c_char) -> libc::c_ulong;
    fn strcpy(_: *mut libc::c_char, _: *const libc::c_char) -> *mut libc::c_char;
    fn mmap(
        __addr: *mut libc::c_void,
        __len: size_t,
        __prot: libc::c_int,
        __flags: libc::c_int,
        __fd: libc::c_int,
        __offset: __off_t,
    ) -> *mut libc::c_void;
    fn munmap(__addr: *mut libc::c_void, __len: size_t) -> libc::c_int;
}
pub type __builtin_va_list = [__va_list_tag; 1];
#[derive(Copy, Clone)]
#[repr(C)]
pub struct __va_list_tag {
    pub gp_offset: libc::c_uint,
    pub fp_offset: libc::c_uint,
    pub overflow_arg_area: *mut libc::c_void,
    pub reg_save_area: *mut libc::c_void,
}
pub type __uint8_t = libc::c_uchar;
pub type __off_t = libc::c_long;
pub type __off64_t = libc::c_long;
pub type C2RustUnnamed = libc::c_uint;
pub const _ISalnum: C2RustUnnamed = 8;
pub const _ISpunct: C2RustUnnamed = 4;
pub const _IScntrl: C2RustUnnamed = 2;
pub const _ISblank: C2RustUnnamed = 1;
pub const _ISgraph: C2RustUnnamed = 32768;
pub const _ISprint: C2RustUnnamed = 16384;
pub const _ISspace: C2RustUnnamed = 8192;
pub const _ISxdigit: C2RustUnnamed = 4096;
pub const _ISdigit: C2RustUnnamed = 2048;
pub const _ISalpha: C2RustUnnamed = 1024;
pub const _ISlower: C2RustUnnamed = 512;
pub const _ISupper: C2RustUnnamed = 256;
pub type va_list = __builtin_va_list;
pub type ptrdiff_t = libc::c_long;
pub type size_t = libc::c_ulong;
pub type uint8_t = __uint8_t;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct _IO_FILE {
    pub _flags: libc::c_int,
    pub _IO_read_ptr: *mut libc::c_char,
    pub _IO_read_end: *mut libc::c_char,
    pub _IO_read_base: *mut libc::c_char,
    pub _IO_write_base: *mut libc::c_char,
    pub _IO_write_ptr: *mut libc::c_char,
    pub _IO_write_end: *mut libc::c_char,
    pub _IO_buf_base: *mut libc::c_char,
    pub _IO_buf_end: *mut libc::c_char,
    pub _IO_save_base: *mut libc::c_char,
    pub _IO_backup_base: *mut libc::c_char,
    pub _IO_save_end: *mut libc::c_char,
    pub _markers: *mut _IO_marker,
    pub _chain: *mut _IO_FILE,
    pub _fileno: libc::c_int,
    pub _flags2: libc::c_int,
    pub _old_offset: __off_t,
    pub _cur_column: libc::c_ushort,
    pub _vtable_offset: libc::c_schar,
    pub _shortbuf: [libc::c_char; 1],
    pub _lock: *mut libc::c_void,
    pub _offset: __off64_t,
    pub _codecvt: *mut _IO_codecvt,
    pub _wide_data: *mut _IO_wide_data,
    pub _freeres_list: *mut _IO_FILE,
    pub _freeres_buf: *mut libc::c_void,
    pub __pad5: size_t,
    pub _mode: libc::c_int,
    pub _unused2: [libc::c_char; 20],
}
pub type _IO_lock_t = ();
pub type FILE = _IO_FILE;
pub type C2RustUnnamed_0 = libc::c_uint;
pub const TCPAREN: C2RustUnnamed_0 = 12;
pub const TDOT: C2RustUnnamed_0 = 11;
pub const TNIL: C2RustUnnamed_0 = 10;
pub const TTRUE: C2RustUnnamed_0 = 9;
pub const TMOVED: C2RustUnnamed_0 = 8;
pub const TENV: C2RustUnnamed_0 = 7;
pub const TMACRO: C2RustUnnamed_0 = 6;
pub const TFUNCTION: C2RustUnnamed_0 = 5;
pub const TPRIMITIVE: C2RustUnnamed_0 = 4;
pub const TSYMBOL: C2RustUnnamed_0 = 3;
pub const TCELL: C2RustUnnamed_0 = 2;
pub const TINT: C2RustUnnamed_0 = 1;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct Obj {
    pub type_0: libc::c_int,
    pub size: libc::c_int,
    pub c2rust_unnamed: C2RustUnnamed_1,
}
#[derive(Copy, Clone)]
#[repr(C)]
pub union C2RustUnnamed_1 {
    pub value: libc::c_int,
    pub c2rust_unnamed: C2RustUnnamed_4,
    pub name: [libc::c_char; 24],
    pub fn_0: Option::<Primitive>,
    pub c2rust_unnamed_0: C2RustUnnamed_3,
    pub c2rust_unnamed_1: C2RustUnnamed_2,
    pub moved: *mut libc::c_void,
}
#[derive(Copy, Clone)]
#[repr(C)]
pub struct C2RustUnnamed_2 {
    pub vars: *mut Obj,
    pub up: *mut Obj,
}
#[derive(Copy, Clone)]
#[repr(C)]
pub struct C2RustUnnamed_3 {
    pub params: *mut Obj,
    pub body: *mut Obj,
    pub env: *mut Obj,
}
pub type Primitive = unsafe extern "C" fn(
    *mut libc::c_void,
    *mut *mut Obj,
    *mut *mut Obj,
) -> *mut Obj;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct C2RustUnnamed_4 {
    pub car: *mut Obj,
    pub cdr: *mut Obj,
}
#[inline]
unsafe extern "C" fn getchar() -> libc::c_int {
    return getc(stdin);
}
unsafe extern "C" fn error(mut fmt: *mut libc::c_char, mut args: ...) -> ! {
    let mut ap: ::std::ffi::VaListImpl;
    ap = args.clone();
    vfprintf(stderr, fmt, ap.as_va_list());
    fprintf(stderr, b"\n\0" as *const u8 as *const libc::c_char);
    exit(1 as libc::c_int);
}
static mut True: *mut Obj = &{
    let mut init = Obj {
        type_0: 9,
        size: 0,
        c2rust_unnamed: C2RustUnnamed_1 { value: 0 },
    };
    init
} as *const Obj as *mut Obj;
static mut Nil: *mut Obj = &{
    let mut init = Obj {
        type_0: 10,
        size: 0,
        c2rust_unnamed: C2RustUnnamed_1 { value: 0 },
    };
    init
} as *const Obj as *mut Obj;
static mut Dot: *mut Obj = &{
    let mut init = Obj {
        type_0: 11,
        size: 0,
        c2rust_unnamed: C2RustUnnamed_1 { value: 0 },
    };
    init
} as *const Obj as *mut Obj;
static mut Cparen: *mut Obj = &{
    let mut init = Obj {
        type_0: 12,
        size: 0,
        c2rust_unnamed: C2RustUnnamed_1 { value: 0 },
    };
    init
} as *const Obj as *mut Obj;
static mut Symbols: *mut Obj = 0 as *const Obj as *mut Obj;
static mut memory: *mut libc::c_void = 0 as *const libc::c_void as *mut libc::c_void;
static mut from_space: *mut libc::c_void = 0 as *const libc::c_void as *mut libc::c_void;
static mut mem_nused: size_t = 0 as libc::c_int as size_t;
static mut gc_running: bool = 0 as libc::c_int != 0;
static mut debug_gc: bool = 0 as libc::c_int != 0;
static mut always_gc: bool = 0 as libc::c_int != 0;
#[inline]
unsafe extern "C" fn roundup(mut var: size_t, mut size: size_t) -> size_t {
    return var.wrapping_add(size).wrapping_sub(1 as libc::c_int as libc::c_ulong)
        & !size.wrapping_sub(1 as libc::c_int as libc::c_ulong);
}
unsafe extern "C" fn alloc(
    mut root: *mut libc::c_void,
    mut type_0: libc::c_int,
    mut size: size_t,
) -> *mut Obj {
    size = roundup(size, ::std::mem::size_of::<*mut libc::c_void>() as libc::c_ulong);
    size = (size as libc::c_ulong).wrapping_add(8 as libc::c_ulong) as size_t as size_t;
    size = roundup(size, ::std::mem::size_of::<*mut libc::c_void>() as libc::c_ulong);
    if always_gc as libc::c_int != 0 && !gc_running {
        gc(root);
    }
    if !always_gc
        && (65536 as libc::c_int as libc::c_ulong) < mem_nused.wrapping_add(size)
    {
        gc(root);
    }
    if (65536 as libc::c_int as libc::c_ulong) < mem_nused.wrapping_add(size) {
        error(
            b"Memory exhausted\0" as *const u8 as *const libc::c_char
                as *mut libc::c_char,
        );
    }
    let mut obj: *mut Obj = memory.offset(mem_nused as isize) as *mut Obj;
    (*obj).type_0 = type_0;
    (*obj).size = size as libc::c_int;
    mem_nused = (mem_nused as libc::c_ulong).wrapping_add(size) as size_t as size_t;
    return obj;
}
static mut scan1: *mut Obj = 0 as *const Obj as *mut Obj;
static mut scan2: *mut Obj = 0 as *const Obj as *mut Obj;
#[inline]
unsafe extern "C" fn forward(mut obj: *mut Obj) -> *mut Obj {
    let mut offset: ptrdiff_t = (obj as *mut uint8_t)
        .offset_from(from_space as *mut uint8_t) as libc::c_long;
    if offset < 0 as libc::c_int as libc::c_long
        || 65536 as libc::c_int as libc::c_long <= offset
    {
        return obj;
    }
    if (*obj).type_0 == TMOVED as libc::c_int {
        return (*obj).c2rust_unnamed.moved as *mut Obj;
    }
    let mut newloc: *mut Obj = scan2;
    memcpy(
        newloc as *mut libc::c_void,
        obj as *const libc::c_void,
        (*obj).size as libc::c_ulong,
    );
    scan2 = (scan2 as *mut uint8_t).offset((*obj).size as isize) as *mut Obj;
    (*obj).type_0 = TMOVED as libc::c_int;
    (*obj).c2rust_unnamed.moved = newloc as *mut libc::c_void;
    return newloc;
}
unsafe extern "C" fn alloc_semispace() -> *mut libc::c_void {
    return mmap(
        0 as *mut libc::c_void,
        65536 as libc::c_int as size_t,
        0x1 as libc::c_int | 0x2 as libc::c_int,
        0x2 as libc::c_int | 0x20 as libc::c_int,
        -(1 as libc::c_int),
        0 as libc::c_int as __off_t,
    );
}
unsafe extern "C" fn forward_root_objects(mut root: *mut libc::c_void) {
    Symbols = forward(Symbols);
    let mut frame: *mut *mut libc::c_void = root as *mut *mut libc::c_void;
    while !frame.is_null() {
        let mut i: libc::c_int = 1 as libc::c_int;
        while *frame.offset(i as isize) != -(1 as libc::c_int) as *mut libc::c_void {
            if !(*frame.offset(i as isize)).is_null() {
                let ref mut fresh0 = *frame.offset(i as isize);
                *fresh0 = forward(*frame.offset(i as isize) as *mut Obj)
                    as *mut libc::c_void;
            }
            i += 1;
            i;
        }
        frame = *(frame as *mut *mut *mut libc::c_void);
    }
}
unsafe extern "C" fn gc(mut root: *mut libc::c_void) {
    if !gc_running {} else {
        __assert_fail(
            b"!gc_running\0" as *const u8 as *const libc::c_char,
            b"minilisp.c\0" as *const u8 as *const libc::c_char,
            275 as libc::c_int as libc::c_uint,
            (*::std::mem::transmute::<
                &[u8; 16],
                &[libc::c_char; 16],
            >(b"void gc(void *)\0"))
                .as_ptr(),
        );
    }
    'c_3086: {
        if !gc_running {} else {
            __assert_fail(
                b"!gc_running\0" as *const u8 as *const libc::c_char,
                b"minilisp.c\0" as *const u8 as *const libc::c_char,
                275 as libc::c_int as libc::c_uint,
                (*::std::mem::transmute::<
                    &[u8; 16],
                    &[libc::c_char; 16],
                >(b"void gc(void *)\0"))
                    .as_ptr(),
            );
        }
    };
    gc_running = 1 as libc::c_int != 0;
    from_space = memory;
    memory = alloc_semispace();
    scan2 = memory as *mut Obj;
    scan1 = scan2;
    forward_root_objects(root);
    while scan1 < scan2 {
        match (*scan1).type_0 {
            1 | 3 | 4 => {}
            2 => {
                (*scan1)
                    .c2rust_unnamed
                    .c2rust_unnamed
                    .car = forward((*scan1).c2rust_unnamed.c2rust_unnamed.car);
                (*scan1)
                    .c2rust_unnamed
                    .c2rust_unnamed
                    .cdr = forward((*scan1).c2rust_unnamed.c2rust_unnamed.cdr);
            }
            5 | 6 => {
                (*scan1)
                    .c2rust_unnamed
                    .c2rust_unnamed_0
                    .params = forward((*scan1).c2rust_unnamed.c2rust_unnamed_0.params);
                (*scan1)
                    .c2rust_unnamed
                    .c2rust_unnamed_0
                    .body = forward((*scan1).c2rust_unnamed.c2rust_unnamed_0.body);
                (*scan1)
                    .c2rust_unnamed
                    .c2rust_unnamed_0
                    .env = forward((*scan1).c2rust_unnamed.c2rust_unnamed_0.env);
            }
            7 => {
                (*scan1)
                    .c2rust_unnamed
                    .c2rust_unnamed_1
                    .vars = forward((*scan1).c2rust_unnamed.c2rust_unnamed_1.vars);
                (*scan1)
                    .c2rust_unnamed
                    .c2rust_unnamed_1
                    .up = forward((*scan1).c2rust_unnamed.c2rust_unnamed_1.up);
            }
            _ => {
                error(
                    b"Bug: copy: unknown type %d\0" as *const u8 as *const libc::c_char
                        as *mut libc::c_char,
                    (*scan1).type_0,
                );
            }
        }
        scan1 = (scan1 as *mut uint8_t).offset((*scan1).size as isize) as *mut Obj;
    }
    munmap(from_space, 65536 as libc::c_int as size_t);
    let mut old_nused: size_t = mem_nused;
    mem_nused = (scan1 as *mut uint8_t).offset_from(memory as *mut uint8_t)
        as libc::c_long as size_t;
    if debug_gc {
        fprintf(
            stderr,
            b"GC: %zu bytes out of %zu bytes copied.\n\0" as *const u8
                as *const libc::c_char,
            mem_nused,
            old_nused,
        );
    }
    gc_running = 0 as libc::c_int != 0;
}
unsafe extern "C" fn make_int(
    mut root: *mut libc::c_void,
    mut value: libc::c_int,
) -> *mut Obj {
    let mut r: *mut Obj = alloc(
        root,
        TINT as libc::c_int,
        ::std::mem::size_of::<libc::c_int>() as libc::c_ulong,
    );
    (*r).c2rust_unnamed.value = value;
    return r;
}
unsafe extern "C" fn cons(
    mut root: *mut libc::c_void,
    mut car: *mut *mut Obj,
    mut cdr: *mut *mut Obj,
) -> *mut Obj {
    let mut cell: *mut Obj = alloc(
        root,
        TCELL as libc::c_int,
        (::std::mem::size_of::<*mut Obj>() as libc::c_ulong)
            .wrapping_mul(2 as libc::c_int as libc::c_ulong),
    );
    (*cell).c2rust_unnamed.c2rust_unnamed.car = *car;
    (*cell).c2rust_unnamed.c2rust_unnamed.cdr = *cdr;
    return cell;
}
unsafe extern "C" fn make_symbol(
    mut root: *mut libc::c_void,
    mut name: *mut libc::c_char,
) -> *mut Obj {
    let mut sym: *mut Obj = alloc(
        root,
        TSYMBOL as libc::c_int,
        (strlen(name)).wrapping_add(1 as libc::c_int as libc::c_ulong),
    );
    strcpy(((*sym).c2rust_unnamed.name).as_mut_ptr(), name);
    return sym;
}
unsafe extern "C" fn make_primitive(
    mut root: *mut libc::c_void,
    mut fn_0: Option::<Primitive>,
) -> *mut Obj {
    let mut r: *mut Obj = alloc(
        root,
        TPRIMITIVE as libc::c_int,
        ::std::mem::size_of::<Option::<Primitive>>() as libc::c_ulong,
    );
    (*r).c2rust_unnamed.fn_0 = fn_0;
    return r;
}
unsafe extern "C" fn make_function(
    mut root: *mut libc::c_void,
    mut env: *mut *mut Obj,
    mut type_0: libc::c_int,
    mut params: *mut *mut Obj,
    mut body: *mut *mut Obj,
) -> *mut Obj {
    if type_0 == TFUNCTION as libc::c_int || type_0 == TMACRO as libc::c_int {} else {
        __assert_fail(
            b"type == TFUNCTION || type == TMACRO\0" as *const u8 as *const libc::c_char,
            b"minilisp.c\0" as *const u8 as *const libc::c_char,
            357 as libc::c_int as libc::c_uint,
            (*::std::mem::transmute::<
                &[u8; 56],
                &[libc::c_char; 56],
            >(b"Obj *make_function(void *, Obj **, int, Obj **, Obj **)\0"))
                .as_ptr(),
        );
    }
    'c_3452: {
        if type_0 == TFUNCTION as libc::c_int || type_0 == TMACRO as libc::c_int
        {} else {
            __assert_fail(
                b"type == TFUNCTION || type == TMACRO\0" as *const u8
                    as *const libc::c_char,
                b"minilisp.c\0" as *const u8 as *const libc::c_char,
                357 as libc::c_int as libc::c_uint,
                (*::std::mem::transmute::<
                    &[u8; 56],
                    &[libc::c_char; 56],
                >(b"Obj *make_function(void *, Obj **, int, Obj **, Obj **)\0"))
                    .as_ptr(),
            );
        }
    };
    let mut r: *mut Obj = alloc(
        root,
        type_0,
        (::std::mem::size_of::<*mut Obj>() as libc::c_ulong)
            .wrapping_mul(3 as libc::c_int as libc::c_ulong),
    );
    (*r).c2rust_unnamed.c2rust_unnamed_0.params = *params;
    (*r).c2rust_unnamed.c2rust_unnamed_0.body = *body;
    (*r).c2rust_unnamed.c2rust_unnamed_0.env = *env;
    return r;
}
pub unsafe extern "C" fn make_env(
    mut root: *mut libc::c_void,
    mut vars: *mut *mut Obj,
    mut up: *mut *mut Obj,
) -> *mut Obj {
    let mut r: *mut Obj = alloc(
        root,
        TENV as libc::c_int,
        (::std::mem::size_of::<*mut Obj>() as libc::c_ulong)
            .wrapping_mul(2 as libc::c_int as libc::c_ulong),
    );
    (*r).c2rust_unnamed.c2rust_unnamed_1.vars = *vars;
    (*r).c2rust_unnamed.c2rust_unnamed_1.up = *up;
    return r;
}
unsafe extern "C" fn acons(
    mut root: *mut libc::c_void,
    mut x: *mut *mut Obj,
    mut y: *mut *mut Obj,
    mut a: *mut *mut Obj,
) -> *mut Obj {
    let mut root_ADD_ROOT_: [*mut libc::c_void; 3] = [0 as *mut libc::c_void; 3];
    root_ADD_ROOT_[0 as libc::c_int as usize] = root;
    let mut i: libc::c_int = 1 as libc::c_int;
    while i <= 1 as libc::c_int {
        root_ADD_ROOT_[i as usize] = 0 as *mut libc::c_void;
        i += 1;
        i;
    }
    root_ADD_ROOT_[(1 as libc::c_int + 1 as libc::c_int)
        as usize] = -(1 as libc::c_int) as *mut libc::c_void;
    root = root_ADD_ROOT_.as_mut_ptr() as *mut libc::c_void;
    let mut cell: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(1 as libc::c_int as isize) as *mut *mut Obj;
    *cell = cons(root, x, y);
    return cons(root, cell, a);
}
pub static mut symbol_chars: [libc::c_char; 19] = unsafe {
    *::std::mem::transmute::<&[u8; 19], &[libc::c_char; 19]>(b"~!@#$%^&*-_=+:/?<>\0")
};
unsafe extern "C" fn peek() -> libc::c_int {
    let mut c: libc::c_int = getchar();
    ungetc(c, stdin);
    return c;
}
unsafe extern "C" fn reverse(mut p: *mut Obj) -> *mut Obj {
    let mut ret: *mut Obj = Nil;
    while p != Nil {
        let mut head: *mut Obj = p;
        p = (*p).c2rust_unnamed.c2rust_unnamed.cdr;
        (*head).c2rust_unnamed.c2rust_unnamed.cdr = ret;
        ret = head;
    }
    return ret;
}
unsafe extern "C" fn skip_line() {
    loop {
        let mut c: libc::c_int = getchar();
        if c == -(1 as libc::c_int) || c == '\n' as i32 {
            return;
        }
        if c == '\r' as i32 {
            if peek() == '\n' as i32 {
                getchar();
            }
            return;
        }
    };
}
unsafe extern "C" fn read_list(mut root: *mut libc::c_void) -> *mut Obj {
    let mut root_ADD_ROOT_: [*mut libc::c_void; 5] = [0 as *mut libc::c_void; 5];
    root_ADD_ROOT_[0 as libc::c_int as usize] = root;
    let mut i: libc::c_int = 1 as libc::c_int;
    while i <= 3 as libc::c_int {
        root_ADD_ROOT_[i as usize] = 0 as *mut libc::c_void;
        i += 1;
        i;
    }
    root_ADD_ROOT_[(3 as libc::c_int + 1 as libc::c_int)
        as usize] = -(1 as libc::c_int) as *mut libc::c_void;
    root = root_ADD_ROOT_.as_mut_ptr() as *mut libc::c_void;
    let mut obj: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(1 as libc::c_int as isize) as *mut *mut Obj;
    let mut head: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(2 as libc::c_int as isize) as *mut *mut Obj;
    let mut last: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(3 as libc::c_int as isize) as *mut *mut Obj;
    *head = Nil;
    loop {
        *obj = read_expr(root);
        if (*obj).is_null() {
            error(
                b"Unclosed parenthesis\0" as *const u8 as *const libc::c_char
                    as *mut libc::c_char,
            );
        }
        if *obj == Cparen {
            return reverse(*head);
        }
        if *obj == Dot {
            *last = read_expr(root);
            if read_expr(root) != Cparen {
                error(
                    b"Closed parenthesis expected after dot\0" as *const u8
                        as *const libc::c_char as *mut libc::c_char,
                );
            }
            let mut ret: *mut Obj = reverse(*head);
            (**head).c2rust_unnamed.c2rust_unnamed.cdr = *last;
            return ret;
        }
        *head = cons(root, obj, head);
    };
}
unsafe extern "C" fn intern(
    mut root: *mut libc::c_void,
    mut name: *mut libc::c_char,
) -> *mut Obj {
    let mut p: *mut Obj = Symbols;
    while p != Nil {
        if strcmp(
            name,
            ((*(*p).c2rust_unnamed.c2rust_unnamed.car).c2rust_unnamed.name).as_mut_ptr(),
        ) == 0 as libc::c_int
        {
            return (*p).c2rust_unnamed.c2rust_unnamed.car;
        }
        p = (*p).c2rust_unnamed.c2rust_unnamed.cdr;
    }
    let mut root_ADD_ROOT_: [*mut libc::c_void; 3] = [0 as *mut libc::c_void; 3];
    root_ADD_ROOT_[0 as libc::c_int as usize] = root;
    let mut i: libc::c_int = 1 as libc::c_int;
    while i <= 1 as libc::c_int {
        root_ADD_ROOT_[i as usize] = 0 as *mut libc::c_void;
        i += 1;
        i;
    }
    root_ADD_ROOT_[(1 as libc::c_int + 1 as libc::c_int)
        as usize] = -(1 as libc::c_int) as *mut libc::c_void;
    root = root_ADD_ROOT_.as_mut_ptr() as *mut libc::c_void;
    let mut sym: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(1 as libc::c_int as isize) as *mut *mut Obj;
    *sym = make_symbol(root, name);
    Symbols = cons(root, sym, &mut Symbols);
    return *sym;
}
unsafe extern "C" fn read_quote(mut root: *mut libc::c_void) -> *mut Obj {
    let mut root_ADD_ROOT_: [*mut libc::c_void; 4] = [0 as *mut libc::c_void; 4];
    root_ADD_ROOT_[0 as libc::c_int as usize] = root;
    let mut i: libc::c_int = 1 as libc::c_int;
    while i <= 2 as libc::c_int {
        root_ADD_ROOT_[i as usize] = 0 as *mut libc::c_void;
        i += 1;
        i;
    }
    root_ADD_ROOT_[(2 as libc::c_int + 1 as libc::c_int)
        as usize] = -(1 as libc::c_int) as *mut libc::c_void;
    root = root_ADD_ROOT_.as_mut_ptr() as *mut libc::c_void;
    let mut sym: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(1 as libc::c_int as isize) as *mut *mut Obj;
    let mut tmp: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(2 as libc::c_int as isize) as *mut *mut Obj;
    *sym = intern(
        root,
        b"quote\0" as *const u8 as *const libc::c_char as *mut libc::c_char,
    );
    *tmp = read_expr(root);
    *tmp = cons(root, tmp, &mut Nil);
    *tmp = cons(root, sym, tmp);
    return *tmp;
}
unsafe extern "C" fn read_number(mut val: libc::c_int) -> libc::c_int {
    while *(*__ctype_b_loc()).offset(peek() as isize) as libc::c_int
        & _ISdigit as libc::c_int as libc::c_ushort as libc::c_int != 0
    {
        val = val * 10 as libc::c_int + (getchar() - '0' as i32);
    }
    return val;
}
unsafe extern "C" fn read_symbol(
    mut root: *mut libc::c_void,
    mut c: libc::c_char,
) -> *mut Obj {
    let mut buf: [libc::c_char; 201] = [0; 201];
    buf[0 as libc::c_int as usize] = c;
    let mut len: libc::c_int = 1 as libc::c_int;
    while *(*__ctype_b_loc()).offset(peek() as isize) as libc::c_int
        & _ISalnum as libc::c_int as libc::c_ushort as libc::c_int != 0
        || !(strchr(symbol_chars.as_ptr(), peek())).is_null()
    {
        if 200 as libc::c_int <= len {
            error(
                b"Symbol name too long\0" as *const u8 as *const libc::c_char
                    as *mut libc::c_char,
            );
        }
        let fresh1 = len;
        len = len + 1;
        buf[fresh1 as usize] = getchar() as libc::c_char;
    }
    buf[len as usize] = '\0' as i32 as libc::c_char;
    return intern(root, buf.as_mut_ptr());
}
unsafe extern "C" fn read_expr(mut root: *mut libc::c_void) -> *mut Obj {
    loop {
        let mut c: libc::c_int = getchar();
        if c == ' ' as i32 || c == '\n' as i32 || c == '\r' as i32 || c == '\t' as i32 {
            continue;
        }
        if c == -(1 as libc::c_int) {
            return 0 as *mut Obj;
        }
        if c == ';' as i32 {
            skip_line();
        } else {
            if c == '(' as i32 {
                return read_list(root);
            }
            if c == ')' as i32 {
                return Cparen;
            }
            if c == '.' as i32 {
                return Dot;
            }
            if c == '\'' as i32 {
                return read_quote(root);
            }
            if *(*__ctype_b_loc()).offset(c as isize) as libc::c_int
                & _ISdigit as libc::c_int as libc::c_ushort as libc::c_int != 0
            {
                return make_int(root, read_number(c - '0' as i32));
            }
            if c == '-' as i32
                && *(*__ctype_b_loc()).offset(peek() as isize) as libc::c_int
                    & _ISdigit as libc::c_int as libc::c_ushort as libc::c_int != 0
            {
                return make_int(root, -read_number(0 as libc::c_int));
            }
            if *(*__ctype_b_loc()).offset(c as isize) as libc::c_int
                & _ISalpha as libc::c_int as libc::c_ushort as libc::c_int != 0
                || !(strchr(symbol_chars.as_ptr(), c)).is_null()
            {
                return read_symbol(root, c as libc::c_char);
            }
            error(
                b"Don't know how to handle %c\0" as *const u8 as *const libc::c_char
                    as *mut libc::c_char,
                c,
            );
        }
    };
}
unsafe extern "C" fn print(mut obj: *mut Obj) {
    match (*obj).type_0 {
        2 => {
            printf(b"(\0" as *const u8 as *const libc::c_char);
            loop {
                print((*obj).c2rust_unnamed.c2rust_unnamed.car);
                if (*obj).c2rust_unnamed.c2rust_unnamed.cdr == Nil {
                    break;
                }
                if (*(*obj).c2rust_unnamed.c2rust_unnamed.cdr).type_0
                    != TCELL as libc::c_int
                {
                    printf(b" . \0" as *const u8 as *const libc::c_char);
                    print((*obj).c2rust_unnamed.c2rust_unnamed.cdr);
                    break;
                } else {
                    printf(b" \0" as *const u8 as *const libc::c_char);
                    obj = (*obj).c2rust_unnamed.c2rust_unnamed.cdr;
                }
            }
            printf(b")\0" as *const u8 as *const libc::c_char);
            return;
        }
        1 => {
            printf(
                b"%d\0" as *const u8 as *const libc::c_char,
                (*obj).c2rust_unnamed.value,
            );
            return;
        }
        3 => {
            printf(
                b"%s\0" as *const u8 as *const libc::c_char,
                ((*obj).c2rust_unnamed.name).as_mut_ptr(),
            );
            return;
        }
        4 => {
            printf(b"<primitive>\0" as *const u8 as *const libc::c_char);
            return;
        }
        5 => {
            printf(b"<function>\0" as *const u8 as *const libc::c_char);
            return;
        }
        6 => {
            printf(b"<macro>\0" as *const u8 as *const libc::c_char);
            return;
        }
        8 => {
            printf(b"<moved>\0" as *const u8 as *const libc::c_char);
            return;
        }
        9 => {
            printf(b"t\0" as *const u8 as *const libc::c_char);
            return;
        }
        10 => {
            printf(b"()\0" as *const u8 as *const libc::c_char);
            return;
        }
        _ => {
            error(
                b"Bug: print: Unknown tag type: %d\0" as *const u8 as *const libc::c_char
                    as *mut libc::c_char,
                (*obj).type_0,
            );
        }
    };
}
unsafe extern "C" fn length(mut list: *mut Obj) -> libc::c_int {
    let mut len: libc::c_int = 0 as libc::c_int;
    while (*list).type_0 == TCELL as libc::c_int {
        len += 1;
        len;
        list = (*list).c2rust_unnamed.c2rust_unnamed.cdr;
    }
    return if list == Nil { len } else { -(1 as libc::c_int) };
}
unsafe extern "C" fn add_variable(
    mut root: *mut libc::c_void,
    mut env: *mut *mut Obj,
    mut sym: *mut *mut Obj,
    mut val: *mut *mut Obj,
) {
    let mut root_ADD_ROOT_: [*mut libc::c_void; 4] = [0 as *mut libc::c_void; 4];
    root_ADD_ROOT_[0 as libc::c_int as usize] = root;
    let mut i: libc::c_int = 1 as libc::c_int;
    while i <= 2 as libc::c_int {
        root_ADD_ROOT_[i as usize] = 0 as *mut libc::c_void;
        i += 1;
        i;
    }
    root_ADD_ROOT_[(2 as libc::c_int + 1 as libc::c_int)
        as usize] = -(1 as libc::c_int) as *mut libc::c_void;
    root = root_ADD_ROOT_.as_mut_ptr() as *mut libc::c_void;
    let mut vars: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(1 as libc::c_int as isize) as *mut *mut Obj;
    let mut tmp: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(2 as libc::c_int as isize) as *mut *mut Obj;
    *vars = (**env).c2rust_unnamed.c2rust_unnamed_1.vars;
    *tmp = acons(root, sym, val, vars);
    (**env).c2rust_unnamed.c2rust_unnamed_1.vars = *tmp;
}
unsafe extern "C" fn push_env(
    mut root: *mut libc::c_void,
    mut env: *mut *mut Obj,
    mut vars: *mut *mut Obj,
    mut vals: *mut *mut Obj,
) -> *mut Obj {
    let mut root_ADD_ROOT_: [*mut libc::c_void; 5] = [0 as *mut libc::c_void; 5];
    root_ADD_ROOT_[0 as libc::c_int as usize] = root;
    let mut i: libc::c_int = 1 as libc::c_int;
    while i <= 3 as libc::c_int {
        root_ADD_ROOT_[i as usize] = 0 as *mut libc::c_void;
        i += 1;
        i;
    }
    root_ADD_ROOT_[(3 as libc::c_int + 1 as libc::c_int)
        as usize] = -(1 as libc::c_int) as *mut libc::c_void;
    root = root_ADD_ROOT_.as_mut_ptr() as *mut libc::c_void;
    let mut map: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(1 as libc::c_int as isize) as *mut *mut Obj;
    let mut sym: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(2 as libc::c_int as isize) as *mut *mut Obj;
    let mut val: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(3 as libc::c_int as isize) as *mut *mut Obj;
    *map = Nil;
    while (**vars).type_0 == TCELL as libc::c_int {
        if (**vals).type_0 != TCELL as libc::c_int {
            error(
                b"Cannot apply function: number of argument does not match\0"
                    as *const u8 as *const libc::c_char as *mut libc::c_char,
            );
        }
        *sym = (**vars).c2rust_unnamed.c2rust_unnamed.car;
        *val = (**vals).c2rust_unnamed.c2rust_unnamed.car;
        *map = acons(root, sym, val, map);
        *vars = (**vars).c2rust_unnamed.c2rust_unnamed.cdr;
        *vals = (**vals).c2rust_unnamed.c2rust_unnamed.cdr;
    }
    if *vars != Nil {
        *map = acons(root, vars, vals, map);
    }
    return make_env(root, map, env);
}
unsafe extern "C" fn progn(
    mut root: *mut libc::c_void,
    mut env: *mut *mut Obj,
    mut list: *mut *mut Obj,
) -> *mut Obj {
    let mut root_ADD_ROOT_: [*mut libc::c_void; 4] = [0 as *mut libc::c_void; 4];
    root_ADD_ROOT_[0 as libc::c_int as usize] = root;
    let mut i: libc::c_int = 1 as libc::c_int;
    while i <= 2 as libc::c_int {
        root_ADD_ROOT_[i as usize] = 0 as *mut libc::c_void;
        i += 1;
        i;
    }
    root_ADD_ROOT_[(2 as libc::c_int + 1 as libc::c_int)
        as usize] = -(1 as libc::c_int) as *mut libc::c_void;
    root = root_ADD_ROOT_.as_mut_ptr() as *mut libc::c_void;
    let mut lp: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(1 as libc::c_int as isize) as *mut *mut Obj;
    let mut r: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(2 as libc::c_int as isize) as *mut *mut Obj;
    *lp = *list;
    while *lp != Nil {
        *r = (**lp).c2rust_unnamed.c2rust_unnamed.car;
        *r = eval(root, env, r);
        *lp = (**lp).c2rust_unnamed.c2rust_unnamed.cdr;
    }
    return *r;
}
unsafe extern "C" fn eval_list(
    mut root: *mut libc::c_void,
    mut env: *mut *mut Obj,
    mut list: *mut *mut Obj,
) -> *mut Obj {
    let mut root_ADD_ROOT_: [*mut libc::c_void; 6] = [0 as *mut libc::c_void; 6];
    root_ADD_ROOT_[0 as libc::c_int as usize] = root;
    let mut i: libc::c_int = 1 as libc::c_int;
    while i <= 4 as libc::c_int {
        root_ADD_ROOT_[i as usize] = 0 as *mut libc::c_void;
        i += 1;
        i;
    }
    root_ADD_ROOT_[(4 as libc::c_int + 1 as libc::c_int)
        as usize] = -(1 as libc::c_int) as *mut libc::c_void;
    root = root_ADD_ROOT_.as_mut_ptr() as *mut libc::c_void;
    let mut head: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(1 as libc::c_int as isize) as *mut *mut Obj;
    let mut lp: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(2 as libc::c_int as isize) as *mut *mut Obj;
    let mut expr: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(3 as libc::c_int as isize) as *mut *mut Obj;
    let mut result: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(4 as libc::c_int as isize) as *mut *mut Obj;
    *head = Nil;
    lp = list;
    while *lp != Nil {
        *expr = (**lp).c2rust_unnamed.c2rust_unnamed.car;
        *result = eval(root, env, expr);
        *head = cons(root, result, head);
        *lp = (**lp).c2rust_unnamed.c2rust_unnamed.cdr;
    }
    return reverse(*head);
}
unsafe extern "C" fn is_list(mut obj: *mut Obj) -> bool {
    return obj == Nil || (*obj).type_0 == TCELL as libc::c_int;
}
unsafe extern "C" fn apply_func(
    mut root: *mut libc::c_void,
    mut env: *mut *mut Obj,
    mut fn_0: *mut *mut Obj,
    mut args: *mut *mut Obj,
) -> *mut Obj {
    let mut root_ADD_ROOT_: [*mut libc::c_void; 5] = [0 as *mut libc::c_void; 5];
    root_ADD_ROOT_[0 as libc::c_int as usize] = root;
    let mut i: libc::c_int = 1 as libc::c_int;
    while i <= 3 as libc::c_int {
        root_ADD_ROOT_[i as usize] = 0 as *mut libc::c_void;
        i += 1;
        i;
    }
    root_ADD_ROOT_[(3 as libc::c_int + 1 as libc::c_int)
        as usize] = -(1 as libc::c_int) as *mut libc::c_void;
    root = root_ADD_ROOT_.as_mut_ptr() as *mut libc::c_void;
    let mut params: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(1 as libc::c_int as isize) as *mut *mut Obj;
    let mut newenv: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(2 as libc::c_int as isize) as *mut *mut Obj;
    let mut body: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(3 as libc::c_int as isize) as *mut *mut Obj;
    *params = (**fn_0).c2rust_unnamed.c2rust_unnamed_0.params;
    *newenv = (**fn_0).c2rust_unnamed.c2rust_unnamed_0.env;
    *newenv = push_env(root, newenv, params, args);
    *body = (**fn_0).c2rust_unnamed.c2rust_unnamed_0.body;
    return progn(root, newenv, body);
}
unsafe extern "C" fn apply(
    mut root: *mut libc::c_void,
    mut env: *mut *mut Obj,
    mut fn_0: *mut *mut Obj,
    mut args: *mut *mut Obj,
) -> *mut Obj {
    if !is_list(*args) {
        error(
            b"argument must be a list\0" as *const u8 as *const libc::c_char
                as *mut libc::c_char,
        );
    }
    if (**fn_0).type_0 == TPRIMITIVE as libc::c_int {
        return ((**fn_0).c2rust_unnamed.fn_0).unwrap()(root, env, args);
    }
    if (**fn_0).type_0 == TFUNCTION as libc::c_int {
        let mut root_ADD_ROOT_: [*mut libc::c_void; 3] = [0 as *mut libc::c_void; 3];
        root_ADD_ROOT_[0 as libc::c_int as usize] = root;
        let mut i: libc::c_int = 1 as libc::c_int;
        while i <= 1 as libc::c_int {
            root_ADD_ROOT_[i as usize] = 0 as *mut libc::c_void;
            i += 1;
            i;
        }
        root_ADD_ROOT_[(1 as libc::c_int + 1 as libc::c_int)
            as usize] = -(1 as libc::c_int) as *mut libc::c_void;
        root = root_ADD_ROOT_.as_mut_ptr() as *mut libc::c_void;
        let mut eargs: *mut *mut Obj = root_ADD_ROOT_
            .as_mut_ptr()
            .offset(1 as libc::c_int as isize) as *mut *mut Obj;
        *eargs = eval_list(root, env, args);
        return apply_func(root, env, fn_0, eargs);
    }
    error(b"not supported\0" as *const u8 as *const libc::c_char as *mut libc::c_char);
}
unsafe extern "C" fn find(mut env: *mut *mut Obj, mut sym: *mut Obj) -> *mut Obj {
    let mut p: *mut Obj = *env;
    while p != Nil {
        let mut cell: *mut Obj = (*p).c2rust_unnamed.c2rust_unnamed_1.vars;
        while cell != Nil {
            let mut bind: *mut Obj = (*cell).c2rust_unnamed.c2rust_unnamed.car;
            if sym == (*bind).c2rust_unnamed.c2rust_unnamed.car {
                return bind;
            }
            cell = (*cell).c2rust_unnamed.c2rust_unnamed.cdr;
        }
        p = (*p).c2rust_unnamed.c2rust_unnamed_1.up;
    }
    return 0 as *mut Obj;
}
unsafe extern "C" fn macroexpand(
    mut root: *mut libc::c_void,
    mut env: *mut *mut Obj,
    mut obj: *mut *mut Obj,
) -> *mut Obj {
    if (**obj).type_0 != TCELL as libc::c_int
        || (*(**obj).c2rust_unnamed.c2rust_unnamed.car).type_0 != TSYMBOL as libc::c_int
    {
        return *obj;
    }
    let mut root_ADD_ROOT_: [*mut libc::c_void; 5] = [0 as *mut libc::c_void; 5];
    root_ADD_ROOT_[0 as libc::c_int as usize] = root;
    let mut i: libc::c_int = 1 as libc::c_int;
    while i <= 3 as libc::c_int {
        root_ADD_ROOT_[i as usize] = 0 as *mut libc::c_void;
        i += 1;
        i;
    }
    root_ADD_ROOT_[(3 as libc::c_int + 1 as libc::c_int)
        as usize] = -(1 as libc::c_int) as *mut libc::c_void;
    root = root_ADD_ROOT_.as_mut_ptr() as *mut libc::c_void;
    let mut bind: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(1 as libc::c_int as isize) as *mut *mut Obj;
    let mut macro_0: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(2 as libc::c_int as isize) as *mut *mut Obj;
    let mut args: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(3 as libc::c_int as isize) as *mut *mut Obj;
    *bind = find(env, (**obj).c2rust_unnamed.c2rust_unnamed.car);
    if (*bind).is_null()
        || (*(**bind).c2rust_unnamed.c2rust_unnamed.cdr).type_0 != TMACRO as libc::c_int
    {
        return *obj;
    }
    *macro_0 = (**bind).c2rust_unnamed.c2rust_unnamed.cdr;
    *args = (**obj).c2rust_unnamed.c2rust_unnamed.cdr;
    return apply_func(root, env, macro_0, args);
}
unsafe extern "C" fn eval(
    mut root: *mut libc::c_void,
    mut env: *mut *mut Obj,
    mut obj: *mut *mut Obj,
) -> *mut Obj {
    match (**obj).type_0 {
        1 | 4 | 5 | 9 | 10 => return *obj,
        3 => {
            let mut bind: *mut Obj = find(env, *obj);
            if bind.is_null() {
                error(
                    b"Undefined symbol: %s\0" as *const u8 as *const libc::c_char
                        as *mut libc::c_char,
                    ((**obj).c2rust_unnamed.name).as_mut_ptr(),
                );
            }
            return (*bind).c2rust_unnamed.c2rust_unnamed.cdr;
        }
        2 => {
            let mut root_ADD_ROOT_: [*mut libc::c_void; 5] = [0 as *mut libc::c_void; 5];
            root_ADD_ROOT_[0 as libc::c_int as usize] = root;
            let mut i: libc::c_int = 1 as libc::c_int;
            while i <= 3 as libc::c_int {
                root_ADD_ROOT_[i as usize] = 0 as *mut libc::c_void;
                i += 1;
                i;
            }
            root_ADD_ROOT_[(3 as libc::c_int + 1 as libc::c_int)
                as usize] = -(1 as libc::c_int) as *mut libc::c_void;
            root = root_ADD_ROOT_.as_mut_ptr() as *mut libc::c_void;
            let mut fn_0: *mut *mut Obj = root_ADD_ROOT_
                .as_mut_ptr()
                .offset(1 as libc::c_int as isize) as *mut *mut Obj;
            let mut expanded: *mut *mut Obj = root_ADD_ROOT_
                .as_mut_ptr()
                .offset(2 as libc::c_int as isize) as *mut *mut Obj;
            let mut args: *mut *mut Obj = root_ADD_ROOT_
                .as_mut_ptr()
                .offset(3 as libc::c_int as isize) as *mut *mut Obj;
            *expanded = macroexpand(root, env, obj);
            if *expanded != *obj {
                return eval(root, env, expanded);
            }
            *fn_0 = (**obj).c2rust_unnamed.c2rust_unnamed.car;
            *fn_0 = eval(root, env, fn_0);
            *args = (**obj).c2rust_unnamed.c2rust_unnamed.cdr;
            if (**fn_0).type_0 != TPRIMITIVE as libc::c_int
                && (**fn_0).type_0 != TFUNCTION as libc::c_int
            {
                error(
                    b"The head of a list must be a function\0" as *const u8
                        as *const libc::c_char as *mut libc::c_char,
                );
            }
            return apply(root, env, fn_0, args);
        }
        _ => {
            error(
                b"Bug: eval: Unknown tag type: %d\0" as *const u8 as *const libc::c_char
                    as *mut libc::c_char,
                (**obj).type_0,
            );
        }
    };
}
unsafe extern "C" fn prim_quote(
    mut root: *mut libc::c_void,
    mut env: *mut *mut Obj,
    mut list: *mut *mut Obj,
) -> *mut Obj {
    if length(*list) != 1 as libc::c_int {
        error(
            b"Malformed quote\0" as *const u8 as *const libc::c_char as *mut libc::c_char,
        );
    }
    return (**list).c2rust_unnamed.c2rust_unnamed.car;
}
unsafe extern "C" fn prim_cons(
    mut root: *mut libc::c_void,
    mut env: *mut *mut Obj,
    mut list: *mut *mut Obj,
) -> *mut Obj {
    if length(*list) != 2 as libc::c_int {
        error(
            b"Malformed cons\0" as *const u8 as *const libc::c_char as *mut libc::c_char,
        );
    }
    let mut cell: *mut Obj = eval_list(root, env, list);
    (*cell)
        .c2rust_unnamed
        .c2rust_unnamed
        .cdr = (*(*cell).c2rust_unnamed.c2rust_unnamed.cdr)
        .c2rust_unnamed
        .c2rust_unnamed
        .car;
    return cell;
}
unsafe extern "C" fn prim_car(
    mut root: *mut libc::c_void,
    mut env: *mut *mut Obj,
    mut list: *mut *mut Obj,
) -> *mut Obj {
    let mut args: *mut Obj = eval_list(root, env, list);
    if (*(*args).c2rust_unnamed.c2rust_unnamed.car).type_0 != TCELL as libc::c_int
        || (*args).c2rust_unnamed.c2rust_unnamed.cdr != Nil
    {
        error(
            b"Malformed car\0" as *const u8 as *const libc::c_char as *mut libc::c_char,
        );
    }
    return (*(*args).c2rust_unnamed.c2rust_unnamed.car)
        .c2rust_unnamed
        .c2rust_unnamed
        .car;
}
unsafe extern "C" fn prim_cdr(
    mut root: *mut libc::c_void,
    mut env: *mut *mut Obj,
    mut list: *mut *mut Obj,
) -> *mut Obj {
    let mut args: *mut Obj = eval_list(root, env, list);
    if (*(*args).c2rust_unnamed.c2rust_unnamed.car).type_0 != TCELL as libc::c_int
        || (*args).c2rust_unnamed.c2rust_unnamed.cdr != Nil
    {
        error(
            b"Malformed cdr\0" as *const u8 as *const libc::c_char as *mut libc::c_char,
        );
    }
    return (*(*args).c2rust_unnamed.c2rust_unnamed.car)
        .c2rust_unnamed
        .c2rust_unnamed
        .cdr;
}
unsafe extern "C" fn prim_setq(
    mut root: *mut libc::c_void,
    mut env: *mut *mut Obj,
    mut list: *mut *mut Obj,
) -> *mut Obj {
    if length(*list) != 2 as libc::c_int
        || (*(**list).c2rust_unnamed.c2rust_unnamed.car).type_0 != TSYMBOL as libc::c_int
    {
        error(
            b"Malformed setq\0" as *const u8 as *const libc::c_char as *mut libc::c_char,
        );
    }
    let mut root_ADD_ROOT_: [*mut libc::c_void; 4] = [0 as *mut libc::c_void; 4];
    root_ADD_ROOT_[0 as libc::c_int as usize] = root;
    let mut i: libc::c_int = 1 as libc::c_int;
    while i <= 2 as libc::c_int {
        root_ADD_ROOT_[i as usize] = 0 as *mut libc::c_void;
        i += 1;
        i;
    }
    root_ADD_ROOT_[(2 as libc::c_int + 1 as libc::c_int)
        as usize] = -(1 as libc::c_int) as *mut libc::c_void;
    root = root_ADD_ROOT_.as_mut_ptr() as *mut libc::c_void;
    let mut bind: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(1 as libc::c_int as isize) as *mut *mut Obj;
    let mut value: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(2 as libc::c_int as isize) as *mut *mut Obj;
    *bind = find(env, (**list).c2rust_unnamed.c2rust_unnamed.car);
    if (*bind).is_null() {
        error(
            b"Unbound variable %s\0" as *const u8 as *const libc::c_char
                as *mut libc::c_char,
            ((*(**list).c2rust_unnamed.c2rust_unnamed.car).c2rust_unnamed.name)
                .as_mut_ptr(),
        );
    }
    *value = (*(**list).c2rust_unnamed.c2rust_unnamed.cdr)
        .c2rust_unnamed
        .c2rust_unnamed
        .car;
    *value = eval(root, env, value);
    (**bind).c2rust_unnamed.c2rust_unnamed.cdr = *value;
    return *value;
}
unsafe extern "C" fn prim_setcar(
    mut root: *mut libc::c_void,
    mut env: *mut *mut Obj,
    mut list: *mut *mut Obj,
) -> *mut Obj {
    let mut root_ADD_ROOT_: [*mut libc::c_void; 3] = [0 as *mut libc::c_void; 3];
    root_ADD_ROOT_[0 as libc::c_int as usize] = root;
    let mut i: libc::c_int = 1 as libc::c_int;
    while i <= 1 as libc::c_int {
        root_ADD_ROOT_[i as usize] = 0 as *mut libc::c_void;
        i += 1;
        i;
    }
    root_ADD_ROOT_[(1 as libc::c_int + 1 as libc::c_int)
        as usize] = -(1 as libc::c_int) as *mut libc::c_void;
    root = root_ADD_ROOT_.as_mut_ptr() as *mut libc::c_void;
    let mut args: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(1 as libc::c_int as isize) as *mut *mut Obj;
    *args = eval_list(root, env, list);
    if length(*args) != 2 as libc::c_int
        || (*(**args).c2rust_unnamed.c2rust_unnamed.car).type_0 != TCELL as libc::c_int
    {
        error(
            b"Malformed setcar\0" as *const u8 as *const libc::c_char
                as *mut libc::c_char,
        );
    }
    (*(**args).c2rust_unnamed.c2rust_unnamed.car)
        .c2rust_unnamed
        .c2rust_unnamed
        .car = (*(**args).c2rust_unnamed.c2rust_unnamed.cdr)
        .c2rust_unnamed
        .c2rust_unnamed
        .car;
    return (**args).c2rust_unnamed.c2rust_unnamed.car;
}
unsafe extern "C" fn prim_while(
    mut root: *mut libc::c_void,
    mut env: *mut *mut Obj,
    mut list: *mut *mut Obj,
) -> *mut Obj {
    if length(*list) < 2 as libc::c_int {
        error(
            b"Malformed while\0" as *const u8 as *const libc::c_char as *mut libc::c_char,
        );
    }
    let mut root_ADD_ROOT_: [*mut libc::c_void; 4] = [0 as *mut libc::c_void; 4];
    root_ADD_ROOT_[0 as libc::c_int as usize] = root;
    let mut i: libc::c_int = 1 as libc::c_int;
    while i <= 2 as libc::c_int {
        root_ADD_ROOT_[i as usize] = 0 as *mut libc::c_void;
        i += 1;
        i;
    }
    root_ADD_ROOT_[(2 as libc::c_int + 1 as libc::c_int)
        as usize] = -(1 as libc::c_int) as *mut libc::c_void;
    root = root_ADD_ROOT_.as_mut_ptr() as *mut libc::c_void;
    let mut cond: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(1 as libc::c_int as isize) as *mut *mut Obj;
    let mut exprs: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(2 as libc::c_int as isize) as *mut *mut Obj;
    *cond = (**list).c2rust_unnamed.c2rust_unnamed.car;
    while eval(root, env, cond) != Nil {
        *exprs = (**list).c2rust_unnamed.c2rust_unnamed.cdr;
        eval_list(root, env, exprs);
    }
    return Nil;
}
unsafe extern "C" fn prim_gensym(
    mut root: *mut libc::c_void,
    mut env: *mut *mut Obj,
    mut list: *mut *mut Obj,
) -> *mut Obj {
    static mut count: libc::c_int = 0 as libc::c_int;
    let mut buf: [libc::c_char; 10] = [0; 10];
    let fresh2 = count;
    count = count + 1;
    snprintf(
        buf.as_mut_ptr(),
        ::std::mem::size_of::<[libc::c_char; 10]>() as libc::c_ulong,
        b"G__%d\0" as *const u8 as *const libc::c_char,
        fresh2,
    );
    return make_symbol(root, buf.as_mut_ptr());
}
unsafe extern "C" fn prim_plus(
    mut root: *mut libc::c_void,
    mut env: *mut *mut Obj,
    mut list: *mut *mut Obj,
) -> *mut Obj {
    let mut sum: libc::c_int = 0 as libc::c_int;
    let mut args: *mut Obj = eval_list(root, env, list);
    while args != Nil {
        if (*(*args).c2rust_unnamed.c2rust_unnamed.car).type_0 != TINT as libc::c_int {
            error(
                b"+ takes only numbers\0" as *const u8 as *const libc::c_char
                    as *mut libc::c_char,
            );
        }
        sum += (*(*args).c2rust_unnamed.c2rust_unnamed.car).c2rust_unnamed.value;
        args = (*args).c2rust_unnamed.c2rust_unnamed.cdr;
    }
    return make_int(root, sum);
}
unsafe extern "C" fn prim_minus(
    mut root: *mut libc::c_void,
    mut env: *mut *mut Obj,
    mut list: *mut *mut Obj,
) -> *mut Obj {
    let mut args: *mut Obj = eval_list(root, env, list);
    let mut p: *mut Obj = args;
    while p != Nil {
        if (*(*p).c2rust_unnamed.c2rust_unnamed.car).type_0 != TINT as libc::c_int {
            error(
                b"- takes only numbers\0" as *const u8 as *const libc::c_char
                    as *mut libc::c_char,
            );
        }
        p = (*p).c2rust_unnamed.c2rust_unnamed.cdr;
    }
    if (*args).c2rust_unnamed.c2rust_unnamed.cdr == Nil {
        return make_int(
            root,
            -(*(*args).c2rust_unnamed.c2rust_unnamed.car).c2rust_unnamed.value,
        );
    }
    let mut r: libc::c_int = (*(*args).c2rust_unnamed.c2rust_unnamed.car)
        .c2rust_unnamed
        .value;
    let mut p_0: *mut Obj = (*args).c2rust_unnamed.c2rust_unnamed.cdr;
    while p_0 != Nil {
        r -= (*(*p_0).c2rust_unnamed.c2rust_unnamed.car).c2rust_unnamed.value;
        p_0 = (*p_0).c2rust_unnamed.c2rust_unnamed.cdr;
    }
    return make_int(root, r);
}
unsafe extern "C" fn prim_lt(
    mut root: *mut libc::c_void,
    mut env: *mut *mut Obj,
    mut list: *mut *mut Obj,
) -> *mut Obj {
    let mut args: *mut Obj = eval_list(root, env, list);
    if length(args) != 2 as libc::c_int {
        error(b"malformed <\0" as *const u8 as *const libc::c_char as *mut libc::c_char);
    }
    let mut x: *mut Obj = (*args).c2rust_unnamed.c2rust_unnamed.car;
    let mut y: *mut Obj = (*(*args).c2rust_unnamed.c2rust_unnamed.cdr)
        .c2rust_unnamed
        .c2rust_unnamed
        .car;
    if (*x).type_0 != TINT as libc::c_int || (*y).type_0 != TINT as libc::c_int {
        error(
            b"< takes only numbers\0" as *const u8 as *const libc::c_char
                as *mut libc::c_char,
        );
    }
    return if (*x).c2rust_unnamed.value < (*y).c2rust_unnamed.value {
        True
    } else {
        Nil
    };
}
unsafe extern "C" fn handle_function(
    mut root: *mut libc::c_void,
    mut env: *mut *mut Obj,
    mut list: *mut *mut Obj,
    mut type_0: libc::c_int,
) -> *mut Obj {
    if (**list).type_0 != TCELL as libc::c_int
        || !is_list((**list).c2rust_unnamed.c2rust_unnamed.car)
        || (*(**list).c2rust_unnamed.c2rust_unnamed.cdr).type_0 != TCELL as libc::c_int
    {
        error(
            b"Malformed lambda\0" as *const u8 as *const libc::c_char
                as *mut libc::c_char,
        );
    }
    let mut p: *mut Obj = (**list).c2rust_unnamed.c2rust_unnamed.car;
    while (*p).type_0 == TCELL as libc::c_int {
        if (*(*p).c2rust_unnamed.c2rust_unnamed.car).type_0 != TSYMBOL as libc::c_int {
            error(
                b"Parameter must be a symbol\0" as *const u8 as *const libc::c_char
                    as *mut libc::c_char,
            );
        }
        p = (*p).c2rust_unnamed.c2rust_unnamed.cdr;
    }
    if p != Nil && (*p).type_0 != TSYMBOL as libc::c_int {
        error(
            b"Parameter must be a symbol\0" as *const u8 as *const libc::c_char
                as *mut libc::c_char,
        );
    }
    let mut root_ADD_ROOT_: [*mut libc::c_void; 4] = [0 as *mut libc::c_void; 4];
    root_ADD_ROOT_[0 as libc::c_int as usize] = root;
    let mut i: libc::c_int = 1 as libc::c_int;
    while i <= 2 as libc::c_int {
        root_ADD_ROOT_[i as usize] = 0 as *mut libc::c_void;
        i += 1;
        i;
    }
    root_ADD_ROOT_[(2 as libc::c_int + 1 as libc::c_int)
        as usize] = -(1 as libc::c_int) as *mut libc::c_void;
    root = root_ADD_ROOT_.as_mut_ptr() as *mut libc::c_void;
    let mut params: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(1 as libc::c_int as isize) as *mut *mut Obj;
    let mut body: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(2 as libc::c_int as isize) as *mut *mut Obj;
    *params = (**list).c2rust_unnamed.c2rust_unnamed.car;
    *body = (**list).c2rust_unnamed.c2rust_unnamed.cdr;
    return make_function(root, env, type_0, params, body);
}
unsafe extern "C" fn prim_lambda(
    mut root: *mut libc::c_void,
    mut env: *mut *mut Obj,
    mut list: *mut *mut Obj,
) -> *mut Obj {
    return handle_function(root, env, list, TFUNCTION as libc::c_int);
}
unsafe extern "C" fn handle_defun(
    mut root: *mut libc::c_void,
    mut env: *mut *mut Obj,
    mut list: *mut *mut Obj,
    mut type_0: libc::c_int,
) -> *mut Obj {
    if (*(**list).c2rust_unnamed.c2rust_unnamed.car).type_0 != TSYMBOL as libc::c_int
        || (*(**list).c2rust_unnamed.c2rust_unnamed.cdr).type_0 != TCELL as libc::c_int
    {
        error(
            b"Malformed defun\0" as *const u8 as *const libc::c_char as *mut libc::c_char,
        );
    }
    let mut root_ADD_ROOT_: [*mut libc::c_void; 5] = [0 as *mut libc::c_void; 5];
    root_ADD_ROOT_[0 as libc::c_int as usize] = root;
    let mut i: libc::c_int = 1 as libc::c_int;
    while i <= 3 as libc::c_int {
        root_ADD_ROOT_[i as usize] = 0 as *mut libc::c_void;
        i += 1;
        i;
    }
    root_ADD_ROOT_[(3 as libc::c_int + 1 as libc::c_int)
        as usize] = -(1 as libc::c_int) as *mut libc::c_void;
    root = root_ADD_ROOT_.as_mut_ptr() as *mut libc::c_void;
    let mut fn_0: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(1 as libc::c_int as isize) as *mut *mut Obj;
    let mut sym: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(2 as libc::c_int as isize) as *mut *mut Obj;
    let mut rest: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(3 as libc::c_int as isize) as *mut *mut Obj;
    *sym = (**list).c2rust_unnamed.c2rust_unnamed.car;
    *rest = (**list).c2rust_unnamed.c2rust_unnamed.cdr;
    *fn_0 = handle_function(root, env, rest, type_0);
    add_variable(root, env, sym, fn_0);
    return *fn_0;
}
unsafe extern "C" fn prim_defun(
    mut root: *mut libc::c_void,
    mut env: *mut *mut Obj,
    mut list: *mut *mut Obj,
) -> *mut Obj {
    return handle_defun(root, env, list, TFUNCTION as libc::c_int);
}
unsafe extern "C" fn prim_define(
    mut root: *mut libc::c_void,
    mut env: *mut *mut Obj,
    mut list: *mut *mut Obj,
) -> *mut Obj {
    if length(*list) != 2 as libc::c_int
        || (*(**list).c2rust_unnamed.c2rust_unnamed.car).type_0 != TSYMBOL as libc::c_int
    {
        error(
            b"Malformed define\0" as *const u8 as *const libc::c_char
                as *mut libc::c_char,
        );
    }
    let mut root_ADD_ROOT_: [*mut libc::c_void; 4] = [0 as *mut libc::c_void; 4];
    root_ADD_ROOT_[0 as libc::c_int as usize] = root;
    let mut i: libc::c_int = 1 as libc::c_int;
    while i <= 2 as libc::c_int {
        root_ADD_ROOT_[i as usize] = 0 as *mut libc::c_void;
        i += 1;
        i;
    }
    root_ADD_ROOT_[(2 as libc::c_int + 1 as libc::c_int)
        as usize] = -(1 as libc::c_int) as *mut libc::c_void;
    root = root_ADD_ROOT_.as_mut_ptr() as *mut libc::c_void;
    let mut sym: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(1 as libc::c_int as isize) as *mut *mut Obj;
    let mut value: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(2 as libc::c_int as isize) as *mut *mut Obj;
    *sym = (**list).c2rust_unnamed.c2rust_unnamed.car;
    *value = (*(**list).c2rust_unnamed.c2rust_unnamed.cdr)
        .c2rust_unnamed
        .c2rust_unnamed
        .car;
    *value = eval(root, env, value);
    add_variable(root, env, sym, value);
    return *value;
}
unsafe extern "C" fn prim_defmacro(
    mut root: *mut libc::c_void,
    mut env: *mut *mut Obj,
    mut list: *mut *mut Obj,
) -> *mut Obj {
    return handle_defun(root, env, list, TMACRO as libc::c_int);
}
unsafe extern "C" fn prim_macroexpand(
    mut root: *mut libc::c_void,
    mut env: *mut *mut Obj,
    mut list: *mut *mut Obj,
) -> *mut Obj {
    if length(*list) != 1 as libc::c_int {
        error(
            b"Malformed macroexpand\0" as *const u8 as *const libc::c_char
                as *mut libc::c_char,
        );
    }
    let mut root_ADD_ROOT_: [*mut libc::c_void; 3] = [0 as *mut libc::c_void; 3];
    root_ADD_ROOT_[0 as libc::c_int as usize] = root;
    let mut i: libc::c_int = 1 as libc::c_int;
    while i <= 1 as libc::c_int {
        root_ADD_ROOT_[i as usize] = 0 as *mut libc::c_void;
        i += 1;
        i;
    }
    root_ADD_ROOT_[(1 as libc::c_int + 1 as libc::c_int)
        as usize] = -(1 as libc::c_int) as *mut libc::c_void;
    root = root_ADD_ROOT_.as_mut_ptr() as *mut libc::c_void;
    let mut body: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(1 as libc::c_int as isize) as *mut *mut Obj;
    *body = (**list).c2rust_unnamed.c2rust_unnamed.car;
    return macroexpand(root, env, body);
}
unsafe extern "C" fn prim_println(
    mut root: *mut libc::c_void,
    mut env: *mut *mut Obj,
    mut list: *mut *mut Obj,
) -> *mut Obj {
    let mut root_ADD_ROOT_: [*mut libc::c_void; 3] = [0 as *mut libc::c_void; 3];
    root_ADD_ROOT_[0 as libc::c_int as usize] = root;
    let mut i: libc::c_int = 1 as libc::c_int;
    while i <= 1 as libc::c_int {
        root_ADD_ROOT_[i as usize] = 0 as *mut libc::c_void;
        i += 1;
        i;
    }
    root_ADD_ROOT_[(1 as libc::c_int + 1 as libc::c_int)
        as usize] = -(1 as libc::c_int) as *mut libc::c_void;
    root = root_ADD_ROOT_.as_mut_ptr() as *mut libc::c_void;
    let mut tmp: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(1 as libc::c_int as isize) as *mut *mut Obj;
    *tmp = (**list).c2rust_unnamed.c2rust_unnamed.car;
    print(eval(root, env, tmp));
    printf(b"\n\0" as *const u8 as *const libc::c_char);
    return Nil;
}
unsafe extern "C" fn prim_if(
    mut root: *mut libc::c_void,
    mut env: *mut *mut Obj,
    mut list: *mut *mut Obj,
) -> *mut Obj {
    if length(*list) < 2 as libc::c_int {
        error(
            b"Malformed if\0" as *const u8 as *const libc::c_char as *mut libc::c_char,
        );
    }
    let mut root_ADD_ROOT_: [*mut libc::c_void; 5] = [0 as *mut libc::c_void; 5];
    root_ADD_ROOT_[0 as libc::c_int as usize] = root;
    let mut i: libc::c_int = 1 as libc::c_int;
    while i <= 3 as libc::c_int {
        root_ADD_ROOT_[i as usize] = 0 as *mut libc::c_void;
        i += 1;
        i;
    }
    root_ADD_ROOT_[(3 as libc::c_int + 1 as libc::c_int)
        as usize] = -(1 as libc::c_int) as *mut libc::c_void;
    root = root_ADD_ROOT_.as_mut_ptr() as *mut libc::c_void;
    let mut cond: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(1 as libc::c_int as isize) as *mut *mut Obj;
    let mut then: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(2 as libc::c_int as isize) as *mut *mut Obj;
    let mut els: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(3 as libc::c_int as isize) as *mut *mut Obj;
    *cond = (**list).c2rust_unnamed.c2rust_unnamed.car;
    *cond = eval(root, env, cond);
    if *cond != Nil {
        *then = (*(**list).c2rust_unnamed.c2rust_unnamed.cdr)
            .c2rust_unnamed
            .c2rust_unnamed
            .car;
        return eval(root, env, then);
    }
    *els = (*(**list).c2rust_unnamed.c2rust_unnamed.cdr)
        .c2rust_unnamed
        .c2rust_unnamed
        .cdr;
    return if *els == Nil { Nil } else { progn(root, env, els) };
}
unsafe extern "C" fn prim_num_eq(
    mut root: *mut libc::c_void,
    mut env: *mut *mut Obj,
    mut list: *mut *mut Obj,
) -> *mut Obj {
    if length(*list) != 2 as libc::c_int {
        error(b"Malformed =\0" as *const u8 as *const libc::c_char as *mut libc::c_char);
    }
    let mut values: *mut Obj = eval_list(root, env, list);
    let mut x: *mut Obj = (*values).c2rust_unnamed.c2rust_unnamed.car;
    let mut y: *mut Obj = (*(*values).c2rust_unnamed.c2rust_unnamed.cdr)
        .c2rust_unnamed
        .c2rust_unnamed
        .car;
    if (*x).type_0 != TINT as libc::c_int || (*y).type_0 != TINT as libc::c_int {
        error(
            b"= only takes numbers\0" as *const u8 as *const libc::c_char
                as *mut libc::c_char,
        );
    }
    return if (*x).c2rust_unnamed.value == (*y).c2rust_unnamed.value {
        True
    } else {
        Nil
    };
}
unsafe extern "C" fn prim_eq(
    mut root: *mut libc::c_void,
    mut env: *mut *mut Obj,
    mut list: *mut *mut Obj,
) -> *mut Obj {
    if length(*list) != 2 as libc::c_int {
        error(
            b"Malformed eq\0" as *const u8 as *const libc::c_char as *mut libc::c_char,
        );
    }
    let mut values: *mut Obj = eval_list(root, env, list);
    return if (*values).c2rust_unnamed.c2rust_unnamed.car
        == (*(*values).c2rust_unnamed.c2rust_unnamed.cdr)
            .c2rust_unnamed
            .c2rust_unnamed
            .car
    {
        True
    } else {
        Nil
    };
}
unsafe extern "C" fn add_primitive(
    mut root: *mut libc::c_void,
    mut env: *mut *mut Obj,
    mut name: *mut libc::c_char,
    mut fn_0: Option::<Primitive>,
) {
    let mut root_ADD_ROOT_: [*mut libc::c_void; 4] = [0 as *mut libc::c_void; 4];
    root_ADD_ROOT_[0 as libc::c_int as usize] = root;
    let mut i: libc::c_int = 1 as libc::c_int;
    while i <= 2 as libc::c_int {
        root_ADD_ROOT_[i as usize] = 0 as *mut libc::c_void;
        i += 1;
        i;
    }
    root_ADD_ROOT_[(2 as libc::c_int + 1 as libc::c_int)
        as usize] = -(1 as libc::c_int) as *mut libc::c_void;
    root = root_ADD_ROOT_.as_mut_ptr() as *mut libc::c_void;
    let mut sym: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(1 as libc::c_int as isize) as *mut *mut Obj;
    let mut prim: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(2 as libc::c_int as isize) as *mut *mut Obj;
    *sym = intern(root, name);
    *prim = make_primitive(root, fn_0);
    add_variable(root, env, sym, prim);
}
unsafe extern "C" fn define_constants(
    mut root: *mut libc::c_void,
    mut env: *mut *mut Obj,
) {
    let mut root_ADD_ROOT_: [*mut libc::c_void; 3] = [0 as *mut libc::c_void; 3];
    root_ADD_ROOT_[0 as libc::c_int as usize] = root;
    let mut i: libc::c_int = 1 as libc::c_int;
    while i <= 1 as libc::c_int {
        root_ADD_ROOT_[i as usize] = 0 as *mut libc::c_void;
        i += 1;
        i;
    }
    root_ADD_ROOT_[(1 as libc::c_int + 1 as libc::c_int)
        as usize] = -(1 as libc::c_int) as *mut libc::c_void;
    root = root_ADD_ROOT_.as_mut_ptr() as *mut libc::c_void;
    let mut sym: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(1 as libc::c_int as isize) as *mut *mut Obj;
    *sym = intern(root, b"t\0" as *const u8 as *const libc::c_char as *mut libc::c_char);
    add_variable(root, env, sym, &mut True);
}
unsafe extern "C" fn define_primitives(
    mut root: *mut libc::c_void,
    mut env: *mut *mut Obj,
) {
    add_primitive(
        root,
        env,
        b"quote\0" as *const u8 as *const libc::c_char as *mut libc::c_char,
        Some(
            prim_quote
                as unsafe extern "C" fn(
                    *mut libc::c_void,
                    *mut *mut Obj,
                    *mut *mut Obj,
                ) -> *mut Obj,
        ),
    );
    add_primitive(
        root,
        env,
        b"cons\0" as *const u8 as *const libc::c_char as *mut libc::c_char,
        Some(
            prim_cons
                as unsafe extern "C" fn(
                    *mut libc::c_void,
                    *mut *mut Obj,
                    *mut *mut Obj,
                ) -> *mut Obj,
        ),
    );
    add_primitive(
        root,
        env,
        b"car\0" as *const u8 as *const libc::c_char as *mut libc::c_char,
        Some(
            prim_car
                as unsafe extern "C" fn(
                    *mut libc::c_void,
                    *mut *mut Obj,
                    *mut *mut Obj,
                ) -> *mut Obj,
        ),
    );
    add_primitive(
        root,
        env,
        b"cdr\0" as *const u8 as *const libc::c_char as *mut libc::c_char,
        Some(
            prim_cdr
                as unsafe extern "C" fn(
                    *mut libc::c_void,
                    *mut *mut Obj,
                    *mut *mut Obj,
                ) -> *mut Obj,
        ),
    );
    add_primitive(
        root,
        env,
        b"setq\0" as *const u8 as *const libc::c_char as *mut libc::c_char,
        Some(
            prim_setq
                as unsafe extern "C" fn(
                    *mut libc::c_void,
                    *mut *mut Obj,
                    *mut *mut Obj,
                ) -> *mut Obj,
        ),
    );
    add_primitive(
        root,
        env,
        b"setcar\0" as *const u8 as *const libc::c_char as *mut libc::c_char,
        Some(
            prim_setcar
                as unsafe extern "C" fn(
                    *mut libc::c_void,
                    *mut *mut Obj,
                    *mut *mut Obj,
                ) -> *mut Obj,
        ),
    );
    add_primitive(
        root,
        env,
        b"while\0" as *const u8 as *const libc::c_char as *mut libc::c_char,
        Some(
            prim_while
                as unsafe extern "C" fn(
                    *mut libc::c_void,
                    *mut *mut Obj,
                    *mut *mut Obj,
                ) -> *mut Obj,
        ),
    );
    add_primitive(
        root,
        env,
        b"gensym\0" as *const u8 as *const libc::c_char as *mut libc::c_char,
        Some(
            prim_gensym
                as unsafe extern "C" fn(
                    *mut libc::c_void,
                    *mut *mut Obj,
                    *mut *mut Obj,
                ) -> *mut Obj,
        ),
    );
    add_primitive(
        root,
        env,
        b"+\0" as *const u8 as *const libc::c_char as *mut libc::c_char,
        Some(
            prim_plus
                as unsafe extern "C" fn(
                    *mut libc::c_void,
                    *mut *mut Obj,
                    *mut *mut Obj,
                ) -> *mut Obj,
        ),
    );
    add_primitive(
        root,
        env,
        b"-\0" as *const u8 as *const libc::c_char as *mut libc::c_char,
        Some(
            prim_minus
                as unsafe extern "C" fn(
                    *mut libc::c_void,
                    *mut *mut Obj,
                    *mut *mut Obj,
                ) -> *mut Obj,
        ),
    );
    add_primitive(
        root,
        env,
        b"<\0" as *const u8 as *const libc::c_char as *mut libc::c_char,
        Some(
            prim_lt
                as unsafe extern "C" fn(
                    *mut libc::c_void,
                    *mut *mut Obj,
                    *mut *mut Obj,
                ) -> *mut Obj,
        ),
    );
    add_primitive(
        root,
        env,
        b"define\0" as *const u8 as *const libc::c_char as *mut libc::c_char,
        Some(
            prim_define
                as unsafe extern "C" fn(
                    *mut libc::c_void,
                    *mut *mut Obj,
                    *mut *mut Obj,
                ) -> *mut Obj,
        ),
    );
    add_primitive(
        root,
        env,
        b"defun\0" as *const u8 as *const libc::c_char as *mut libc::c_char,
        Some(
            prim_defun
                as unsafe extern "C" fn(
                    *mut libc::c_void,
                    *mut *mut Obj,
                    *mut *mut Obj,
                ) -> *mut Obj,
        ),
    );
    add_primitive(
        root,
        env,
        b"defmacro\0" as *const u8 as *const libc::c_char as *mut libc::c_char,
        Some(
            prim_defmacro
                as unsafe extern "C" fn(
                    *mut libc::c_void,
                    *mut *mut Obj,
                    *mut *mut Obj,
                ) -> *mut Obj,
        ),
    );
    add_primitive(
        root,
        env,
        b"macroexpand\0" as *const u8 as *const libc::c_char as *mut libc::c_char,
        Some(
            prim_macroexpand
                as unsafe extern "C" fn(
                    *mut libc::c_void,
                    *mut *mut Obj,
                    *mut *mut Obj,
                ) -> *mut Obj,
        ),
    );
    add_primitive(
        root,
        env,
        b"lambda\0" as *const u8 as *const libc::c_char as *mut libc::c_char,
        Some(
            prim_lambda
                as unsafe extern "C" fn(
                    *mut libc::c_void,
                    *mut *mut Obj,
                    *mut *mut Obj,
                ) -> *mut Obj,
        ),
    );
    add_primitive(
        root,
        env,
        b"if\0" as *const u8 as *const libc::c_char as *mut libc::c_char,
        Some(
            prim_if
                as unsafe extern "C" fn(
                    *mut libc::c_void,
                    *mut *mut Obj,
                    *mut *mut Obj,
                ) -> *mut Obj,
        ),
    );
    add_primitive(
        root,
        env,
        b"=\0" as *const u8 as *const libc::c_char as *mut libc::c_char,
        Some(
            prim_num_eq
                as unsafe extern "C" fn(
                    *mut libc::c_void,
                    *mut *mut Obj,
                    *mut *mut Obj,
                ) -> *mut Obj,
        ),
    );
    add_primitive(
        root,
        env,
        b"eq\0" as *const u8 as *const libc::c_char as *mut libc::c_char,
        Some(
            prim_eq
                as unsafe extern "C" fn(
                    *mut libc::c_void,
                    *mut *mut Obj,
                    *mut *mut Obj,
                ) -> *mut Obj,
        ),
    );
    add_primitive(
        root,
        env,
        b"println\0" as *const u8 as *const libc::c_char as *mut libc::c_char,
        Some(
            prim_println
                as unsafe extern "C" fn(
                    *mut libc::c_void,
                    *mut *mut Obj,
                    *mut *mut Obj,
                ) -> *mut Obj,
        ),
    );
}
unsafe extern "C" fn getEnvFlag(mut name: *mut libc::c_char) -> bool {
    let mut val: *mut libc::c_char = getenv(name);
    return !val.is_null() && *val.offset(0 as libc::c_int as isize) as libc::c_int != 0;
}
unsafe fn main_0(
    mut argc: libc::c_int,
    mut argv: *mut *mut libc::c_char,
) -> libc::c_int {
    debug_gc = getEnvFlag(
        b"MINILISP_DEBUG_GC\0" as *const u8 as *const libc::c_char as *mut libc::c_char,
    );
    always_gc = getEnvFlag(
        b"MINILISP_ALWAYS_GC\0" as *const u8 as *const libc::c_char as *mut libc::c_char,
    );
    memory = alloc_semispace();
    Symbols = Nil;
    let mut root: *mut libc::c_void = 0 as *mut libc::c_void;
    let mut root_ADD_ROOT_: [*mut libc::c_void; 4] = [0 as *mut libc::c_void; 4];
    root_ADD_ROOT_[0 as libc::c_int as usize] = root;
    let mut i: libc::c_int = 1 as libc::c_int;
    while i <= 2 as libc::c_int {
        root_ADD_ROOT_[i as usize] = 0 as *mut libc::c_void;
        i += 1;
        i;
    }
    root_ADD_ROOT_[(2 as libc::c_int + 1 as libc::c_int)
        as usize] = -(1 as libc::c_int) as *mut libc::c_void;
    root = root_ADD_ROOT_.as_mut_ptr() as *mut libc::c_void;
    let mut env: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(1 as libc::c_int as isize) as *mut *mut Obj;
    let mut expr: *mut *mut Obj = root_ADD_ROOT_
        .as_mut_ptr()
        .offset(2 as libc::c_int as isize) as *mut *mut Obj;
    *env = make_env(root, &mut Nil, &mut Nil);
    define_constants(root, env);
    define_primitives(root, env);
    loop {
        *expr = read_expr(root);
        if (*expr).is_null() {
            return 0 as libc::c_int;
        }
        if *expr == Cparen {
            error(
                b"Stray close parenthesis\0" as *const u8 as *const libc::c_char
                    as *mut libc::c_char,
            );
        }
        if *expr == Dot {
            error(
                b"Stray dot\0" as *const u8 as *const libc::c_char as *mut libc::c_char,
            );
        }
        print(eval(root, env, expr));
        printf(b"\n\0" as *const u8 as *const libc::c_char);
    };
}
pub fn main() {
    let mut args: Vec::<*mut libc::c_char> = Vec::new();
    for arg in ::std::env::args_os() {
        args.push(
            (::std::ffi::CString::new(
                ::std::os::unix::ffi::OsStrExt::as_bytes(arg.as_os_str()),
            ))
                .unwrap()
                .into_raw(),
        );
    }
    args.push(::std::ptr::null_mut());
    unsafe {
        ::std::process::exit(
            main_0(
                (args.len() - 1) as libc::c_int,
                args.as_mut_ptr() as *mut *mut libc::c_char,
            ) as i32,
        )
    }
}
