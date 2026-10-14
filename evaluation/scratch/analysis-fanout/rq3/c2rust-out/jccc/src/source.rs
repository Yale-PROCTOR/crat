extern "C" {
    pub type _IO_wide_data;
    pub type _IO_codecvt;
    pub type _IO_marker;
    fn __assert_fail(
        __assertion: *const ::core::ffi::c_char,
        __file: *const ::core::ffi::c_char,
        __line: ::core::ffi::c_uint,
        __function: *const ::core::ffi::c_char,
    ) -> !;
    static mut stdout: *mut FILE;
    static mut stderr: *mut FILE;
    fn fclose(__stream: *mut FILE) -> ::core::ffi::c_int;
    fn fflush(__stream: *mut FILE) -> ::core::ffi::c_int;
    fn fopen(
        __filename: *const ::core::ffi::c_char,
        __modes: *const ::core::ffi::c_char,
    ) -> *mut FILE;
    fn fprintf(
        __stream: *mut FILE,
        __format: *const ::core::ffi::c_char,
        ...
    ) -> ::core::ffi::c_int;
    fn printf(__format: *const ::core::ffi::c_char, ...) -> ::core::ffi::c_int;
    fn sprintf(
        __s: *mut ::core::ffi::c_char,
        __format: *const ::core::ffi::c_char,
        ...
    ) -> ::core::ffi::c_int;
    fn getc(__stream: *mut FILE) -> ::core::ffi::c_int;
    fn ungetc(__c: ::core::ffi::c_int, __stream: *mut FILE) -> ::core::ffi::c_int;
    fn atoi(__nptr: *const ::core::ffi::c_char) -> ::core::ffi::c_int;
    fn malloc(__size: size_t) -> *mut ::core::ffi::c_void;
    fn calloc(__nmemb: size_t, __size: size_t) -> *mut ::core::ffi::c_void;
    fn free(__ptr: *mut ::core::ffi::c_void);
    fn memcpy(
        __dest: *mut ::core::ffi::c_void,
        __src: *const ::core::ffi::c_void,
        __n: size_t,
    ) -> *mut ::core::ffi::c_void;
    fn memset(
        __s: *mut ::core::ffi::c_void,
        __c: ::core::ffi::c_int,
        __n: size_t,
    ) -> *mut ::core::ffi::c_void;
    fn strcpy(
        __dest: *mut ::core::ffi::c_char,
        __src: *const ::core::ffi::c_char,
    ) -> *mut ::core::ffi::c_char;
    fn strcmp(
        __s1: *const ::core::ffi::c_char,
        __s2: *const ::core::ffi::c_char,
    ) -> ::core::ffi::c_int;
    fn strlen(__s: *const ::core::ffi::c_char) -> size_t;
}
pub type __uint32_t = u32;
pub type __uint64_t = u64;
pub type __off_t = ::core::ffi::c_long;
pub type __off64_t = ::core::ffi::c_long;
pub type uint32_t = __uint32_t;
pub type uint64_t = __uint64_t;
pub type size_t = usize;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct _IO_FILE {
    pub _flags: ::core::ffi::c_int,
    pub _IO_read_ptr: *mut ::core::ffi::c_char,
    pub _IO_read_end: *mut ::core::ffi::c_char,
    pub _IO_read_base: *mut ::core::ffi::c_char,
    pub _IO_write_base: *mut ::core::ffi::c_char,
    pub _IO_write_ptr: *mut ::core::ffi::c_char,
    pub _IO_write_end: *mut ::core::ffi::c_char,
    pub _IO_buf_base: *mut ::core::ffi::c_char,
    pub _IO_buf_end: *mut ::core::ffi::c_char,
    pub _IO_save_base: *mut ::core::ffi::c_char,
    pub _IO_backup_base: *mut ::core::ffi::c_char,
    pub _IO_save_end: *mut ::core::ffi::c_char,
    pub _markers: *mut _IO_marker,
    pub _chain: *mut _IO_FILE,
    pub _fileno: ::core::ffi::c_int,
    pub _flags2: ::core::ffi::c_int,
    pub _old_offset: __off_t,
    pub _cur_column: ::core::ffi::c_ushort,
    pub _vtable_offset: ::core::ffi::c_schar,
    pub _shortbuf: [::core::ffi::c_char; 1],
    pub _lock: *mut ::core::ffi::c_void,
    pub _offset: __off64_t,
    pub _codecvt: *mut _IO_codecvt,
    pub _wide_data: *mut _IO_wide_data,
    pub _freeres_list: *mut _IO_FILE,
    pub _freeres_buf: *mut ::core::ffi::c_void,
    pub __pad5: size_t,
    pub _mode: ::core::ffi::c_int,
    pub _unused2: [::core::ffi::c_char; 20],
}
pub type _IO_lock_t = ();
pub type FILE = _IO_FILE;
pub type TokenType = ::core::ffi::c_uint;
pub const TT_WHILE: TokenType = 84;
pub const TT_VOLATILE: TokenType = 83;
pub const TT_VOID: TokenType = 82;
pub const TT_UNION: TokenType = 81;
pub const TT_UNSIGNED: TokenType = 80;
pub const TT_TYPEDEF: TokenType = 79;
pub const TT_SIZEOF: TokenType = 78;
pub const TT_STRUCT: TokenType = 77;
pub const TT_SIGNED: TokenType = 76;
pub const TT_SHORT: TokenType = 75;
pub const TT_SWITCH: TokenType = 74;
pub const TT_STATIC: TokenType = 73;
pub const TT_REGISTER: TokenType = 72;
pub const TT_RETURN: TokenType = 71;
pub const TT_LONG: TokenType = 70;
pub const TT_INT: TokenType = 69;
pub const TT_IF: TokenType = 68;
pub const TT_GOTO: TokenType = 67;
pub const TT_FOR: TokenType = 66;
pub const TT_FLOAT: TokenType = 65;
pub const TT_EXTERN: TokenType = 64;
pub const TT_ELSE: TokenType = 63;
pub const TT_ENUM: TokenType = 62;
pub const TT_DEFAULT: TokenType = 61;
pub const TT_DO: TokenType = 60;
pub const TT_DOUBLE: TokenType = 59;
pub const TT_CONTINUE: TokenType = 58;
pub const TT_CASE: TokenType = 57;
pub const TT_CONST: TokenType = 56;
pub const TT_CHAR: TokenType = 55;
pub const TT_BREAK: TokenType = 54;
pub const TT_AUTO: TokenType = 53;
pub const TT_RIGHTSHIFTEQUALS: TokenType = 52;
pub const TT_LEFTSHIFTEQUALS: TokenType = 51;
pub const TT_POINT: TokenType = 50;
pub const TT_XOREQ: TokenType = 49;
pub const TT_XOR: TokenType = 48;
pub const TT_NOTEQ: TokenType = 47;
pub const TT_EQUALS: TokenType = 46;
pub const TT_BNOT: TokenType = 45;
pub const TT_LNOT: TokenType = 44;
pub const TT_RIGHTSHIFT: TokenType = 43;
pub const TT_LEFTSHIFT: TokenType = 42;
pub const TT_GREATEREQ: TokenType = 41;
pub const TT_LESSEQ: TokenType = 40;
pub const TT_LESS: TokenType = 39;
pub const TT_GREATER: TokenType = 38;
pub const TT_LOREQ: TokenType = 37;
pub const TT_LANDEQ: TokenType = 36;
pub const TT_BOREQ: TokenType = 35;
pub const TT_BANDEQ: TokenType = 34;
pub const TT_MODEQ: TokenType = 33;
pub const TT_MULEQ: TokenType = 32;
pub const TT_DIVEQ: TokenType = 31;
pub const TT_MINUSMINUS: TokenType = 30;
pub const TT_PLUSPLUS: TokenType = 29;
pub const TT_INC: TokenType = 28;
pub const TT_DEC: TokenType = 27;
pub const TT_LOR: TokenType = 26;
pub const TT_BOR: TokenType = 25;
pub const TT_LAND: TokenType = 24;
pub const TT_BAND: TokenType = 23;
pub const TT_MOD: TokenType = 22;
pub const TT_COLON: TokenType = 21;
pub const TT_ASSIGN: TokenType = 20;
pub const TT_SLASH: TokenType = 19;
pub const TT_STAR: TokenType = 18;
pub const TT_PLUS: TokenType = 17;
pub const TT_MINUS: TokenType = 16;
pub const TT_QMARK: TokenType = 15;
pub const TT_COMMA: TokenType = 14;
pub const TT_PERIOD: TokenType = 13;
pub const TT_POUND: TokenType = 12;
pub const TT_NEWLINE: TokenType = 11;
pub const TT_EOF: TokenType = 10;
pub const TT_NO_TOKEN: TokenType = 9;
pub const TT_SEMI: TokenType = 8;
pub const TT_CBRACKET: TokenType = 7;
pub const TT_OBRACKET: TokenType = 6;
pub const TT_CBRACE: TokenType = 5;
pub const TT_OBRACE: TokenType = 4;
pub const TT_CPAREN: TokenType = 3;
pub const TT_OPAREN: TokenType = 2;
pub const TT_IDENTIFIER: TokenType = 1;
pub const TT_LITERAL: TokenType = 0;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct Token {
    pub type_0: TokenType,
    pub contents: [::core::ffi::c_char; 256],
    pub length: ::core::ffi::c_uint,
    pub source_file: [::core::ffi::c_char; 256],
    pub line: ::core::ffi::c_int,
    pub column: ::core::ffi::c_int,
}
pub type Op = ::core::ffi::c_uint;
pub const OP_NOP: Op = 3;
pub const OP_MOV: Op = 2;
pub const OP_SUB: Op = 1;
pub const OP_ADD: Op = 0;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct Lexer {
    pub fp: *mut FILE,
    pub current_file: [::core::ffi::c_char; 256],
    pub buffer: [::core::ffi::c_char; 1],
    pub position: ::core::ffi::c_long,
    pub last_column: ::core::ffi::c_int,
    pub column: ::core::ffi::c_int,
    pub line: ::core::ffi::c_int,
    pub unlexed: [Token; 5],
    pub unlexed_count: ::core::ffi::c_uint,
}
#[derive(Copy, Clone)]
#[repr(C)]
pub struct List {
    pub head: *mut ListBlock,
    pub tail: *mut ListBlock,
    pub blocksize: ::core::ffi::c_int,
}
#[derive(Copy, Clone)]
#[repr(C)]
pub struct ListBlock {
    pub array: *mut ::core::ffi::c_int,
    pub size: ::core::ffi::c_int,
    pub full: ::core::ffi::c_int,
    pub next: *mut ListBlock,
}
pub type NodeType = ::core::ffi::c_uint;
pub const NT_LITERAL: NodeType = 6;
pub const NT_FUNCCALL: NodeType = 5;
pub const NT_FUNCDECL: NodeType = 4;
pub const NT_RETURN_STMT: NodeType = 3;
pub const NT_BLOCK_STMT: NodeType = 2;
pub const NT_EXPR: NodeType = 1;
pub const NT_STMT: NodeType = 0;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct BlockStatement {
    pub stmts: *mut List,
}
#[derive(Copy, Clone)]
#[repr(C)]
pub struct FunctionDeclaration {
    pub body: BlockStatement,
    pub name: [::core::ffi::c_char; 256],
}
#[derive(Copy, Clone)]
#[repr(C)]
pub struct FunctionCall {
    pub name: [::core::ffi::c_char; 256],
}
#[derive(Copy, Clone)]
#[repr(C)]
pub struct Expression {
    pub u: C2RustUnnamed,
    pub type_0: NodeType,
}
#[derive(Copy, Clone)]
#[repr(C)]
pub union C2RustUnnamed {
    pub fc: FunctionCall,
    pub literal: [::core::ffi::c_char; 256],
}
#[derive(Copy, Clone)]
#[repr(C)]
pub struct ConcreteFileTree {
    pub decls: *mut List,
}
#[derive(Copy, Clone)]
#[repr(C)]
pub struct BucketNode {
    pub key: *mut ::core::ffi::c_char,
    pub value: *mut ::core::ffi::c_char,
    pub next: *mut BucketNode,
}
#[derive(Copy, Clone)]
#[repr(C)]
pub struct Hashmap {
    pub buckets: *mut *mut BucketNode,
    pub size: ::core::ffi::c_int,
    pub cap: ::core::ffi::c_int,
}
pub const __ASSERT_FUNCTION: [::core::ffi::c_char; 29] = unsafe {
    ::core::mem::transmute::<
        [u8; 29],
        [::core::ffi::c_char; 29],
    >(*b"int lexer_ungetchar(Lexer *)\0")
};
pub const NULL: *mut ::core::ffi::c_void = ::core::ptr::null_mut::<
    ::core::ffi::c_void,
>();
pub const EOF: ::core::ffi::c_int = -(1 as ::core::ffi::c_int);
#[no_mangle]
pub static mut sp_offset: ::core::ffi::c_uint = 0;
#[no_mangle]
pub unsafe extern "C" fn r_code_gen_init() {
    registers_in_use = 0 as uint32_t;
    sp_offset = 0 as ::core::ffi::c_uint;
}
#[no_mangle]
pub unsafe extern "C" fn r_start_main() -> *mut ::core::ffi::c_char {
    static mut start: [::core::ffi::c_char; 256] = unsafe {
        ::core::mem::transmute::<
            [u8; 256],
            [::core::ffi::c_char; 256],
        >(
            *b".global _start\n_start:\n\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0",
        )
    };
    return &raw mut start as *mut ::core::ffi::c_char;
}
pub const TOKEN_LENGTH: ::core::ffi::c_int = 256 as ::core::ffi::c_int;
#[no_mangle]
pub unsafe extern "C" fn testing_setup_internal(
    mut func_name: *const ::core::ffi::c_char,
) {
    printf(b"Running tests from \0" as *const u8 as *const ::core::ffi::c_char);
    fflush(stdout);
    fprintf(
        stderr,
        b"\x1B[%dm\0" as *const u8 as *const ::core::ffi::c_char,
        32 as ::core::ffi::c_int,
    );
    fprintf(stderr, b"\"%s\"\0" as *const u8 as *const ::core::ffi::c_char, func_name);
    fprintf(stderr, b"\x1B[0m\0" as *const u8 as *const ::core::ffi::c_char);
    printf(b" ...\n\0" as *const u8 as *const ::core::ffi::c_char);
}
#[no_mangle]
pub unsafe extern "C" fn testing_cleanup_internal(
    mut func_name: *const ::core::ffi::c_char,
) {
    printf(b"Concluded tests from \0" as *const u8 as *const ::core::ffi::c_char);
    fflush(stdout);
    fprintf(
        stderr,
        b"\x1B[%dm\0" as *const u8 as *const ::core::ffi::c_char,
        32 as ::core::ffi::c_int,
    );
    fprintf(stderr, b"\"%s\"\0" as *const u8 as *const ::core::ffi::c_char, func_name);
    fprintf(stderr, b"\x1B[0m\0" as *const u8 as *const ::core::ffi::c_char);
    printf(b"\n\0" as *const u8 as *const ::core::ffi::c_char);
}
#[no_mangle]
pub unsafe extern "C" fn testing_single_test_internal(
    mut func_name: *const ::core::ffi::c_char,
) {
    printf(b"Running \0" as *const u8 as *const ::core::ffi::c_char);
    fflush(stdout);
    fprintf(
        stderr,
        b"\x1B[%dm\0" as *const u8 as *const ::core::ffi::c_char,
        32 as ::core::ffi::c_int,
    );
    fprintf(stderr, b"\"%s\"\0" as *const u8 as *const ::core::ffi::c_char, func_name);
    fprintf(stderr, b"\x1B[0m\0" as *const u8 as *const ::core::ffi::c_char);
    printf(b"\n\0" as *const u8 as *const ::core::ffi::c_char);
}
#[no_mangle]
pub unsafe extern "C" fn test_x86() -> ::core::ffi::c_int {
    testing_setup_internal(b"test_x86\0" as *const u8 as *const ::core::ffi::c_char);
    test_init_int_literal();
    test_op_on_rax_with_rdi();
    testing_cleanup_internal(b"test_x86\0" as *const u8 as *const ::core::ffi::c_char);
    return 0 as ::core::ffi::c_int;
}
#[no_mangle]
pub static mut registers_in_use: uint32_t = 0;
#[no_mangle]
pub static mut rsp_offset: ::core::ffi::c_uint = 0;
#[no_mangle]
pub unsafe extern "C" fn code_gen_init() {
    registers_in_use = 0 as uint32_t;
    rsp_offset = 0 as ::core::ffi::c_uint;
}
#[no_mangle]
pub unsafe extern "C" fn ttype_to_op(mut t: TokenType) -> Op {
    match t as ::core::ffi::c_uint {
        17 => return OP_ADD,
        16 => return OP_SUB,
        _ => return OP_NOP,
    };
}
#[no_mangle]
pub unsafe extern "C" fn start_main() -> *mut ::core::ffi::c_char {
    static mut start: [::core::ffi::c_char; 256] = unsafe {
        ::core::mem::transmute::<
            [u8; 256],
            [::core::ffi::c_char; 256],
        >(
            *b"global _start\nsection .text\n\n_start:\n\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0",
        )
    };
    return &raw mut start as *mut ::core::ffi::c_char;
}
#[no_mangle]
pub unsafe extern "C" fn end_main() -> *mut ::core::ffi::c_char {
    static mut end: [::core::ffi::c_char; 256] = unsafe {
        ::core::mem::transmute::<
            [u8; 256],
            [::core::ffi::c_char; 256],
        >(
            *b"\tmov rax, 60\tmov rdi, 0\tsyscall\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0",
        )
    };
    return &raw mut end as *mut ::core::ffi::c_char;
}
#[no_mangle]
pub unsafe extern "C" fn end_main_custom_return(
    mut val: ::core::ffi::c_int,
) -> *mut ::core::ffi::c_char {
    let mut end = ::core::ptr::null_mut::<::core::ffi::c_char>();
    end = malloc(
        (256 as size_t)
            .wrapping_mul(::core::mem::size_of::<::core::ffi::c_char>() as size_t),
    ) as *mut ::core::ffi::c_char;
    sprintf(
        end,
        b"\tmov rax, 60\n\tmov rdi, %d\n\tsyscall\n\0" as *const u8
            as *const ::core::ffi::c_char,
        val,
    );
    return end;
}
static mut op_strs: [*mut ::core::ffi::c_char; 4] = [
    b"add\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    b"sub\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    b"mov\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    ::core::ptr::null::<::core::ffi::c_char>() as *mut ::core::ffi::c_char,
];
#[no_mangle]
pub unsafe extern "C" fn op_on_rax_with_rdi(mut op: Op) -> *mut ::core::ffi::c_char {
    let mut end = ::core::ptr::null_mut::<::core::ffi::c_char>();
    end = malloc(
        (256 as size_t)
            .wrapping_mul(::core::mem::size_of::<::core::ffi::c_char>() as size_t),
    ) as *mut ::core::ffi::c_char;
    let mut op_str = op_strs[op as usize];
    sprintf(
        end,
        b"\t%s rax, rdi\n\0" as *const u8 as *const ::core::ffi::c_char,
        op_str,
    );
    return end;
}
#[no_mangle]
pub unsafe extern "C" fn start_func() -> *mut ::core::ffi::c_char {
    static mut start: [::core::ffi::c_char; 256] = unsafe {
        ::core::mem::transmute::<
            [u8; 256],
            [::core::ffi::c_char; 256],
        >(
            *b"\tsub rsp, 32\tmov [rsp], r12\tmov [rsp+8], r13\tmov [rsp+16], r14\tmov [rsp+24], r15\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0",
        )
    };
    return &raw mut start as *mut ::core::ffi::c_char;
}
#[no_mangle]
pub unsafe extern "C" fn end_func() -> *mut ::core::ffi::c_char {
    static mut end: [::core::ffi::c_char; 256] = unsafe {
        ::core::mem::transmute::<
            [u8; 256],
            [::core::ffi::c_char; 256],
        >(
            *b"\tmov r12, [rsp]\tmov r13, [rsp+8]\tmov r14, [rsp+16]\tmov r15, [rsp+24]\tadd rsp, 32\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0",
        )
    };
    return &raw mut end as *mut ::core::ffi::c_char;
}
#[no_mangle]
pub unsafe extern "C" fn init_int_literal(
    mut val: ::core::ffi::c_int,
) -> *mut ::core::ffi::c_char {
    rsp_offset = rsp_offset.wrapping_add(8 as ::core::ffi::c_uint);
    let mut init = ::core::ptr::null_mut::<::core::ffi::c_char>();
    init = malloc(
        (256 as size_t)
            .wrapping_mul(::core::mem::size_of::<::core::ffi::c_char>() as size_t),
    ) as *mut ::core::ffi::c_char;
    sprintf(
        init,
        b"\tmov [rsp+%d], %d\0" as *const u8 as *const ::core::ffi::c_char,
        rsp_offset,
        val,
    );
    return init;
}
#[no_mangle]
pub unsafe extern "C" fn test_init_int_literal() -> ::core::ffi::c_int {
    testing_single_test_internal(
        b"test_init_int_literal\0" as *const u8 as *const ::core::ffi::c_char,
    );
    code_gen_init();
    if strcmp(
        init_int_literal(100 as ::core::ffi::c_int),
        b"\tmov [rsp+8], 100\0" as *const u8 as *const ::core::ffi::c_char,
    ) == 0 as ::core::ffi::c_int
    {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/codegen/x86/codegen.c\0" as *const u8 as *const ::core::ffi::c_char,
            113 as ::core::ffi::c_int,
            b"strcmp(init_int_literal(100), \"\tmov [rsp+8], 100\") == 0\0" as *const u8
                as *const ::core::ffi::c_char,
        );
    };
    return 0 as ::core::ffi::c_int;
}
#[no_mangle]
pub unsafe extern "C" fn test_op_on_rax_with_rdi() -> ::core::ffi::c_int {
    testing_single_test_internal(
        b"test_op_on_rax_with_rdi\0" as *const u8 as *const ::core::ffi::c_char,
    );
    let mut out = op_on_rax_with_rdi(OP_ADD);
    if strcmp(out, b"\tadd rax, rdi\n\0" as *const u8 as *const ::core::ffi::c_char)
        == 0 as ::core::ffi::c_int
    {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/codegen/x86/codegen.c\0" as *const u8 as *const ::core::ffi::c_char,
            122 as ::core::ffi::c_int,
            b"strcmp(out, \"\tadd rax, rdi\\n\") == 0\0" as *const u8
                as *const ::core::ffi::c_char,
        );
    };
    let mut out2 = op_on_rax_with_rdi(OP_MOV);
    if strcmp(out2, b"\tmov rax, rdi\n\0" as *const u8 as *const ::core::ffi::c_char)
        == 0 as ::core::ffi::c_int
    {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/codegen/x86/codegen.c\0" as *const u8 as *const ::core::ffi::c_char,
            125 as ::core::ffi::c_int,
            b"strcmp(out2, \"\tmov rax, rdi\\n\") == 0\0" as *const u8
                as *const ::core::ffi::c_char,
        );
    };
    return 0 as ::core::ffi::c_int;
}
pub const TOKEN_PUTBACKS: ::core::ffi::c_int = 5 as ::core::ffi::c_int;
#[no_mangle]
pub unsafe extern "C" fn in_string(
    mut c: ::core::ffi::c_char,
    mut s: *mut ::core::ffi::c_char,
) -> ::core::ffi::c_int {
    let mut d = s as *mut ::core::ffi::c_char;
    while *d != 0 {
        if *d as ::core::ffi::c_int == c as ::core::ffi::c_int {
            return 1 as ::core::ffi::c_int;
        }
        d = d.offset(1);
    }
    return 0 as ::core::ffi::c_int;
}
#[no_mangle]
pub static mut single_char_tokens: [::core::ffi::c_char; 15] = unsafe {
    ::core::mem::transmute::<[u8; 15], [::core::ffi::c_char; 15]>(*b"(){}[];~#,.:?~\0")
};
#[no_mangle]
pub static mut operator_strings: [*mut ::core::ffi::c_char; 37] = [
    b"-\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    b"+\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    b"*\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    b"/\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    b"=\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    b":\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    b"%\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    b"&\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    b"&&\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    b"|\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    b"||\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    b"-=\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    b"+=\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    b"++\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    b"--\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    b"/=\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    b"*=\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    b"%=\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    b"&=\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    b"|=\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    b"&&=\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    b"||=\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    b">\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    b"<\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    b"<=\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    b">=\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    b"<<\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    b">>\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    b"!\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    b"==\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    b"!=\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    b"^\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    b"^=\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    b"->\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    b"<<=\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    b">>=\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    ::core::ptr::null::<::core::ffi::c_char>() as *mut ::core::ffi::c_char,
];
#[no_mangle]
pub unsafe extern "C" fn starts_operator(
    mut c: ::core::ffi::c_char,
) -> ::core::ffi::c_int {
    match c as ::core::ffi::c_int {
        45 | 43 | 42 | 47 | 61 | 58 | 37 | 38 | 124 | 60 | 62 | 33 | 126 | 94 => {
            return 1 as ::core::ffi::c_int;
        }
        _ => return 0 as ::core::ffi::c_int,
    };
}
#[no_mangle]
pub unsafe extern "C" fn valid_operator_sequence(
    mut op: *mut ::core::ffi::c_char,
) -> ::core::ffi::c_int {
    let mut top = &raw mut operator_strings as *mut *mut ::core::ffi::c_char;
    while !(*top).is_null() {
        if strcmp(*top, op) == 0 {
            return 1 as ::core::ffi::c_int;
        }
        top = top.offset(1);
    }
    return 0 as ::core::ffi::c_int;
}
#[no_mangle]
pub unsafe extern "C" fn is_valid_numeric_or_id_char(
    mut c: ::core::ffi::c_char,
) -> ::core::ffi::c_int {
    return (c as ::core::ffi::c_int == '_' as i32
        || c as ::core::ffi::c_int == '.' as i32) as ::core::ffi::c_int;
}
#[no_mangle]
pub unsafe extern "C" fn lexer_getchar(mut l: *mut Lexer) -> ::core::ffi::c_int {
    (*l).position += 1;
    (*l).last_column = (*l).column;
    (*l).buffer[0 as ::core::ffi::c_int as usize] = getc((*l).fp) as ::core::ffi::c_char;
    if (*l).buffer[0 as ::core::ffi::c_int as usize] as ::core::ffi::c_int == '\n' as i32
    {
        (*l).line += 1;
        (*l).column = 0 as ::core::ffi::c_int;
    } else {
        (*l).column += 1;
    }
    return (*l).buffer[0 as ::core::ffi::c_int as usize] as ::core::ffi::c_int;
}
#[no_mangle]
pub unsafe extern "C" fn lexer_ungetchar(mut l: *mut Lexer) -> ::core::ffi::c_int {
    if (*l).position >= 0 as ::core::ffi::c_long {} else {
        __assert_fail(
            b"l->position >= 0\0" as *const u8 as *const ::core::ffi::c_char,
            b"src/lexer/lex.c\0" as *const u8 as *const ::core::ffi::c_char,
            102 as ::core::ffi::c_uint,
            __ASSERT_FUNCTION.as_ptr(),
        );
    }
    'c_4152: {
        if (*l).position >= 0 as ::core::ffi::c_long {} else {
            __assert_fail(
                b"l->position >= 0\0" as *const u8 as *const ::core::ffi::c_char,
                b"src/lexer/lex.c\0" as *const u8 as *const ::core::ffi::c_char,
                102 as ::core::ffi::c_uint,
                __ASSERT_FUNCTION.as_ptr(),
            );
        }
    };
    (*l).position -= 1;
    (*l).column = (*l).last_column;
    if (*l).buffer[0 as ::core::ffi::c_int as usize] as ::core::ffi::c_int == '\n' as i32
    {
        (*l).line -= 1;
    }
    ungetc((*l).buffer[0 as ::core::ffi::c_int as usize] as ::core::ffi::c_int, (*l).fp);
    return 1 as ::core::ffi::c_int;
}
#[no_mangle]
pub unsafe extern "C" fn lex(
    mut l: *mut Lexer,
    mut t: *mut Token,
) -> ::core::ffi::c_int {
    loop {
        real_lex(l, t);
        if (*t).type_0 as ::core::ffi::c_uint
            != TT_NEWLINE as ::core::ffi::c_int as ::core::ffi::c_uint
        {
            break;
        }
    }
    return 0 as ::core::ffi::c_int;
}
#[no_mangle]
pub unsafe extern "C" fn real_lex(
    mut l: *mut Lexer,
    mut t: *mut Token,
) -> ::core::ffi::c_int {
    if (*l).unlexed_count > 0 as ::core::ffi::c_uint {
        (*l).unlexed_count = (*l).unlexed_count.wrapping_sub(1);
        memcpy(
            t as *mut ::core::ffi::c_void,
            (&raw mut (*l).unlexed as *mut Token).offset((*l).unlexed_count as isize)
                as *mut Token as *const ::core::ffi::c_void,
            ::core::mem::size_of::<Token>() as size_t,
        );
        return 0 as ::core::ffi::c_int;
    }
    skip_to_token(l);
    let mut init = lexer_getchar(l);
    memset(
        &raw mut (*t).contents as *mut ::core::ffi::c_char as *mut ::core::ffi::c_void,
        0 as ::core::ffi::c_int,
        TOKEN_LENGTH as size_t,
    );
    memcpy(
        &raw mut (*t).source_file as *mut ::core::ffi::c_char
            as *mut ::core::ffi::c_void,
        &raw mut (*l).current_file as *const ::core::ffi::c_void,
        TOKEN_LENGTH as size_t,
    );
    static mut eof: [::core::ffi::c_char; 14] = unsafe {
        ::core::mem::transmute::<
            [u8; 14],
            [::core::ffi::c_char; 14],
        >(*b"[end of file]\0")
    };
    if init == EOF {
        strcpy(
            &raw mut (*t).contents as *mut ::core::ffi::c_char,
            &raw mut eof as *mut ::core::ffi::c_char,
        );
        (*t).length = strlen(&raw mut eof as *mut ::core::ffi::c_char)
            as ::core::ffi::c_uint;
        (*t).type_0 = TT_EOF;
        (*t).line = (*l).line;
        (*t).column = (*l).column;
        return 0 as ::core::ffi::c_int;
    }
    if init == ' ' as i32 || init == '\t' as i32 {
        fprintf(
            stderr,
            b"\x1B[%dm\0" as *const u8 as *const ::core::ffi::c_char,
            31 as ::core::ffi::c_int,
        );
        fprintf(
            stderr,
            b"Error: jccc: internal error: did not skip whitespace correctly\n\0"
                as *const u8 as *const ::core::ffi::c_char,
        );
        fprintf(stderr, b"\x1B[0m\0" as *const u8 as *const ::core::ffi::c_char);
        return -(1 as ::core::ffi::c_int);
    }
    static mut nline: [::core::ffi::c_char; 10] = unsafe {
        ::core::mem::transmute::<[u8; 10], [::core::ffi::c_char; 10]>(*b"[newline]\0")
    };
    if init == '\n' as i32 {
        strcpy(
            &raw mut (*t).contents as *mut ::core::ffi::c_char,
            &raw mut nline as *mut ::core::ffi::c_char,
        );
        (*t).length = strlen(&raw mut nline as *mut ::core::ffi::c_char)
            as ::core::ffi::c_uint;
        (*t).type_0 = TT_NEWLINE;
        (*t).line = (*l).line;
        (*t).column = (*l).column;
        return 0 as ::core::ffi::c_int;
    }
    let mut pos = 0 as ::core::ffi::c_int;
    let fresh0 = pos;
    pos = pos + 1;
    (*t).contents[fresh0 as usize] = init as ::core::ffi::c_char;
    if in_string(
        init as ::core::ffi::c_char,
        &raw mut single_char_tokens as *mut ::core::ffi::c_char,
    ) != 0
    {
        (*t).length = pos as ::core::ffi::c_uint;
        (*t).type_0 = ttype_one_char(init as ::core::ffi::c_char);
        (*t).line = (*l).line;
        (*t).column = (*l).column;
        return 0 as ::core::ffi::c_int;
    }
    let mut c: ::core::ffi::c_int = 0;
    let mut starting_line: ::core::ffi::c_int = 0;
    let mut starting_col: ::core::ffi::c_int = 0;
    if is_valid_numeric_or_id_char(init as ::core::ffi::c_char) != 0 {
        starting_line = (*l).line;
        starting_col = (*l).column;
        loop {
            c = lexer_getchar(l);
            if is_valid_numeric_or_id_char(c as ::core::ffi::c_char) == 0 {
                break;
            }
            if pos >= TOKEN_LENGTH - 1 as ::core::ffi::c_int {
                fprintf(
                    stderr,
                    b"\x1B[%dm\0" as *const u8 as *const ::core::ffi::c_char,
                    31 as ::core::ffi::c_int,
                );
                fprintf(
                    stderr,
                    b"Error: jccc: identifier too long, over %d characters\n\0"
                        as *const u8 as *const ::core::ffi::c_char,
                    256 as ::core::ffi::c_int,
                );
                fprintf(stderr, b"\x1B[0m\0" as *const u8 as *const ::core::ffi::c_char);
                fprintf(
                    stderr,
                    b"\x1B[%dm\0" as *const u8 as *const ::core::ffi::c_char,
                    31 as ::core::ffi::c_int,
                );
                fprintf(
                    stderr,
                    b"Error: jccc: identifier began with the following:\n\0" as *const u8
                        as *const ::core::ffi::c_char,
                );
                fprintf(stderr, b"\x1B[0m\0" as *const u8 as *const ::core::ffi::c_char);
                fprintf(
                    stderr,
                    b"\x1B[%dm\0" as *const u8 as *const ::core::ffi::c_char,
                    31 as ::core::ffi::c_int,
                );
                fprintf(
                    stderr,
                    b"Error: jccc: %.*s\n\0" as *const u8 as *const ::core::ffi::c_char,
                    256 as ::core::ffi::c_int,
                    &raw mut (*t).contents as *mut ::core::ffi::c_char,
                );
                fprintf(stderr, b"\x1B[0m\0" as *const u8 as *const ::core::ffi::c_char);
                return -(1 as ::core::ffi::c_int);
            }
            let fresh1 = pos;
            pos = pos + 1;
            (*t).contents[fresh1 as usize] = c as ::core::ffi::c_char;
        }
        lexer_ungetchar(l);
        (*t).contents[pos as usize] = '\0' as i32 as ::core::ffi::c_char;
        (*t).type_0 = ttype_many_chars(
            &raw mut (*t).contents as *mut ::core::ffi::c_char,
        );
        (*t).length = pos as ::core::ffi::c_uint;
        (*t).line = starting_line;
        (*t).column = starting_col;
        return 0 as ::core::ffi::c_int;
    }
    if starts_operator(init as ::core::ffi::c_char) != 0 {
        while valid_operator_sequence(&raw mut (*t).contents as *mut ::core::ffi::c_char)
            != 0
        {
            c = lexer_getchar(l);
            let fresh2 = pos;
            pos = pos + 1;
            (*t).contents[fresh2 as usize] = c as ::core::ffi::c_char;
        }
        lexer_ungetchar(l);
        (*t).contents[(pos - 1 as ::core::ffi::c_int) as usize] = '\0' as i32
            as ::core::ffi::c_char;
        (*t).type_0 = ttype_from_string(
            &raw mut (*t).contents as *mut ::core::ffi::c_char,
        );
        (*t).length = pos as ::core::ffi::c_uint;
        return 0 as ::core::ffi::c_int;
    }
    fprintf(
        stderr,
        b"\x1B[%dm\0" as *const u8 as *const ::core::ffi::c_char,
        31 as ::core::ffi::c_int,
    );
    fprintf(
        stderr,
        b"Error: jccc: lexer unable to identify token starting with: %c\n\0" as *const u8
            as *const ::core::ffi::c_char,
        init,
    );
    fprintf(stderr, b"\x1B[0m\0" as *const u8 as *const ::core::ffi::c_char);
    return 0 as ::core::ffi::c_int;
}
#[no_mangle]
pub unsafe extern "C" fn unlex(
    mut l: *mut Lexer,
    mut t: *mut Token,
) -> ::core::ffi::c_int {
    if (*l).unlexed_count >= TOKEN_PUTBACKS as ::core::ffi::c_uint {
        fprintf(
            stderr,
            b"\x1B[%dm\0" as *const u8 as *const ::core::ffi::c_char,
            31 as ::core::ffi::c_int,
        );
        fprintf(
            stderr,
            b"Error: jccc: internal: tried to unlex more than %d tokens at a time\n\0"
                as *const u8 as *const ::core::ffi::c_char,
            5 as ::core::ffi::c_int,
        );
        fprintf(stderr, b"\x1B[0m\0" as *const u8 as *const ::core::ffi::c_char);
        return -(1 as ::core::ffi::c_int);
    }
    memcpy(
        (&raw mut (*l).unlexed as *mut Token).offset((*l).unlexed_count as isize)
            as *mut Token as *mut ::core::ffi::c_void,
        t as *const ::core::ffi::c_void,
        ::core::mem::size_of::<Token>() as size_t,
    );
    (*l).unlexed_count = (*l).unlexed_count.wrapping_add(1);
    return 0 as ::core::ffi::c_int;
}
#[no_mangle]
pub unsafe extern "C" fn skip_to_token(mut l: *mut Lexer) -> ::core::ffi::c_int {
    let mut cur: ::core::ffi::c_char = 0;
    let mut prev: ::core::ffi::c_char = 0;
    let mut in_block = 0 as ::core::ffi::c_int;
    let mut pass = 0 as ::core::ffi::c_int;
    cur = lexer_getchar(l) as ::core::ffi::c_char;
    if cur as ::core::ffi::c_int != EOF {
        prev = cur;
        if !(cur as ::core::ffi::c_int == ' ' as i32
            || cur as ::core::ffi::c_int == '\t' as i32
            || cur as ::core::ffi::c_int == '/' as i32)
        {
            lexer_ungetchar(l);
            return 0 as ::core::ffi::c_int;
        }
    } else {
        return -(1 as ::core::ffi::c_int)
    }
    loop {
        cur = lexer_getchar(l) as ::core::ffi::c_char;
        if !(cur as ::core::ffi::c_int != EOF) {
            break;
        }
        if cur as ::core::ffi::c_int == '/' as i32
            && prev as ::core::ffi::c_int == '/' as i32
            && in_block == 0 as ::core::ffi::c_int
        {
            in_block = 1 as ::core::ffi::c_int;
        } else if cur as ::core::ffi::c_int == '*' as i32
            && prev as ::core::ffi::c_int == '/' as i32
            && in_block == 0 as ::core::ffi::c_int
        {
            in_block = 2 as ::core::ffi::c_int;
            pass = 2 as ::core::ffi::c_int;
        } else if in_block == 1 as ::core::ffi::c_int
            && cur as ::core::ffi::c_int == '\n' as i32
            || in_block == 2 as ::core::ffi::c_int
                && cur as ::core::ffi::c_int == '/' as i32
                && prev as ::core::ffi::c_int == '*' as i32
                && pass <= 0 as ::core::ffi::c_int
        {
            in_block = 0 as ::core::ffi::c_int;
        } else if prev as ::core::ffi::c_int == '/' as i32
            && !(cur as ::core::ffi::c_int == '*' as i32
                || cur as ::core::ffi::c_int == '/' as i32)
            && in_block == 0 as ::core::ffi::c_int
        {
            lexer_ungetchar(l);
            return 0 as ::core::ffi::c_int;
        }
        if !(cur as ::core::ffi::c_int == ' ' as i32
            || cur as ::core::ffi::c_int == '\t' as i32
            || cur as ::core::ffi::c_int == '/' as i32)
            && in_block == 0 as ::core::ffi::c_int
        {
            lexer_ungetchar(l);
            return 0 as ::core::ffi::c_int;
        }
        pass -= 1 as ::core::ffi::c_int;
        prev = cur;
    }
    return -(1 as ::core::ffi::c_int);
}
#[no_mangle]
pub unsafe extern "C" fn ttype_one_char(mut c: ::core::ffi::c_char) -> TokenType {
    match c as ::core::ffi::c_int {
        40 => return TT_OPAREN,
        41 => return TT_CPAREN,
        123 => return TT_OBRACE,
        125 => return TT_CBRACE,
        91 => return TT_OBRACKET,
        93 => return TT_CBRACKET,
        59 => return TT_SEMI,
        46 => return TT_PERIOD,
        44 => return TT_COMMA,
        45 => return TT_MINUS,
        43 => return TT_PLUS,
        42 => return TT_STAR,
        47 => return TT_SLASH,
        61 => return TT_ASSIGN,
        58 => return TT_COLON,
        37 => return TT_MOD,
        38 => return TT_BAND,
        124 => return TT_BOR,
        62 => return TT_GREATER,
        60 => return TT_LESS,
        33 => return TT_LNOT,
        126 => return TT_BNOT,
        94 => return TT_XOR,
        35 => return TT_POUND,
        63 => return TT_QMARK,
        _ => return TT_LITERAL,
    };
}
#[no_mangle]
pub unsafe extern "C" fn ttype_many_chars(
    mut contents: *const ::core::ffi::c_char,
) -> TokenType {
    if strcmp(contents, b"auto\0" as *const u8 as *const ::core::ffi::c_char) == 0 {
        return TT_AUTO
    } else if strcmp(contents, b"break\0" as *const u8 as *const ::core::ffi::c_char)
        == 0
    {
        return TT_BREAK
    } else if strcmp(contents, b"continue\0" as *const u8 as *const ::core::ffi::c_char)
        == 0
    {
        return TT_CONTINUE
    } else if strcmp(contents, b"const\0" as *const u8 as *const ::core::ffi::c_char)
        == 0
    {
        return TT_CONST
    } else if strcmp(contents, b"case\0" as *const u8 as *const ::core::ffi::c_char) == 0
    {
        return TT_CASE
    } else if strcmp(contents, b"char\0" as *const u8 as *const ::core::ffi::c_char) == 0
    {
        return TT_CHAR
    } else if strcmp(contents, b"do\0" as *const u8 as *const ::core::ffi::c_char) == 0 {
        return TT_DO
    } else if strcmp(contents, b"double\0" as *const u8 as *const ::core::ffi::c_char)
        == 0
    {
        return TT_DOUBLE
    } else if strcmp(contents, b"default\0" as *const u8 as *const ::core::ffi::c_char)
        == 0
    {
        return TT_DEFAULT
    } else if strcmp(contents, b"enum\0" as *const u8 as *const ::core::ffi::c_char) == 0
    {
        return TT_ENUM
    } else if strcmp(contents, b"else\0" as *const u8 as *const ::core::ffi::c_char) == 0
    {
        return TT_ELSE
    } else if strcmp(contents, b"extern\0" as *const u8 as *const ::core::ffi::c_char)
        == 0
    {
        return TT_EXTERN
    } else if strcmp(contents, b"float\0" as *const u8 as *const ::core::ffi::c_char)
        == 0
    {
        return TT_FLOAT
    } else if strcmp(contents, b"for\0" as *const u8 as *const ::core::ffi::c_char) == 0
    {
        return TT_FOR
    } else if strcmp(contents, b"goto\0" as *const u8 as *const ::core::ffi::c_char) == 0
    {
        return TT_GOTO
    } else if strcmp(contents, b"int\0" as *const u8 as *const ::core::ffi::c_char) == 0
    {
        return TT_INT
    } else if strcmp(contents, b"if\0" as *const u8 as *const ::core::ffi::c_char) == 0 {
        return TT_IF
    } else if strcmp(contents, b"long\0" as *const u8 as *const ::core::ffi::c_char) == 0
    {
        return TT_LONG
    } else if strcmp(contents, b"return\0" as *const u8 as *const ::core::ffi::c_char)
        == 0
    {
        return TT_RETURN
    } else if strcmp(contents, b"register\0" as *const u8 as *const ::core::ffi::c_char)
        == 0
    {
        return TT_REGISTER
    } else if strcmp(contents, b"struct\0" as *const u8 as *const ::core::ffi::c_char)
        == 0
    {
        return TT_STRUCT
    } else if strcmp(contents, b"signed\0" as *const u8 as *const ::core::ffi::c_char)
        == 0
    {
        return TT_SIGNED
    } else if strcmp(contents, b"sizeof\0" as *const u8 as *const ::core::ffi::c_char)
        == 0
    {
        return TT_SIZEOF
    } else if strcmp(contents, b"static\0" as *const u8 as *const ::core::ffi::c_char)
        == 0
    {
        return TT_STATIC
    } else if strcmp(contents, b"short\0" as *const u8 as *const ::core::ffi::c_char)
        == 0
    {
        return TT_SHORT
    } else if strcmp(contents, b"switch\0" as *const u8 as *const ::core::ffi::c_char)
        == 0
    {
        return TT_SWITCH
    } else if strcmp(contents, b"typedef\0" as *const u8 as *const ::core::ffi::c_char)
        == 0
    {
        return TT_TYPEDEF
    } else if strcmp(contents, b"union\0" as *const u8 as *const ::core::ffi::c_char)
        == 0
    {
        return TT_UNION
    } else if strcmp(contents, b"unsigned\0" as *const u8 as *const ::core::ffi::c_char)
        == 0
    {
        return TT_UNSIGNED
    } else if strcmp(contents, b"void\0" as *const u8 as *const ::core::ffi::c_char) == 0
    {
        return TT_VOID
    } else if strcmp(contents, b"volatile\0" as *const u8 as *const ::core::ffi::c_char)
        == 0
    {
        return TT_VOLATILE
    } else if strcmp(contents, b"while\0" as *const u8 as *const ::core::ffi::c_char)
        == 0
    {
        return TT_WHILE
    } else if strcmp(contents, b"&&\0" as *const u8 as *const ::core::ffi::c_char) == 0 {
        return TT_LAND
    } else if strcmp(contents, b"||\0" as *const u8 as *const ::core::ffi::c_char) == 0 {
        return TT_LOR
    } else if strcmp(contents, b"-=\0" as *const u8 as *const ::core::ffi::c_char) == 0 {
        return TT_DEC
    } else if strcmp(contents, b"+=\0" as *const u8 as *const ::core::ffi::c_char) == 0 {
        return TT_INC
    } else if strcmp(contents, b"++\0" as *const u8 as *const ::core::ffi::c_char) == 0 {
        return TT_PLUSPLUS
    } else if strcmp(contents, b"--\0" as *const u8 as *const ::core::ffi::c_char) == 0 {
        return TT_MINUSMINUS
    } else if strcmp(contents, b"/=\0" as *const u8 as *const ::core::ffi::c_char) == 0 {
        return TT_DIVEQ
    } else if strcmp(contents, b"*=\0" as *const u8 as *const ::core::ffi::c_char) == 0 {
        return TT_MULEQ
    } else if strcmp(contents, b"%=\0" as *const u8 as *const ::core::ffi::c_char) == 0 {
        return TT_MODEQ
    } else if strcmp(contents, b"&=\0" as *const u8 as *const ::core::ffi::c_char) == 0 {
        return TT_BANDEQ
    } else if strcmp(contents, b"|=\0" as *const u8 as *const ::core::ffi::c_char) == 0 {
        return TT_BOREQ
    } else if strcmp(contents, b"&&=\0" as *const u8 as *const ::core::ffi::c_char) == 0
    {
        return TT_LANDEQ
    } else if strcmp(contents, b"||=\0" as *const u8 as *const ::core::ffi::c_char) == 0
    {
        return TT_LOREQ
    } else if strcmp(contents, b"<=\0" as *const u8 as *const ::core::ffi::c_char) == 0 {
        return TT_LESSEQ
    } else if strcmp(contents, b">=\0" as *const u8 as *const ::core::ffi::c_char) == 0 {
        return TT_GREATEREQ
    } else if strcmp(contents, b"<<\0" as *const u8 as *const ::core::ffi::c_char) == 0 {
        return TT_LEFTSHIFT
    } else if strcmp(contents, b">>\0" as *const u8 as *const ::core::ffi::c_char) == 0 {
        return TT_RIGHTSHIFT
    } else if strcmp(contents, b"==\0" as *const u8 as *const ::core::ffi::c_char) == 0 {
        return TT_EQUALS
    } else if strcmp(contents, b"^=\0" as *const u8 as *const ::core::ffi::c_char) == 0 {
        return TT_XOREQ
    } else if strcmp(contents, b"->\0" as *const u8 as *const ::core::ffi::c_char) == 0 {
        return TT_POINT
    } else if strcmp(contents, b"<<=\0" as *const u8 as *const ::core::ffi::c_char) == 0
    {
        return TT_LEFTSHIFTEQUALS
    } else if strcmp(contents, b">>=\0" as *const u8 as *const ::core::ffi::c_char) == 0
    {
        return TT_RIGHTSHIFTEQUALS
    } else if strcmp(contents, b"!=\0" as *const u8 as *const ::core::ffi::c_char) == 0 {
        return TT_NOTEQ
    }
    let mut all_numeric = 1 as ::core::ffi::c_int;
    let mut count_fs = 0 as ::core::ffi::c_int;
    let mut count_us = 0 as ::core::ffi::c_int;
    let mut i: ::core::ffi::c_int = 0;
    if contents.is_null() {
        return TT_NO_TOKEN;
    }
    i = 0 as ::core::ffi::c_int;
    while *contents.offset(i as isize) as ::core::ffi::c_int != '\0' as i32 {
        let mut c = *contents.offset(i as isize);
        if c as ::core::ffi::c_int == '.' as i32 {
            return TT_LITERAL;
        }
        if c as ::core::ffi::c_int == 'f' as i32 {
            count_fs += 1;
        }
        if c as ::core::ffi::c_int == 'u' as i32 {
            count_us += 1;
        }
        if (c as ::core::ffi::c_int > '9' as i32
            || (c as ::core::ffi::c_int) < '0' as i32)
            && c as ::core::ffi::c_int != 'u' as i32
        {
            all_numeric = 0 as ::core::ffi::c_int;
        }
        if c as ::core::ffi::c_int == '\'' as i32
            || c as ::core::ffi::c_int == '"' as i32
        {
            return TT_LITERAL;
        }
        i += 1;
    }
    if all_numeric != 0 {
        if count_us == 1 as ::core::ffi::c_int
            && *contents.offset((i - 1 as ::core::ffi::c_int) as isize)
                as ::core::ffi::c_int == 'u' as i32
        {
            return TT_LITERAL;
        }
        if count_us == 0 as ::core::ffi::c_int {
            return TT_LITERAL;
        }
    }
    return TT_IDENTIFIER;
}
#[no_mangle]
pub unsafe extern "C" fn ttype_from_string(
    mut contents: *const ::core::ffi::c_char,
) -> TokenType {
    let mut len: ::core::ffi::c_int = 0;
    len = strlen(contents) as ::core::ffi::c_int;
    if len == 1 as ::core::ffi::c_int {
        let mut token = ttype_one_char(
            *contents.offset(0 as ::core::ffi::c_int as isize),
        );
        return token;
    }
    return ttype_many_chars(contents);
}
static mut ttype_names: [*const ::core::ffi::c_char; 85] = [
    b"literal\0" as *const u8 as *const ::core::ffi::c_char,
    b"identifier\0" as *const u8 as *const ::core::ffi::c_char,
    b"open paren\0" as *const u8 as *const ::core::ffi::c_char,
    b"close paren\0" as *const u8 as *const ::core::ffi::c_char,
    b"open brace\0" as *const u8 as *const ::core::ffi::c_char,
    b"close brace\0" as *const u8 as *const ::core::ffi::c_char,
    b"open bracket\0" as *const u8 as *const ::core::ffi::c_char,
    b"close bracket\0" as *const u8 as *const ::core::ffi::c_char,
    b"semicolon\0" as *const u8 as *const ::core::ffi::c_char,
    b"no token\0" as *const u8 as *const ::core::ffi::c_char,
    b"end of file\0" as *const u8 as *const ::core::ffi::c_char,
    b"newline\0" as *const u8 as *const ::core::ffi::c_char,
    b"pound\0" as *const u8 as *const ::core::ffi::c_char,
    b".\0" as *const u8 as *const ::core::ffi::c_char,
    b",\0" as *const u8 as *const ::core::ffi::c_char,
    b"?\0" as *const u8 as *const ::core::ffi::c_char,
    b"-\0" as *const u8 as *const ::core::ffi::c_char,
    b"+\0" as *const u8 as *const ::core::ffi::c_char,
    b"*\0" as *const u8 as *const ::core::ffi::c_char,
    b"/\0" as *const u8 as *const ::core::ffi::c_char,
    b"=\0" as *const u8 as *const ::core::ffi::c_char,
    b":\0" as *const u8 as *const ::core::ffi::c_char,
    b"%\0" as *const u8 as *const ::core::ffi::c_char,
    b"&\0" as *const u8 as *const ::core::ffi::c_char,
    b"&&\0" as *const u8 as *const ::core::ffi::c_char,
    b"|\0" as *const u8 as *const ::core::ffi::c_char,
    b"||\0" as *const u8 as *const ::core::ffi::c_char,
    b"-=\0" as *const u8 as *const ::core::ffi::c_char,
    b"+=\0" as *const u8 as *const ::core::ffi::c_char,
    b"++\0" as *const u8 as *const ::core::ffi::c_char,
    b"--\0" as *const u8 as *const ::core::ffi::c_char,
    b"/=\0" as *const u8 as *const ::core::ffi::c_char,
    b"*=\0" as *const u8 as *const ::core::ffi::c_char,
    b"%=\0" as *const u8 as *const ::core::ffi::c_char,
    b"&=\0" as *const u8 as *const ::core::ffi::c_char,
    b"|=\0" as *const u8 as *const ::core::ffi::c_char,
    b"&&=\0" as *const u8 as *const ::core::ffi::c_char,
    b"||=\0" as *const u8 as *const ::core::ffi::c_char,
    b">\0" as *const u8 as *const ::core::ffi::c_char,
    b"<\0" as *const u8 as *const ::core::ffi::c_char,
    b"<=\0" as *const u8 as *const ::core::ffi::c_char,
    b">=\0" as *const u8 as *const ::core::ffi::c_char,
    b"<<\0" as *const u8 as *const ::core::ffi::c_char,
    b">>\0" as *const u8 as *const ::core::ffi::c_char,
    b"!\0" as *const u8 as *const ::core::ffi::c_char,
    b"~\0" as *const u8 as *const ::core::ffi::c_char,
    b"==\0" as *const u8 as *const ::core::ffi::c_char,
    b"!=\0" as *const u8 as *const ::core::ffi::c_char,
    b"^\0" as *const u8 as *const ::core::ffi::c_char,
    b"^=\0" as *const u8 as *const ::core::ffi::c_char,
    b"->\0" as *const u8 as *const ::core::ffi::c_char,
    b"<<=\0" as *const u8 as *const ::core::ffi::c_char,
    b">>=\0" as *const u8 as *const ::core::ffi::c_char,
    b"auto\0" as *const u8 as *const ::core::ffi::c_char,
    b"break\0" as *const u8 as *const ::core::ffi::c_char,
    b"char\0" as *const u8 as *const ::core::ffi::c_char,
    b"const\0" as *const u8 as *const ::core::ffi::c_char,
    b"case\0" as *const u8 as *const ::core::ffi::c_char,
    b"continue\0" as *const u8 as *const ::core::ffi::c_char,
    b"double\0" as *const u8 as *const ::core::ffi::c_char,
    b"do\0" as *const u8 as *const ::core::ffi::c_char,
    b"default\0" as *const u8 as *const ::core::ffi::c_char,
    b"enum\0" as *const u8 as *const ::core::ffi::c_char,
    b"else\0" as *const u8 as *const ::core::ffi::c_char,
    b"extern\0" as *const u8 as *const ::core::ffi::c_char,
    b"float\0" as *const u8 as *const ::core::ffi::c_char,
    b"for\0" as *const u8 as *const ::core::ffi::c_char,
    b"goto\0" as *const u8 as *const ::core::ffi::c_char,
    b"if\0" as *const u8 as *const ::core::ffi::c_char,
    b"int\0" as *const u8 as *const ::core::ffi::c_char,
    b"long\0" as *const u8 as *const ::core::ffi::c_char,
    b"return\0" as *const u8 as *const ::core::ffi::c_char,
    b"register\0" as *const u8 as *const ::core::ffi::c_char,
    b"static\0" as *const u8 as *const ::core::ffi::c_char,
    b"switch\0" as *const u8 as *const ::core::ffi::c_char,
    b"short\0" as *const u8 as *const ::core::ffi::c_char,
    b"signed\0" as *const u8 as *const ::core::ffi::c_char,
    b"struct\0" as *const u8 as *const ::core::ffi::c_char,
    b"sizeof\0" as *const u8 as *const ::core::ffi::c_char,
    b"typedef\0" as *const u8 as *const ::core::ffi::c_char,
    b"unsigned\0" as *const u8 as *const ::core::ffi::c_char,
    b"union\0" as *const u8 as *const ::core::ffi::c_char,
    b"void\0" as *const u8 as *const ::core::ffi::c_char,
    b"volatile\0" as *const u8 as *const ::core::ffi::c_char,
    b"while\0" as *const u8 as *const ::core::ffi::c_char,
];
#[no_mangle]
pub unsafe extern "C" fn ttype_name(mut tt: TokenType) -> *const ::core::ffi::c_char {
    return ttype_names[tt as usize];
}
#[no_mangle]
pub unsafe extern "C" fn test_ttype_many_chars() -> ::core::ffi::c_int {
    testing_single_test_internal(
        b"test_ttype_many_chars\0" as *const u8 as *const ::core::ffi::c_char,
    );
    if ttype_many_chars(b"foo\0" as *const u8 as *const ::core::ffi::c_char)
        as ::core::ffi::c_uint
        == TT_IDENTIFIER as ::core::ffi::c_int as ::core::ffi::c_uint
    {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/lexer/lex.c\0" as *const u8 as *const ::core::ffi::c_char,
            659 as ::core::ffi::c_int,
            b"ttype_many_chars(\"foo\") == TT_IDENTIFIER\0" as *const u8
                as *const ::core::ffi::c_char,
        );
    };
    if ttype_many_chars(b"struct\0" as *const u8 as *const ::core::ffi::c_char)
        as ::core::ffi::c_uint == TT_STRUCT as ::core::ffi::c_int as ::core::ffi::c_uint
    {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/lexer/lex.c\0" as *const u8 as *const ::core::ffi::c_char,
            660 as ::core::ffi::c_int,
            b"ttype_many_chars(\"struct\") == TT_STRUCT\0" as *const u8
                as *const ::core::ffi::c_char,
        );
    };
    if ttype_many_chars(b"while\0" as *const u8 as *const ::core::ffi::c_char)
        as ::core::ffi::c_uint == TT_WHILE as ::core::ffi::c_int as ::core::ffi::c_uint
    {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/lexer/lex.c\0" as *const u8 as *const ::core::ffi::c_char,
            661 as ::core::ffi::c_int,
            b"ttype_many_chars(\"while\") == TT_WHILE\0" as *const u8
                as *const ::core::ffi::c_char,
        );
    };
    return 0 as ::core::ffi::c_int;
}
#[no_mangle]
pub unsafe extern "C" fn test_ttype_one_char() -> ::core::ffi::c_int {
    testing_single_test_internal(
        b"test_ttype_one_char\0" as *const u8 as *const ::core::ffi::c_char,
    );
    if ttype_one_char('a' as i32 as ::core::ffi::c_char) as ::core::ffi::c_uint
        == TT_IDENTIFIER as ::core::ffi::c_int as ::core::ffi::c_uint
    {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/lexer/lex.c\0" as *const u8 as *const ::core::ffi::c_char,
            670 as ::core::ffi::c_int,
            b"ttype_one_char('a') == TT_IDENTIFIER\0" as *const u8
                as *const ::core::ffi::c_char,
        );
    };
    if ttype_one_char('1' as i32 as ::core::ffi::c_char) as ::core::ffi::c_uint
        == TT_LITERAL as ::core::ffi::c_int as ::core::ffi::c_uint
    {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/lexer/lex.c\0" as *const u8 as *const ::core::ffi::c_char,
            671 as ::core::ffi::c_int,
            b"ttype_one_char('1') == TT_LITERAL\0" as *const u8
                as *const ::core::ffi::c_char,
        );
    };
    if ttype_one_char('+' as i32 as ::core::ffi::c_char) as ::core::ffi::c_uint
        == TT_PLUS as ::core::ffi::c_int as ::core::ffi::c_uint
    {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/lexer/lex.c\0" as *const u8 as *const ::core::ffi::c_char,
            673 as ::core::ffi::c_int,
            b"ttype_one_char('+') == TT_PLUS\0" as *const u8
                as *const ::core::ffi::c_char,
        );
    };
    if ttype_one_char('-' as i32 as ::core::ffi::c_char) as ::core::ffi::c_uint
        == TT_MINUS as ::core::ffi::c_int as ::core::ffi::c_uint
    {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/lexer/lex.c\0" as *const u8 as *const ::core::ffi::c_char,
            674 as ::core::ffi::c_int,
            b"ttype_one_char('-') == TT_MINUS\0" as *const u8
                as *const ::core::ffi::c_char,
        );
    };
    if ttype_one_char('>' as i32 as ::core::ffi::c_char) as ::core::ffi::c_uint
        == TT_GREATER as ::core::ffi::c_int as ::core::ffi::c_uint
    {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/lexer/lex.c\0" as *const u8 as *const ::core::ffi::c_char,
            675 as ::core::ffi::c_int,
            b"ttype_one_char('>') == TT_GREATER\0" as *const u8
                as *const ::core::ffi::c_char,
        );
    };
    if ttype_one_char('~' as i32 as ::core::ffi::c_char) as ::core::ffi::c_uint
        == TT_BNOT as ::core::ffi::c_int as ::core::ffi::c_uint
    {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/lexer/lex.c\0" as *const u8 as *const ::core::ffi::c_char,
            676 as ::core::ffi::c_int,
            b"ttype_one_char('~') == TT_BNOT\0" as *const u8
                as *const ::core::ffi::c_char,
        );
    };
    return 0 as ::core::ffi::c_int;
}
#[no_mangle]
pub unsafe extern "C" fn test_ttype_name() -> ::core::ffi::c_int {
    testing_single_test_internal(
        b"test_ttype_name\0" as *const u8 as *const ::core::ffi::c_char,
    );
    if strcmp(
        ttype_name(TT_LITERAL),
        b"literal\0" as *const u8 as *const ::core::ffi::c_char,
    ) == 0 as ::core::ffi::c_int
    {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/lexer/lex.c\0" as *const u8 as *const ::core::ffi::c_char,
            684 as ::core::ffi::c_int,
            b"strcmp(ttype_name(TT_LITERAL), \"literal\") == 0\0" as *const u8
                as *const ::core::ffi::c_char,
        );
    };
    if strcmp(ttype_name(TT_PLUS), b"+\0" as *const u8 as *const ::core::ffi::c_char)
        == 0 as ::core::ffi::c_int
    {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/lexer/lex.c\0" as *const u8 as *const ::core::ffi::c_char,
            685 as ::core::ffi::c_int,
            b"strcmp(ttype_name(TT_PLUS), \"+\") == 0\0" as *const u8
                as *const ::core::ffi::c_char,
        );
    };
    if strcmp(
        ttype_name(TT_SIZEOF),
        b"sizeof\0" as *const u8 as *const ::core::ffi::c_char,
    ) == 0 as ::core::ffi::c_int
    {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/lexer/lex.c\0" as *const u8 as *const ::core::ffi::c_char,
            686 as ::core::ffi::c_int,
            b"strcmp(ttype_name(TT_SIZEOF), \"sizeof\") == 0\0" as *const u8
                as *const ::core::ffi::c_char,
        );
    };
    if strcmp(
        ttype_name(TT_WHILE),
        b"while\0" as *const u8 as *const ::core::ffi::c_char,
    ) == 0 as ::core::ffi::c_int
    {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/lexer/lex.c\0" as *const u8 as *const ::core::ffi::c_char,
            687 as ::core::ffi::c_int,
            b"strcmp(ttype_name(TT_WHILE), \"while\") == 0\0" as *const u8
                as *const ::core::ffi::c_char,
        );
    };
    return 0 as ::core::ffi::c_int;
}
#[no_mangle]
pub unsafe extern "C" fn test_ttype_from_string() -> ::core::ffi::c_int {
    testing_single_test_internal(
        b"test_ttype_from_string\0" as *const u8 as *const ::core::ffi::c_char,
    );
    if ttype_from_string(b"+\0" as *const u8 as *const ::core::ffi::c_char)
        as ::core::ffi::c_uint == TT_PLUS as ::core::ffi::c_int as ::core::ffi::c_uint
    {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/lexer/lex.c\0" as *const u8 as *const ::core::ffi::c_char,
            695 as ::core::ffi::c_int,
            b"ttype_from_string(\"+\") == TT_PLUS\0" as *const u8
                as *const ::core::ffi::c_char,
        );
    };
    if ttype_from_string(b"=\0" as *const u8 as *const ::core::ffi::c_char)
        as ::core::ffi::c_uint == TT_ASSIGN as ::core::ffi::c_int as ::core::ffi::c_uint
    {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/lexer/lex.c\0" as *const u8 as *const ::core::ffi::c_char,
            696 as ::core::ffi::c_int,
            b"ttype_from_string(\"=\") == TT_ASSIGN\0" as *const u8
                as *const ::core::ffi::c_char,
        );
    };
    if ttype_from_string(b"1\0" as *const u8 as *const ::core::ffi::c_char)
        as ::core::ffi::c_uint == TT_LITERAL as ::core::ffi::c_int as ::core::ffi::c_uint
    {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/lexer/lex.c\0" as *const u8 as *const ::core::ffi::c_char,
            698 as ::core::ffi::c_int,
            b"ttype_from_string(\"1\") == TT_LITERAL\0" as *const u8
                as *const ::core::ffi::c_char,
        );
    };
    if ttype_from_string(b"1.2\0" as *const u8 as *const ::core::ffi::c_char)
        as ::core::ffi::c_uint == TT_LITERAL as ::core::ffi::c_int as ::core::ffi::c_uint
    {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/lexer/lex.c\0" as *const u8 as *const ::core::ffi::c_char,
            699 as ::core::ffi::c_int,
            b"ttype_from_string(\"1.2\") == TT_LITERAL\0" as *const u8
                as *const ::core::ffi::c_char,
        );
    };
    if ttype_from_string(b"1u\0" as *const u8 as *const ::core::ffi::c_char)
        as ::core::ffi::c_uint == TT_LITERAL as ::core::ffi::c_int as ::core::ffi::c_uint
    {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/lexer/lex.c\0" as *const u8 as *const ::core::ffi::c_char,
            701 as ::core::ffi::c_int,
            b"ttype_from_string(\"1u\") == TT_LITERAL\0" as *const u8
                as *const ::core::ffi::c_char,
        );
    };
    if ttype_from_string(b"1.2f\0" as *const u8 as *const ::core::ffi::c_char)
        as ::core::ffi::c_uint == TT_LITERAL as ::core::ffi::c_int as ::core::ffi::c_uint
    {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/lexer/lex.c\0" as *const u8 as *const ::core::ffi::c_char,
            702 as ::core::ffi::c_int,
            b"ttype_from_string(\"1.2f\") == TT_LITERAL\0" as *const u8
                as *const ::core::ffi::c_char,
        );
    };
    if ttype_from_string(b"1.f\0" as *const u8 as *const ::core::ffi::c_char)
        as ::core::ffi::c_uint == TT_LITERAL as ::core::ffi::c_int as ::core::ffi::c_uint
    {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/lexer/lex.c\0" as *const u8 as *const ::core::ffi::c_char,
            703 as ::core::ffi::c_int,
            b"ttype_from_string(\"1.f\") == TT_LITERAL\0" as *const u8
                as *const ::core::ffi::c_char,
        );
    };
    if ttype_from_string(b"\"Planck\"\0" as *const u8 as *const ::core::ffi::c_char)
        as ::core::ffi::c_uint == TT_LITERAL as ::core::ffi::c_int as ::core::ffi::c_uint
    {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/lexer/lex.c\0" as *const u8 as *const ::core::ffi::c_char,
            705 as ::core::ffi::c_int,
            b"ttype_from_string(\"\\\"Planck\\\"\") == TT_LITERAL\0" as *const u8
                as *const ::core::ffi::c_char,
        );
    };
    if ttype_from_string(b"'Language'\0" as *const u8 as *const ::core::ffi::c_char)
        as ::core::ffi::c_uint == TT_LITERAL as ::core::ffi::c_int as ::core::ffi::c_uint
    {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/lexer/lex.c\0" as *const u8 as *const ::core::ffi::c_char,
            706 as ::core::ffi::c_int,
            b"ttype_from_string(\"'Language'\") == TT_LITERAL\0" as *const u8
                as *const ::core::ffi::c_char,
        );
    };
    if ttype_from_string(b"Jaba\0" as *const u8 as *const ::core::ffi::c_char)
        as ::core::ffi::c_uint
        == TT_IDENTIFIER as ::core::ffi::c_int as ::core::ffi::c_uint
    {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/lexer/lex.c\0" as *const u8 as *const ::core::ffi::c_char,
            708 as ::core::ffi::c_int,
            b"ttype_from_string(\"Jaba\") == TT_IDENTIFIER\0" as *const u8
                as *const ::core::ffi::c_char,
        );
    };
    if ttype_from_string(b"cat_\0" as *const u8 as *const ::core::ffi::c_char)
        as ::core::ffi::c_uint
        == TT_IDENTIFIER as ::core::ffi::c_int as ::core::ffi::c_uint
    {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/lexer/lex.c\0" as *const u8 as *const ::core::ffi::c_char,
            709 as ::core::ffi::c_int,
            b"ttype_from_string(\"cat_\") == TT_IDENTIFIER\0" as *const u8
                as *const ::core::ffi::c_char,
        );
    };
    if ttype_from_string(b"(\0" as *const u8 as *const ::core::ffi::c_char)
        as ::core::ffi::c_uint == TT_OPAREN as ::core::ffi::c_int as ::core::ffi::c_uint
    {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/lexer/lex.c\0" as *const u8 as *const ::core::ffi::c_char,
            711 as ::core::ffi::c_int,
            b"ttype_from_string(\"(\") == TT_OPAREN\0" as *const u8
                as *const ::core::ffi::c_char,
        );
    };
    if ttype_from_string(b"}\0" as *const u8 as *const ::core::ffi::c_char)
        as ::core::ffi::c_uint == TT_CBRACE as ::core::ffi::c_int as ::core::ffi::c_uint
    {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/lexer/lex.c\0" as *const u8 as *const ::core::ffi::c_char,
            712 as ::core::ffi::c_int,
            b"ttype_from_string(\"}\") == TT_CBRACE\0" as *const u8
                as *const ::core::ffi::c_char,
        );
    };
    if ttype_from_string(b";\0" as *const u8 as *const ::core::ffi::c_char)
        as ::core::ffi::c_uint == TT_SEMI as ::core::ffi::c_int as ::core::ffi::c_uint
    {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/lexer/lex.c\0" as *const u8 as *const ::core::ffi::c_char,
            714 as ::core::ffi::c_int,
            b"ttype_from_string(\";\") == TT_SEMI\0" as *const u8
                as *const ::core::ffi::c_char,
        );
    };
    return 0 as ::core::ffi::c_int;
}
#[no_mangle]
pub unsafe extern "C" fn test_lexer() -> ::core::ffi::c_int {
    testing_setup_internal(b"test_lexer\0" as *const u8 as *const ::core::ffi::c_char);
    test_ttype_name();
    test_ttype_from_string();
    test_ttype_many_chars();
    test_ttype_one_char();
    testing_cleanup_internal(b"test_lexer\0" as *const u8 as *const ::core::ffi::c_char);
    return 0 as ::core::ffi::c_int;
}
#[no_mangle]
pub unsafe extern "C" fn create_list(mut blocksize: ::core::ffi::c_int) -> *mut List {
    let mut l = malloc(::core::mem::size_of::<List>() as size_t) as *mut List;
    if l.is_null() {
        fprintf(
            stderr,
            b"\x1B[%dm\0" as *const u8 as *const ::core::ffi::c_char,
            31 as ::core::ffi::c_int,
        );
        fprintf(
            stderr,
            b"Error: jccc: internal: failed to allocate memory\n\0" as *const u8
                as *const ::core::ffi::c_char,
        );
        fprintf(stderr, b"\x1B[0m\0" as *const u8 as *const ::core::ffi::c_char);
        return ::core::ptr::null_mut::<List>();
    }
    (*l).blocksize = blocksize;
    (*l).tail = ::core::ptr::null_mut::<ListBlock>();
    (*l).head = (*l).tail;
    return l as *mut List;
}
#[no_mangle]
pub unsafe extern "C" fn destroy_list(mut l: *mut List) -> ::core::ffi::c_int {
    let mut lb = (*l).head;
    let mut next = ::core::ptr::null_mut::<ListBlock>();
    while !lb.is_null() {
        next = (*lb).next as *mut ListBlock;
        free((*lb).array as *mut ::core::ffi::c_void);
        free(lb as *mut ::core::ffi::c_void);
        lb = next;
    }
    free(l as *mut ::core::ffi::c_void);
    return 0 as ::core::ffi::c_int;
}
unsafe extern "C" fn lfind_index(
    mut l: *mut List,
    mut lb: *mut *mut ListBlock,
    mut i: *mut ::core::ffi::c_int,
) -> ::core::ffi::c_int {
    *lb = (*l).head;
    if *i < 0 as ::core::ffi::c_int {
        fprintf(
            stderr,
            b"\x1B[%dm\0" as *const u8 as *const ::core::ffi::c_char,
            31 as ::core::ffi::c_int,
        );
        fprintf(
            stderr,
            b"Error: jccc: internal: list index was negative (%d)\n\0" as *const u8
                as *const ::core::ffi::c_char,
            *i,
        );
        fprintf(stderr, b"\x1B[0m\0" as *const u8 as *const ::core::ffi::c_char);
        return -(1 as ::core::ffi::c_int);
    }
    while *i >= (**lb).size {
        if !lb.is_null() {
            *lb = (**lb).next as *mut ListBlock;
            *i -= (**lb).size;
        } else {
            fprintf(
                stderr,
                b"\x1B[%dm\0" as *const u8 as *const ::core::ffi::c_char,
                31 as ::core::ffi::c_int,
            );
            fprintf(
                stderr,
                b"Error: jccc: internal: list index %d out of bounds\n\0" as *const u8
                    as *const ::core::ffi::c_char,
                *i,
            );
            fprintf(stderr, b"\x1B[0m\0" as *const u8 as *const ::core::ffi::c_char);
            return -(1 as ::core::ffi::c_int);
        }
    }
    return 0 as ::core::ffi::c_int;
}
#[no_mangle]
pub unsafe extern "C" fn lget_element(
    mut l: *mut List,
    mut index: ::core::ffi::c_int,
) -> ::core::ffi::c_int {
    let mut i = index;
    let mut lb = ::core::ptr::null_mut::<ListBlock>();
    lfind_index(l, &raw mut lb, &raw mut i);
    if i >= (*lb).full {
        fprintf(
            stderr,
            b"\x1B[%dm\0" as *const u8 as *const ::core::ffi::c_char,
            31 as ::core::ffi::c_int,
        );
        fprintf(
            stderr,
            b"Error: jccc: internal: list index %d out of bounds\n\0" as *const u8
                as *const ::core::ffi::c_char,
            index,
        );
        fprintf(stderr, b"\x1B[0m\0" as *const u8 as *const ::core::ffi::c_char);
        return -(1 as ::core::ffi::c_int);
    }
    return *(*lb).array.offset(i as isize);
}
#[no_mangle]
pub unsafe extern "C" fn lset_element(
    mut l: *mut List,
    mut index: ::core::ffi::c_int,
    mut value: ::core::ffi::c_int,
) -> ::core::ffi::c_int {
    let mut i = index;
    let mut ret: ::core::ffi::c_int = 0;
    let mut lb = ::core::ptr::null_mut::<ListBlock>();
    ret = lfind_index(l, &raw mut lb, &raw mut i);
    if ret != 0 {
        return ret;
    }
    if i >= (*lb).full {
        fprintf(
            stderr,
            b"\x1B[%dm\0" as *const u8 as *const ::core::ffi::c_char,
            31 as ::core::ffi::c_int,
        );
        fprintf(
            stderr,
            b"Error: jccc: internal: list index %d out of bounds\n\0" as *const u8
                as *const ::core::ffi::c_char,
            index,
        );
        fprintf(stderr, b"\x1B[0m\0" as *const u8 as *const ::core::ffi::c_char);
        return -(1 as ::core::ffi::c_int);
    }
    *(*lb).array.offset(i as isize) = value;
    return 0 as ::core::ffi::c_int;
}
unsafe extern "C" fn new_block(mut l: *mut List) -> *mut ListBlock {
    let mut lb = malloc(::core::mem::size_of::<ListBlock>() as size_t) as *mut ListBlock;
    if lb.is_null() {
        return ::core::ptr::null_mut::<ListBlock>();
    }
    (*lb).array = malloc(
        ((*l).blocksize as size_t)
            .wrapping_mul(::core::mem::size_of::<*mut ::core::ffi::c_void>() as size_t),
    ) as *mut ::core::ffi::c_int;
    if (*lb).array.is_null() {
        free(lb as *mut ::core::ffi::c_void);
        return ::core::ptr::null_mut::<ListBlock>();
    }
    (*lb).full = 0 as ::core::ffi::c_int;
    (*lb).size = (*l).blocksize;
    (*lb).next = ::core::ptr::null_mut::<ListBlock>();
    return lb;
}
#[no_mangle]
pub unsafe extern "C" fn ladd_element(
    mut l: *mut List,
    mut element: ::core::ffi::c_int,
) -> ::core::ffi::c_int {
    if (*l).head.is_null() {
        (*l).tail = new_block(l);
        (*l).head = (*l).tail;
    }
    let mut lb = (*l).tail;
    if (*lb).full < (*lb).size {
        let fresh3 = (*lb).full;
        (*lb).full = (*lb).full + 1;
        *(*lb).array.offset(fresh3 as isize) = element;
    } else {
        (*l).tail = new_block(l);
        (*lb).next = (*l).tail as *mut ListBlock;
        lb = (*lb).next as *mut ListBlock;
        let fresh4 = (*lb).full;
        (*lb).full = (*lb).full + 1;
        *(*lb).array.offset(fresh4 as isize) = element;
    }
    return 0 as ::core::ffi::c_int;
}
#[no_mangle]
pub unsafe extern "C" fn parse(
    mut filename: *const ::core::ffi::c_char,
) -> ::core::ffi::c_int {
    let mut lexer = Lexer {
        fp: ::core::ptr::null_mut::<FILE>(),
        current_file: [0; 256],
        buffer: [0; 1],
        position: 0,
        last_column: 0,
        column: 0,
        line: 0,
        unlexed: [Token {
            type_0: TT_LITERAL,
            contents: [0; 256],
            length: 0,
            source_file: [0; 256],
            line: 0,
            column: 0,
        }; 5],
        unlexed_count: 0,
    };
    let mut fp = fopen(filename, b"r\0" as *const u8 as *const ::core::ffi::c_char);
    if fp.is_null() {
        fprintf(
            stderr,
            b"\x1B[%dm\0" as *const u8 as *const ::core::ffi::c_char,
            31 as ::core::ffi::c_int,
        );
        fprintf(
            stderr,
            b"Error: jccc: File %s not found\n\0" as *const u8
                as *const ::core::ffi::c_char,
            filename,
        );
        fprintf(stderr, b"\x1B[0m\0" as *const u8 as *const ::core::ffi::c_char);
        return 1 as ::core::ffi::c_int;
    }
    lexer.fp = fp;
    lexer.unlexed_count = 0 as ::core::ffi::c_uint;
    lexer.line = 1 as ::core::ffi::c_int;
    lexer.column = lexer.line;
    let mut t = Token {
        type_0: TT_LITERAL,
        contents: [0; 256],
        length: 0,
        source_file: [0; 256],
        line: 0,
        column: 0,
    };
    let mut i = 0 as ::core::ffi::c_int;
    let mut buffer_size = 16 as ::core::ffi::c_int;
    let mut tokens = malloc(
        (buffer_size as size_t).wrapping_mul(::core::mem::size_of::<Token>() as size_t),
    ) as *mut Token;
    loop {
        if lex(&raw mut lexer, &raw mut t) != 0 {
            return 1 as ::core::ffi::c_int;
        }
        if buffer_size <= i {
            buffer_size *= 2 as ::core::ffi::c_int;
            tokens = malloc(
                (buffer_size as size_t)
                    .wrapping_mul(::core::mem::size_of::<Token>() as size_t),
            ) as *mut Token;
        }
        *tokens.offset(i as isize) = t;
        printf(
            b"Contents: %20s, type: %20s, position: %d/%d\n\0" as *const u8
                as *const ::core::ffi::c_char,
            &raw mut t.contents as *mut ::core::ffi::c_char,
            ttype_name(t.type_0),
            t.line,
            t.column,
        );
        i += 1;
        if !(t.type_0 as ::core::ffi::c_uint
            != TT_EOF as ::core::ffi::c_int as ::core::ffi::c_uint)
        {
            break;
        }
    }
    if (*tokens.offset(0 as ::core::ffi::c_int as isize)).type_0 as ::core::ffi::c_uint
        == TT_INT as ::core::ffi::c_int as ::core::ffi::c_uint
        && (*tokens.offset(1 as ::core::ffi::c_int as isize)).type_0
            as ::core::ffi::c_uint
            == TT_IDENTIFIER as ::core::ffi::c_int as ::core::ffi::c_uint
        && strcmp(
            &raw mut (*tokens.offset(1 as ::core::ffi::c_int as isize)).contents
                as *mut ::core::ffi::c_char,
            b"main\0" as *const u8 as *const ::core::ffi::c_char,
        ) == 0 as ::core::ffi::c_int
    {
        if (*tokens.offset(2 as ::core::ffi::c_int as isize)).type_0
            as ::core::ffi::c_uint
            == TT_OPAREN as ::core::ffi::c_int as ::core::ffi::c_uint
            && (*tokens.offset(3 as ::core::ffi::c_int as isize)).type_0
                as ::core::ffi::c_uint
                == TT_CPAREN as ::core::ffi::c_int as ::core::ffi::c_uint
            && (*tokens.offset(4 as ::core::ffi::c_int as isize)).type_0
                as ::core::ffi::c_uint
                == TT_OBRACE as ::core::ffi::c_int as ::core::ffi::c_uint
        {
            if (*tokens.offset(5 as ::core::ffi::c_int as isize)).type_0
                as ::core::ffi::c_uint
                == TT_RETURN as ::core::ffi::c_int as ::core::ffi::c_uint
                && (*tokens.offset(6 as ::core::ffi::c_int as isize)).type_0
                    as ::core::ffi::c_uint
                    == TT_LITERAL as ::core::ffi::c_int as ::core::ffi::c_uint
                && (*tokens.offset(7 as ::core::ffi::c_int as isize)).type_0
                    as ::core::ffi::c_uint
                    == TT_SEMI as ::core::ffi::c_int as ::core::ffi::c_uint
            {
                if (*tokens.offset(8 as ::core::ffi::c_int as isize)).type_0
                    as ::core::ffi::c_uint
                    == TT_CBRACE as ::core::ffi::c_int as ::core::ffi::c_uint
                {
                    printf(b"\n\0" as *const u8 as *const ::core::ffi::c_char);
                    let mut code_start = start_main();
                    printf(code_start);
                    let mut code_end = end_main_custom_return(
                        atoi(
                            &raw mut (*tokens.offset(6 as ::core::ffi::c_int as isize))
                                .contents as *mut ::core::ffi::c_char,
                        ),
                    );
                    printf(code_end);
                } else {
                    fprintf(
                        stderr,
                        b"\x1B[%dm\0" as *const u8 as *const ::core::ffi::c_char,
                        31 as ::core::ffi::c_int,
                    );
                    fprintf(
                        stderr,
                        b"Error: jccc: Wrong closing brace.\n\n\0" as *const u8
                            as *const ::core::ffi::c_char,
                    );
                    fprintf(
                        stderr,
                        b"\x1B[0m\0" as *const u8 as *const ::core::ffi::c_char,
                    );
                }
            } else {
                fprintf(
                    stderr,
                    b"\x1B[%dm\0" as *const u8 as *const ::core::ffi::c_char,
                    31 as ::core::ffi::c_int,
                );
                fprintf(
                    stderr,
                    b"Error: jccc: Return value is wrong.\n\n\0" as *const u8
                        as *const ::core::ffi::c_char,
                );
                fprintf(stderr, b"\x1B[0m\0" as *const u8 as *const ::core::ffi::c_char);
            }
        } else {
            fprintf(
                stderr,
                b"\x1B[%dm\0" as *const u8 as *const ::core::ffi::c_char,
                31 as ::core::ffi::c_int,
            );
            fprintf(
                stderr,
                b"Error: jccc: Wrong main function body.\n\n\0" as *const u8
                    as *const ::core::ffi::c_char,
            );
            fprintf(stderr, b"\x1B[0m\0" as *const u8 as *const ::core::ffi::c_char);
        }
    } else {
        fprintf(
            stderr,
            b"\x1B[%dm\0" as *const u8 as *const ::core::ffi::c_char,
            31 as ::core::ffi::c_int,
        );
        fprintf(
            stderr,
            b"Error: jccc: Not correct main function.\n\n\0" as *const u8
                as *const ::core::ffi::c_char,
        );
        fprintf(stderr, b"\x1B[0m\0" as *const u8 as *const ::core::ffi::c_char);
    }
    fclose(fp);
    return 0 as ::core::ffi::c_int;
}
#[no_mangle]
pub unsafe extern "C" fn parse_simple_main_func() -> ::core::ffi::c_int {
    panic!("Reached end of non-void function without returning");
}
#[no_mangle]
pub unsafe extern "C" fn parse_expr(
    mut l: *mut Lexer,
    mut ex: *mut Expression,
) -> ::core::ffi::c_int {
    panic!("Reached end of non-void function without returning");
}
#[no_mangle]
pub unsafe extern "C" fn parse_funccall(
    mut l: *mut Lexer,
    mut ex: *mut Expression,
) -> ::core::ffi::c_int {
    panic!("Reached end of non-void function without returning");
}
#[no_mangle]
pub unsafe extern "C" fn parse_blockstmt(
    mut l: *mut Lexer,
    mut bs: *mut BlockStatement,
) -> ::core::ffi::c_int {
    panic!("Reached end of non-void function without returning");
}
#[no_mangle]
pub unsafe extern "C" fn parse_funcdecl(
    mut l: *mut Lexer,
    mut fd: *mut FunctionDeclaration,
) -> ::core::ffi::c_int {
    panic!("Reached end of non-void function without returning");
}
#[no_mangle]
pub unsafe extern "C" fn make_cst(
    mut l: *mut Lexer,
    mut tree: *mut ConcreteFileTree,
) -> ::core::ffi::c_int {
    panic!("Reached end of non-void function without returning");
}
#[no_mangle]
pub unsafe extern "C" fn fnva1(
    mut value: *mut ::core::ffi::c_char,
) -> ::core::ffi::c_uint {
    let mut h = 16777619 as ::core::ffi::c_ulong;
    let mut prime = 2166136261 as ::core::ffi::c_long;
    while *value as ::core::ffi::c_int != '\0' as i32 {
        h ^= *value as ::core::ffi::c_ulong;
        h = h.wrapping_mul(prime as ::core::ffi::c_ulong);
        value = value.offset(1);
    }
    return h as ::core::ffi::c_uint;
}
#[no_mangle]
pub unsafe extern "C" fn equal_key(
    mut a: *mut ::core::ffi::c_char,
    mut b: *mut ::core::ffi::c_char,
) -> ::core::ffi::c_uint {
    return (strcmp(a, b) == 0 as ::core::ffi::c_int) as ::core::ffi::c_int
        as ::core::ffi::c_uint;
}
#[no_mangle]
pub unsafe extern "C" fn create_hashmap(
    mut capacity: ::core::ffi::c_int,
) -> *mut Hashmap {
    let mut h = malloc(::core::mem::size_of::<Hashmap>() as size_t) as *mut Hashmap;
    (*h).buckets = calloc(
        capacity as size_t,
        ::core::mem::size_of::<*mut BucketNode>() as size_t,
    ) as *mut *mut BucketNode;
    (*h).size = 0 as ::core::ffi::c_int;
    (*h).cap = capacity;
    return h;
}
#[no_mangle]
pub unsafe extern "C" fn destroy_hashmap(mut h: *mut Hashmap) {
    free((*h).buckets as *mut ::core::ffi::c_void);
    free(h as *mut ::core::ffi::c_void);
}
#[no_mangle]
pub unsafe extern "C" fn create_bucket(
    mut key: *mut ::core::ffi::c_char,
    mut value: *mut ::core::ffi::c_char,
) -> *mut BucketNode {
    let mut b = malloc(::core::mem::size_of::<BucketNode>() as size_t)
        as *mut BucketNode;
    (*b).key = key;
    (*b).value = value;
    (*b).next = ::core::ptr::null_mut::<BucketNode>();
    return b;
}
#[no_mangle]
pub unsafe extern "C" fn hm_get(
    mut h: *mut Hashmap,
    mut key: *mut ::core::ffi::c_char,
) -> *mut BucketNode {
    let mut a = fnva1(key).wrapping_rem((*h).cap as ::core::ffi::c_uint);
    let mut b = *(*h).buckets.offset(a as isize);
    if b.is_null() {
        return ::core::ptr::null_mut::<BucketNode>();
    }
    if equal_key((*b).key, key) != 0 {
        return b;
    }
    return ::core::ptr::null_mut::<BucketNode>();
}
#[no_mangle]
pub unsafe extern "C" fn hm_set(
    mut h: *mut Hashmap,
    mut key: *mut ::core::ffi::c_char,
    mut value: *mut ::core::ffi::c_char,
) -> ::core::ffi::c_int {
    let mut a = fnva1(key).wrapping_rem((*h).cap as ::core::ffi::c_uint);
    let mut b = *(*h).buckets.offset(a as isize);
    if b.is_null() {
        if (*h).size == (*h).cap {
            double_cap(h);
        }
        (*h).size += 1;
        let ref mut fresh5 = *(*h).buckets.offset(a as isize);
        *fresh5 = malloc(::core::mem::size_of::<*mut BucketNode>() as size_t)
            as *mut BucketNode;
        let ref mut fresh6 = (**(*h).buckets.offset(a as isize)).key;
        *fresh6 = key;
        let ref mut fresh7 = (**(*h).buckets.offset(a as isize)).value;
        *fresh7 = value;
        let ref mut fresh8 = (**(*h).buckets.offset(a as isize)).next;
        *fresh8 = ::core::ptr::null_mut::<BucketNode>();
        return 0 as ::core::ffi::c_int;
    } else {
        return -(1 as ::core::ffi::c_int)
    };
}
#[no_mangle]
pub unsafe extern "C" fn double_cap(mut h: *mut Hashmap) {
    let mut new_buckets = calloc(
        ((*h).cap * 2 as ::core::ffi::c_int) as size_t,
        ::core::mem::size_of::<*mut BucketNode>() as size_t,
    ) as *mut *mut BucketNode;
    let mut i = 0 as ::core::ffi::c_int;
    while i < (*h).cap {
        if !(*(*h).buckets.offset(i as isize)).is_null() {
            let mut b = *(*h).buckets.offset(i as isize);
            let mut a = fnva1((*b).key).wrapping_rem((*h).cap as ::core::ffi::c_uint);
            let ref mut fresh9 = *new_buckets.offset(a as isize);
            *fresh9 = b;
        }
        i += 1;
    }
    (*h).buckets = new_buckets;
    (*h).cap = (*h).cap * 2 as ::core::ffi::c_int;
}
#[no_mangle]
pub unsafe extern "C" fn test_hash_init() -> ::core::ffi::c_int {
    testing_single_test_internal(
        b"test_hash_init\0" as *const u8 as *const ::core::ffi::c_char,
    );
    let mut h = create_hashmap(100 as ::core::ffi::c_int);
    if (*h).size == 0 as ::core::ffi::c_int {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/util/hashmap.c\0" as *const u8 as *const ::core::ffi::c_char,
            114 as ::core::ffi::c_int,
            b"h->size == 0\0" as *const u8 as *const ::core::ffi::c_char,
        );
    };
    if (*h).cap == 100 as ::core::ffi::c_int {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/util/hashmap.c\0" as *const u8 as *const ::core::ffi::c_char,
            115 as ::core::ffi::c_int,
            b"h->cap == 100\0" as *const u8 as *const ::core::ffi::c_char,
        );
    };
    panic!("Reached end of non-void function without returning");
}
#[no_mangle]
pub unsafe extern "C" fn test_hash_init_and_store() -> ::core::ffi::c_int {
    testing_single_test_internal(
        b"test_hash_init_and_store\0" as *const u8 as *const ::core::ffi::c_char,
    );
    let mut h = create_hashmap(100 as ::core::ffi::c_int);
    if (*h).size == 0 as ::core::ffi::c_int {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/util/hashmap.c\0" as *const u8 as *const ::core::ffi::c_char,
            122 as ::core::ffi::c_int,
            b"h->size == 0\0" as *const u8 as *const ::core::ffi::c_char,
        );
    };
    if (*h).cap == 100 as ::core::ffi::c_int {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/util/hashmap.c\0" as *const u8 as *const ::core::ffi::c_char,
            123 as ::core::ffi::c_int,
            b"h->cap == 100\0" as *const u8 as *const ::core::ffi::c_char,
        );
    };
    let mut name: [::core::ffi::c_char; 5] = ::core::mem::transmute::<
        [u8; 5],
        [::core::ffi::c_char; 5],
    >(*b"jake\0");
    let mut key: [::core::ffi::c_char; 5] = ::core::mem::transmute::<
        [u8; 5],
        [::core::ffi::c_char; 5],
    >(*b"test\0");
    let mut ret = hm_set(
        h,
        &raw mut key as *mut ::core::ffi::c_char,
        &raw mut name as *mut ::core::ffi::c_char,
    );
    if ret != -(1 as ::core::ffi::c_int) {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/util/hashmap.c\0" as *const u8 as *const ::core::ffi::c_char,
            129 as ::core::ffi::c_int,
            b"ret != -1\0" as *const u8 as *const ::core::ffi::c_char,
        );
    };
    let mut ind: uint64_t = fnva1(&raw mut key as *mut ::core::ffi::c_char)
        .wrapping_rem((*h).cap as ::core::ffi::c_uint) as uint64_t;
    let mut b = *(*h).buckets.offset(ind as isize);
    if strcmp((*b).key, &raw mut key as *mut ::core::ffi::c_char)
        == 0 as ::core::ffi::c_int
    {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/util/hashmap.c\0" as *const u8 as *const ::core::ffi::c_char,
            133 as ::core::ffi::c_int,
            b"strcmp(b->key, key) == 0\0" as *const u8 as *const ::core::ffi::c_char,
        );
    };
    if (*h).size == 1 as ::core::ffi::c_int {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/util/hashmap.c\0" as *const u8 as *const ::core::ffi::c_char,
            135 as ::core::ffi::c_int,
            b"h->size == 1\0" as *const u8 as *const ::core::ffi::c_char,
        );
    };
    if (*h).cap == 100 as ::core::ffi::c_int {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/util/hashmap.c\0" as *const u8 as *const ::core::ffi::c_char,
            136 as ::core::ffi::c_int,
            b"h->cap == 100\0" as *const u8 as *const ::core::ffi::c_char,
        );
    };
    panic!("Reached end of non-void function without returning");
}
#[no_mangle]
pub unsafe extern "C" fn test_hash_set_and_get() -> ::core::ffi::c_int {
    testing_single_test_internal(
        b"test_hash_set_and_get\0" as *const u8 as *const ::core::ffi::c_char,
    );
    let mut h = create_hashmap(100 as ::core::ffi::c_int);
    let mut name: [::core::ffi::c_char; 100] = ::core::mem::transmute::<
        [u8; 100],
        [::core::ffi::c_char; 100],
    >(
        *b"jake\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0",
    );
    let mut key: [::core::ffi::c_char; 10] = ::core::mem::transmute::<
        [u8; 10],
        [::core::ffi::c_char; 10],
    >(*b"test\0\0\0\0\0\0");
    let mut ret = hm_set(
        h,
        &raw mut key as *mut ::core::ffi::c_char,
        &raw mut name as *mut ::core::ffi::c_char,
    );
    if ret != -(1 as ::core::ffi::c_int) {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/util/hashmap.c\0" as *const u8 as *const ::core::ffi::c_char,
            147 as ::core::ffi::c_int,
            b"ret != -1\0" as *const u8 as *const ::core::ffi::c_char,
        );
    };
    let mut got = hm_get(
        h,
        b"test\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    );
    if strcmp((*got).value, b"jake\0" as *const u8 as *const ::core::ffi::c_char)
        == 0 as ::core::ffi::c_int
    {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/util/hashmap.c\0" as *const u8 as *const ::core::ffi::c_char,
            150 as ::core::ffi::c_int,
            b"strcmp(got->value, \"jake\") == 0\0" as *const u8
                as *const ::core::ffi::c_char,
        );
    };
    return 0 as ::core::ffi::c_int;
}
#[no_mangle]
pub unsafe extern "C" fn test_hash_set_and_double_get() -> ::core::ffi::c_int {
    testing_single_test_internal(
        b"test_hash_set_and_double_get\0" as *const u8 as *const ::core::ffi::c_char,
    );
    let mut h = create_hashmap(100 as ::core::ffi::c_int);
    let mut name: [::core::ffi::c_char; 100] = ::core::mem::transmute::<
        [u8; 100],
        [::core::ffi::c_char; 100],
    >(
        *b"jake\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0",
    );
    let mut key: [::core::ffi::c_char; 10] = ::core::mem::transmute::<
        [u8; 10],
        [::core::ffi::c_char; 10],
    >(*b"test\0\0\0\0\0\0");
    let mut ret = hm_set(
        h,
        &raw mut key as *mut ::core::ffi::c_char,
        &raw mut name as *mut ::core::ffi::c_char,
    );
    if ret != -(1 as ::core::ffi::c_int) {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/util/hashmap.c\0" as *const u8 as *const ::core::ffi::c_char,
            163 as ::core::ffi::c_int,
            b"ret != -1\0" as *const u8 as *const ::core::ffi::c_char,
        );
    };
    double_cap(h);
    let mut got = hm_get(
        h,
        b"test\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    );
    if strcmp((*got).value, b"jake\0" as *const u8 as *const ::core::ffi::c_char)
        == 0 as ::core::ffi::c_int
    {} else {
        printf(
            b"%s:%u: failed assertion `%s'\n\0" as *const u8
                as *const ::core::ffi::c_char,
            b"src/util/hashmap.c\0" as *const u8 as *const ::core::ffi::c_char,
            168 as ::core::ffi::c_int,
            b"strcmp(got->value, \"jake\") == 0\0" as *const u8
                as *const ::core::ffi::c_char,
        );
    };
    return 0 as ::core::ffi::c_int;
}
#[no_mangle]
pub unsafe extern "C" fn basic_100_test() -> ::core::ffi::c_int {
    static mut BS: ::core::ffi::c_int = 10 as ::core::ffi::c_int;
    static mut TS: ::core::ffi::c_int = 100 as ::core::ffi::c_int;
    let mut l = create_list(BS) as *mut List;
    if l.is_null() {
        return 0 as ::core::ffi::c_int;
    }
    let mut i = 0 as ::core::ffi::c_int;
    while i < TS {
        ladd_element(l, i);
        i += 1;
    }
    let mut i_0 = 0 as ::core::ffi::c_int;
    while i_0 < TS {
        if lget_element(l, i_0) == i_0 {} else {
            printf(
                b"%s:%u: failed assertion `%s'\n\0" as *const u8
                    as *const ::core::ffi::c_char,
                b"src/util/test_list.c\0" as *const u8 as *const ::core::ffi::c_char,
                18 as ::core::ffi::c_int,
                b"lget_element(l, i) == i\0" as *const u8 as *const ::core::ffi::c_char,
            );
        };
        i_0 += 1;
    }
    destroy_list(l);
    return 0 as ::core::ffi::c_int;
}
#[no_mangle]
pub unsafe extern "C" fn test_list() -> ::core::ffi::c_int {
    testing_setup_internal(b"test_list\0" as *const u8 as *const ::core::ffi::c_char);
    basic_100_test();
    testing_cleanup_internal(b"test_list\0" as *const u8 as *const ::core::ffi::c_char);
    return 0 as ::core::ffi::c_int;
}
#[no_mangle]
pub unsafe extern "C" fn test_util() -> ::core::ffi::c_int {
    testing_setup_internal(b"test_util\0" as *const u8 as *const ::core::ffi::c_char);
    test_hash_init();
    test_hash_init_and_store();
    test_hash_set_and_get();
    test_hash_set_and_double_get();
    testing_cleanup_internal(b"test_util\0" as *const u8 as *const ::core::ffi::c_char);
    return 0 as ::core::ffi::c_int;
}
unsafe fn main_0() -> ::core::ffi::c_int {
    test_lexer();
    test_x86();
    test_list();
    test_util();
    return 0 as ::core::ffi::c_int;
}
pub fn main() {
    unsafe { ::std::process::exit(main_0() as i32) }
}
