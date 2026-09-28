#![allow(dead_code, unused_mut, unused_variables, non_snake_case, non_camel_case_types)]
pub type Char = std::os::raw::c_char; pub type Int32 = std::os::raw::c_int; pub type Bool = std::os::raw::c_uchar;
unsafe extern "C" { fn strlen(_: *const std::os::raw::c_char) -> std::os::raw::c_ulong; }
unsafe extern "C" fn endsInBz2(mut name: *mut Char) -> Bool {
let mut n: Int32 = strlen(name) as Int32;
if n <= 4 as std::os::raw::c_int {
return 0 as std::os::raw::c_int as Bool
}
return (*name.offset((n - 4 as std::os::raw::c_int) as isize) as
                                std::os::raw::c_int == '.' as i32 &&
                        *name.offset((n - 3 as std::os::raw::c_int) as isize) as
                                std::os::raw::c_int == 'b' as i32 &&
                    *name.offset((n - 2 as std::os::raw::c_int) as isize) as
                            std::os::raw::c_int == 'z' as i32 &&
                *name.offset((n - 1 as std::os::raw::c_int) as isize) as
                        std::os::raw::c_int == '2' as i32) as std::os::raw::c_int as
    Bool;
}
