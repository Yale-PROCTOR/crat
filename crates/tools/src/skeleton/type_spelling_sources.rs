pub const MOTIVATING: &str = r####"
unsafe extern "C" {
    fn transform(value: f64) -> f64;
}

pub mod src {
    pub mod lib {
        #[derive(Clone, Copy)]
        pub struct cb_rgb {
            pub r: f32,
            pub g: f32,
            pub b: f32,
        }

        pub unsafe fn cb_remove_gamma_rgb(rgb: cb_rgb) -> cb_rgb {
            let result = {
                let init = cb_rgb {
                    r: crate::transform(rgb.r as f64) as f32,
                    g: crate::transform(rgb.g as f64) as f32,
                    b: crate::transform(rgb.b as f64) as f32,
                };
                init
            };
            result
        }
    }
}
"####;

pub const IMPORTS: &str = r####"
pub mod model {
    #[repr(C)]
    pub struct Direct(pub i32);

    #[repr(C)]
    pub struct Renamed(pub i32);

    #[repr(C)]
    pub struct Globbed(pub i32);
}

pub mod direct {
    use crate::model::Direct;

    pub unsafe fn make() -> i32 {
        let value = core::mem::zeroed::<Direct>();
        value.0
    }
}

pub mod renamed {
    use crate::model::Renamed as R;

    pub unsafe fn make() -> i32 {
        let value = core::mem::zeroed::<R>();
        value.0
    }
}

pub mod globbed {
    use crate::model::*;

    pub unsafe fn make() -> i32 {
        let value = core::mem::zeroed::<Globbed>();
        value.0
    }
}
"####;

pub const CANDIDATES: &str = r####"
pub mod left {
    #[repr(C)]
    pub struct Thing {
        pub value: i32,
    }
}

pub mod right {
    #[repr(C)]
    pub struct Thing {
        pub value: i32,
    }
}

pub mod aliases {
    use crate::left::Thing as Zed;
    use crate::left::Thing as Alpha;

    pub unsafe fn inferred() -> i32 {
        let value = core::mem::zeroed::<crate::left::Thing>();
        value.value
    }

    pub unsafe fn source_hint(pointer: *const Zed) -> i32 {
        (*pointer).value
    }
}

pub mod collision {
    use crate::right::Thing;

    pub unsafe fn inferred() -> i32 {
        let value = core::mem::zeroed::<crate::left::Thing>();
        value.value
    }

    pub unsafe fn use_right(value: Thing) -> i32 {
        value.value
    }
}
"####;

pub const CANDIDATE_PRECEDENCE: &str = r####"
pub mod model {
    #[repr(C)]
    pub struct Item {
        pub value: i32,
    }
}

pub mod own {
    #[repr(C)]
    pub struct Local {
        pub value: i32,
    }

    use self::Local as Alias;

    pub unsafe fn inferred() -> i32 {
        let value = core::mem::zeroed::<Local>();
        value.value
    }

    pub unsafe fn source(pointer: *const Alias) -> i32 {
        (*pointer).value
    }
}

pub mod transparent {
    pub type Transparent = crate::model::Item;

    pub unsafe fn inferred() -> i32 {
        let value = core::mem::zeroed::<crate::model::Item>();
        value.value
    }
}

pub mod namespace {
    use crate::model::Item as Name;

    #[allow(non_upper_case_globals)]
    pub const Name: i32 = 7;

    pub unsafe fn inferred() -> i32 {
        let value = core::mem::zeroed::<Name>();
        value.value
    }
}
"####;

pub const REEXPORTS: &str = r####"
pub mod api {
    mod hidden {
        #[repr(C)]
        pub struct Public {
            pub value: i32,
        }
    }

    pub use hidden::Public as Exposed;
}

pub mod consumer {
    pub mod std {}

    pub unsafe fn local() -> i32 {
        let value = core::mem::zeroed::<crate::api::Exposed>();
        value.value
    }

    pub unsafe fn external() -> usize {
        let value = ::std::hash::DefaultHasher::new();
        ::core::mem::size_of_val(&value)
    }
}
"####;

pub const LOCAL_FALLBACK_ROUTES: &str = r####"
pub(crate) mod restricted_api {
    mod hidden {
        #[repr(C)]
        pub(crate) struct Restricted {
            pub(crate) value: i32,
        }
    }

    pub(crate) use hidden::Restricted as Exposed;
}

pub mod short {
    mod hidden {
        #[repr(C)]
        pub struct Short {
            pub value: i32,
        }
    }

    pub use hidden::Short as S;
}

pub mod longer {
    pub mod route {
        pub use crate::short::S;
    }
}

pub mod alpha {
    mod hidden {
        #[repr(C)]
        pub struct Tie {
            pub value: i32,
        }
    }

    pub use hidden::Tie as T;
}

pub mod beta {
    pub use crate::alpha::T;
}

pub mod consumer {
    pub unsafe fn restricted() -> i32 {
        let value =
            core::mem::zeroed::<crate::restricted_api::Exposed>();
        value.value
    }

    pub unsafe fn shortest() -> i32 {
        let value = core::mem::zeroed::<crate::short::S>();
        value.value
    }

    pub unsafe fn tie() -> i32 {
        let value = core::mem::zeroed::<crate::alpha::T>();
        value.value
    }
}
"####;

pub const EXTERNAL_ROOT_ALIAS: &str = r####"
#![no_std]

extern crate std as rust_std;
extern crate std as alt_std;

pub mod consumer {
    pub unsafe fn external_alias() -> usize {
        let value = rust_std::hash::DefaultHasher::new();
        core::mem::size_of_val(&value)
    }
}
"####;

pub const SOURCE_PATHS: &str = r####"
pub mod model {
    #[repr(C)]
    pub struct Point {
        pub value: i32,
    }

    pub type PointAlias = Point;
}

pub mod consumer {
    use crate::model::PointAlias as P;
    use crate::model::PointAlias as LocalP;
    use crate::model::PointAlias as ReturnP;

    pub unsafe fn alias(pointer: *const P) -> i32 {
        (*pointer).value
    }

    pub unsafe fn local_alias(pointer: *const P) -> i32 {
        let local: *const LocalP = pointer;
        (*local).value
    }

    pub unsafe fn alias_id(pointer: *const P) -> *const ReturnP {
        pointer
    }

    pub unsafe fn relative(pointer: *const super::model::Point) -> i32 {
        (*pointer).value
    }
}
"####;

pub const SOURCE_HINT_EDGES: &str = r####"
pub mod model {
    #[repr(C)]
    pub struct Point {
        pub value: i32,
    }

    pub type PointAlias = Point;
    pub type PointPtr = *const Point;
}

pub mod consumer {
    use crate::model::PointAlias as P;

    pub unsafe fn qualified_alias(
        pointer: *const crate::model::PointAlias,
    ) -> i32 {
        (*pointer).value
    }

    pub unsafe fn optional_alias(pointer: *const P) -> i32 {
        if pointer.is_null() {
            0
        } else {
            (*pointer).value
        }
    }

    pub unsafe fn explicit_nominal() -> i32 {
        let value: crate::model::PointAlias =
            core::mem::zeroed::<crate::model::PointAlias>();
        value.value
    }

    pub unsafe fn hidden_pointer_alias(
        pointer: crate::model::PointPtr,
    ) -> i32 {
        (*pointer).value
    }
}
"####;

pub const DIRECT_HINTS: &str = r####"
#[repr(C)]
pub struct P {
    pub value: i32,
}

pub unsafe fn hint(pointer: *const P) -> i32 {
    (*pointer).value
}
"####;

pub const RECURSIVE_TYPES: &str = r####"
pub const WIDTH: usize = 2;

pub struct Wrap<T>(pub T);

pub type Callback =
    unsafe fn(*const i32) -> *const i32;

pub type CCallback =
    unsafe extern "C" fn(*const i32) -> *const i32;

pub unsafe fn grammar(
    singleton: (Wrap<(*const i32, &'static [i32])>,),
    array: [Wrap<i32>; WIDTH],
    callback: Callback,
    c_callback: CCallback,
) -> usize {
    let _ = singleton;
    let _ = array;
    core::mem::size_of_val(&callback)
        + core::mem::size_of_val(&c_callback)
}

pub unsafe fn higher_ranked(
    callback: for<'a> fn(&'a i32) -> &'a i32,
    value: &i32,
) -> i32 {
    *callback(value)
}
"####;

pub const POINTERS: &str = r####"
#[repr(C)]
pub struct Node {
    pub value: i32,
}

pub unsafe fn update_and_return(pointer: *mut Node) -> *mut Node {
    (*pointer).value += 1;
    pointer
}

pub unsafe fn local_pointer() -> i32 {
    let mut node = Node { value: 1 };
    let pointer = &mut node as *mut Node;
    (*pointer).value += 1;
    node.value
}
"####;

pub const COMPOUND: &str = r####"
pub mod types {
    #[repr(C)]
    pub struct A {
        pub value: i32,
    }

    #[repr(C)]
    pub struct B {
        pub value: i32,
    }
}

pub mod consumer {
    use crate::types::A as Alpha;
    use crate::types::B;

    pub unsafe fn mutate(pointer: *mut (Alpha, [B; 2])) {
        (*pointer).0.value += (*pointer).1[0].value;
    }

    pub unsafe fn local() -> i32 {
        let mut value = (
            Alpha { value: 1 },
            [B { value: 2 }, B { value: 3 }],
        );
        let pointer = &mut value as *mut (Alpha, [B; 2]);
        (*pointer).0.value += 1;
        value.0.value
    }
}
"####;

pub const RAW_IDENTIFIERS: &str = r####"
pub mod r#type {
    #[repr(C)]
    pub struct r#match {
        pub value: i32,
    }

    pub unsafe fn read(pointer: *const r#match) -> i32 {
        (*pointer).value
    }

    pub unsafe fn inferred() -> i32 {
        let value = core::mem::zeroed::<r#match>();
        value.value
    }
}
"####;

pub const QUALIFIED_RAW_FALLBACK: &str = r####"
pub mod r#type {
    #[repr(C)]
    pub struct r#match {
        pub value: i32,
    }
}

pub mod consumer {
    pub unsafe fn inferred() -> i32 {
        let value =
            core::mem::zeroed::<crate::r#type::r#match>();
        value.value
    }
}
"####;

pub const STANDARD_CONSTRUCTORS: &str = r####"
pub mod wrapped {
    unsafe extern "C" {
        fn malloc(size: usize) -> *mut i32;
    }

    pub unsafe fn read(p: *const i32) -> i32 {
        if p.is_null() {
            0
        } else {
            *p
        }
    }

    pub unsafe fn owned_id(mut p: *mut i32) -> *mut i32 {
        p
    }

    pub unsafe fn foo() -> *mut i32 {
        let p: *mut i32 =
            malloc(core::mem::size_of::<i32>());
        *p = 7;
        let q: *mut i32 = owned_id(p);
        q
    }

    pub unsafe fn allocate() -> *mut i32 {
        let p: *mut i32 =
            malloc(core::mem::size_of::<i32>());
        *p = 7;
        p
    }
}
"####;

pub const STANDARD_BARE_IMPORTS: &str = r####"
pub mod imported {
    use core::option::Option;
    use std::boxed::Box;

    unsafe extern "C" {
        fn malloc(size: usize) -> *mut i32;
    }

    pub unsafe fn read(p: *const i32) -> i32 {
        if p.is_null() {
            0
        } else {
            *p
        }
    }

    pub unsafe fn allocate() -> *mut i32 {
        let p: *mut i32 =
            malloc(core::mem::size_of::<i32>());
        *p = 7;
        p
    }
}
"####;

pub const NO_STD_OPTION_SUCCESS: &str = r####"
#![no_std]

pub unsafe fn read(p: *const i32) -> i32 {
    if p.is_null() {
        0
    } else {
        *p
    }
}
"####;

pub const NAMED_OPTIONAL_BOX: &str = r####"
pub mod model {
    #[repr(C)]
    pub struct Point {
        pub value: i32,
    }

    pub type PointAlias = Point;
}

pub mod consumer {
    use crate::model::PointAlias as P;
    use crate::model::PointAlias as LocalP;
    use crate::model::PointAlias as LocalQ;
    use crate::model::PointAlias as ReturnP;

    unsafe extern "C" {
        fn malloc(size: usize) -> *mut LocalP;
    }

    pub unsafe fn owned_id(mut p: *mut P) -> *mut ReturnP {
        p
    }

    pub unsafe fn foo() -> *mut ReturnP {
        let p: *mut LocalP =
            malloc(core::mem::size_of::<LocalP>());
        (*p).value = 7;
        let q: *mut LocalQ = owned_id(p);
        q
    }
}
"####;

pub const OPTION_COLLISION: &str = r####"
pub mod wrapped {
    pub struct Option;
    use core::option::Option as Maybe;

    pub unsafe fn read(
        first: *const i32,
        second: *const i32,
    ) -> i32 {
        if first.is_null() {
            if second.is_null() {
                0
            } else {
                *second
            }
        } else {
            *first
        }
    }
}
"####;

pub const BOX_COLLISION: &str = r####"
pub mod wrapped {
    pub struct Box;
    use std::boxed::Box as Owned;

    unsafe extern "C" {
        fn malloc(size: usize) -> *mut i32;
    }

    pub unsafe fn allocate() -> *mut i32 {
        let p: *mut i32 =
            malloc(core::mem::size_of::<i32>());
        *p = 7;
        p
    }
}
"####;

pub const RENAMED_CONSTRUCTOR_COLLISION: &str = r####"
pub mod fake {
    pub struct WrongOption;
}

pub mod renamed {
    use crate::fake::WrongOption as Option;

    pub unsafe fn read(p: *const i32) -> i32 {
        if p.is_null() {
            0
        } else {
            *p
        }
    }
}
"####;

pub const GLOB_CONSTRUCTOR_COLLISION: &str = r####"
pub mod fake {
    pub mod glob {
        pub struct Box;
    }
}

pub mod globbed {
    use crate::fake::glob::*;

    unsafe extern "C" {
        fn malloc(size: usize) -> *mut i32;
    }

    pub unsafe fn allocate() -> *mut i32 {
        let p: *mut i32 =
            malloc(core::mem::size_of::<i32>());
        *p = 7;
        p
    }
}
"####;

pub const OPTIONAL_BOX_PARTIAL_CONSTRUCTOR_COLLISION: &str = r####"
pub mod wrapped {
    pub struct Box;
    use core::option::Option;

    unsafe extern "C" {
        fn malloc(size: usize) -> *mut i32;
    }

    pub unsafe fn owned_id(mut p: *mut i32) -> *mut i32 {
        p
    }

    pub unsafe fn foo() -> *mut i32 {
        let p: *mut i32 =
            malloc(core::mem::size_of::<i32>());
        *p = 7;
        let q: *mut i32 = owned_id(p);
        q
    }
}
"####;

pub const LOCAL_BOX_COLLISION: &str = r####"
pub mod consumer {
    pub struct Box;

    unsafe extern "C" {
        fn malloc(size: usize) -> *mut i32;
        fn free(pointer: *mut core::ffi::c_void);
    }

    pub unsafe fn local_only() -> i32 {
        let first: *mut i32 =
            malloc(core::mem::size_of::<i32>());
        *first = 7;
        let second: *mut i32 =
            malloc(core::mem::size_of::<i32>());
        *second = 11;
        let value = *first + *second;
        free(first as *mut core::ffi::c_void);
        free(second as *mut core::ffi::c_void);
        value
    }
}
"####;

pub const EXTERN_PRELUDE_CONSTRUCTOR_COLLISION: &str = r####"
extern crate core as Option;

pub mod wrapped {
    pub unsafe fn read(p: *const i32) -> i32 {
        if p.is_null() {
            0
        } else {
            *p
        }
    }
}
"####;

pub const IRRELEVANT_COLLISIONS: &str = r####"
pub mod box_only {
    pub struct Option;

    unsafe extern "C" {
        fn malloc(size: usize) -> *mut i32;
    }

    pub unsafe fn allocate() -> *mut i32 {
        let p: *mut i32 =
            malloc(core::mem::size_of::<i32>());
        *p = 7;
        p
    }
}

pub mod option_only {
    pub struct Box;

    pub unsafe fn read(p: *const i32) -> i32 {
        if p.is_null() {
            0
        } else {
            *p
        }
    }
}
"####;

pub const NO_IMPLICIT_PRELUDE_REJECTION: &str = r####"
#![no_implicit_prelude]

extern crate core;

pub mod wrapped {
    use crate::core::option::Option;

    pub unsafe fn read(p: *const i32) -> i32 {
        if p.is_null() {
            0
        } else {
            *p
        }
    }
}
"####;

pub const NO_STD_BOX_REJECTION: &str = r####"
#![no_std]

unsafe extern "C" {
    fn malloc(size: usize) -> *mut i32;
}

pub unsafe fn allocate() -> *mut i32 {
    let p: *mut i32 =
        malloc(core::mem::size_of::<i32>());
    *p = 7;
    p
}
"####;

pub const BOX_NO_IMPLICIT_PRELUDE_REJECTION: &str = r####"
#![no_implicit_prelude]

extern crate core;

unsafe extern "C" {
    fn malloc(size: usize) -> *mut i32;
}

pub unsafe fn allocate() -> *mut i32 {
    let p: *mut i32 =
        malloc(core::mem::size_of::<i32>());
    *p = 7;
    p
}
"####;

pub const MODULE_NO_IMPLICIT_PRELUDE_REJECTION: &str = r####"
#[no_implicit_prelude]
pub mod wrapped {
    pub unsafe fn read(p: *const i32) -> i32 {
        if p.is_null() {
            0
        } else {
            *p
        }
    }
}
"####;

pub const ANCESTOR_NO_IMPLICIT_PRELUDE_REJECTION: &str = r####"
#[no_implicit_prelude]
pub mod outer {
    pub mod middle {
        pub mod inner {
            pub unsafe fn read(p: *const i32) -> i32 {
                if p.is_null() {
                    0
                } else {
                    *p
                }
            }
        }
    }
}
"####;

pub const PRESERVED_PARENT: &str = r####"
pub struct Local {
    pub value: i32,
}

pub unsafe fn preserved(flag: bool) -> i32 {
    if flag {
        let value = Local { value: 1 };
        value.value
    } else {
        0
    }
}
"####;

pub const UNNAMEABLE: &str = r####"
pub fn values() -> impl Iterator<Item = i32> {
    0..3
}

pub unsafe fn consume() {
    let iterator = values();
    core::mem::drop(iterator);
}
"####;

pub const TREE: &str = r####"
#[repr(C)]
pub struct Tree {
    root_id: i32,
}

pub unsafe fn tree_print_helper(tree: *mut Tree, root_id: i32) {
    (*tree).root_id = root_id;
}

pub unsafe fn caller(tree: *mut Tree) {
    tree_print_helper(tree, (*tree).root_id);
}
"####;

pub const COMPREHENSIVE: &str = r####"
const N: usize = 4;

mod model {
    pub struct Point {
        pub x: i32,
    }

    pub union Bits {
        pub i: i32,
        pub u: u32,
    }

    pub enum Mode {
        Off = 0,
        On = crate::N as isize,
    }

    pub type PointPtr = *mut Point;
    pub static ORIGIN: Point = Point { x: 0 };

    pub unsafe fn read(p: *const Point) -> i32 {
        let x = (*p).x;
        if x > 0 {
            x
        } else {
            crate::helper(x)
        }
    }
}

pub unsafe fn helper(x: i32) -> i32 {
    let mut total = 0;
    for i in 0..x {
        total += i;
    }
    if x <= 0 {
        total
    } else {
        helper(x - 1)
    }
}
"####;
