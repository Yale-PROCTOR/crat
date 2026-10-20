#![feature(derive_clone_copy)]
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments, non_camel_case_types)]
pub type size_t = u64;
pub struct ht_entry {
    pub key: *const i8,
    pub value: *mut ::std::ffi::c_void,
}
#[automatically_derived]
impl ::core::marker::Copy for ht_entry { }
#[automatically_derived]
impl ::core::clone::Clone for ht_entry {
    #[inline]
    fn clone(&self) -> ht_entry {
        let _: ::core::clone::AssertParamIsClone<*const i8>;
        let _: ::core::clone::AssertParamIsClone<*mut ::std::ffi::c_void>;
        *self
    }
}
pub struct ht {
    pub entries: *mut ht_entry,
    pub capacity: size_t,
    pub length: size_t,
}
#[automatically_derived]
impl ::core::marker::Copy for ht { }
#[automatically_derived]
impl ::core::clone::Clone for ht {
    #[inline]
    fn clone(&self) -> ht {
        let _: ::core::clone::AssertParamIsClone<*mut ht_entry>;
        let _: ::core::clone::AssertParamIsClone<size_t>;
        *self
    }
}
pub struct hti {
    pub key: *const i8,
    pub value: *mut ::std::ffi::c_void,
    pub _table: *mut ht,
    pub _index: size_t,
}
#[automatically_derived]
impl ::core::marker::Copy for hti { }
#[automatically_derived]
impl ::core::clone::Clone for hti {
    #[inline]
    fn clone(&self) -> hti {
        let _: ::core::clone::AssertParamIsClone<*const i8>;
        let _: ::core::clone::AssertParamIsClone<*mut ::std::ffi::c_void>;
        let _: ::core::clone::AssertParamIsClone<*mut ht>;
        let _: ::core::clone::AssertParamIsClone<size_t>;
        *self
    }
}
#[no_mangle]
pub unsafe extern "C" fn ht_length(mut table: *mut ht) -> size_t {
    return (*table).length;
}
#[no_mangle]
pub unsafe extern "C" fn ht_iterator(mut table: *mut ht) -> hti {
    let mut it =
        hti {
            key: 0 as *const i8,
            value: 0 as *mut ::std::ffi::c_void,
            _table: 0 as *mut ht,
            _index: 0,
        };
    it._table = table;
    it._index = 0 as i32 as size_t;
    return it;
}
#[no_mangle]
pub unsafe extern "C" fn ht_next(mut it: *mut hti) -> bool {
    let mut table = (*it)._table;
    while (*it)._index < (*table).capacity {
        let mut i = (*it)._index;
        (*it)._index = ((*it)._index).wrapping_add(1);
        if !((*((*table).entries).offset(i as isize)).key).is_null() {
            let mut entry = *((*table).entries).offset(i as isize);
            (*it).key = entry.key;
            (*it).value = entry.value;
            return 1 as i32 != 0;
        }
    }
    return 0 as i32 != 0;
}
