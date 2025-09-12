
use std::{
    collections::{BTreeMap, BTreeSet},
    ops::Deref,
    sync::Arc,
};

use lazy_static::lazy_static;
use rustc_abi::FieldIdx;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_index::{bit_set::DenseBitSet, IndexVec};
use rustc_middle::mir::Local;
use rustc_span::def_id::DefId;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone)]
pub struct AbsState {
    pub local: AbsLocal,
    pub args: AbsArgs,
    pub excludes: MayPathSet,
    pub null_excludes: MayPathSet,
    pub reads: MayPathSet,
    pub writes: MustPathSet,
    pub nulls: AbsNulls,
    pub nonnulls: MustLocalSet,
}

impl AbsState {
    #[inline]
    pub fn bot() -> Self {
        Self {
            local: AbsLocal::bot(),
            args: AbsArgs::bot(),
            excludes: MayPathSet::bot(),
            null_excludes: MayPathSet::bot(),
            reads: MayPathSet::bot(),
            writes: MustPathSet::bot(),
            nulls: AbsNulls::bot(),
            nonnulls: MustLocalSet::bot(),
        }
    }

    pub fn join(&self, other: &Self) -> Self {
        Self {
            local: self.local.join(&other.local),
            args: self.args.join(&other.args),
            excludes: self.excludes.join(&other.excludes),
            null_excludes: self.null_excludes.join(&other.null_excludes),
            reads: self.reads.join(&other.reads),
            writes: self.writes.join(&other.writes),
            nulls: self.nulls.join(&other.nulls),
            nonnulls: self.nonnulls.join(&other.nonnulls),
        }
    }

    pub fn widen(&self, other: &Self) -> Self {
        Self {
            local: self.local.widen(&other.local),
            args: self.args.widen(&other.args),
            excludes: self.excludes.widen(&other.excludes),
            null_excludes: self.null_excludes.widen(&other.null_excludes),
            reads: self.reads.widen(&other.reads),
            writes: self.writes.widen(&other.writes),
            nulls: self.nulls.widen(&other.nulls),
            nonnulls: self.nonnulls.widen(&other.nonnulls),
        }
    }

    pub fn ord(&self, other: &Self) -> bool {
        self.local.ord(&other.local)
            && self.args.ord(&other.args)
            && self.excludes.ord(&other.excludes)
            && self.null_excludes.ord(&other.null_excludes)
            && self.reads.ord(&other.reads)
            && self.writes.ord(&other.writes)
            && self.nulls.ord(&other.nulls)
            && self.nonnulls.ord(&other.nonnulls)
    }

    pub fn get(&self, base: AbsBase) -> Option<&AbsValue> {
        match base {
            AbsBase::Local(i) => self.local.0.get(i),
            AbsBase::Arg(i) => self.args.0.get(i),
            AbsBase::Heap => Some(&V_TOP),
            AbsBase::Null => None,
        }
    }

    pub fn get_mut(&mut self, base: AbsBase) -> Option<&mut AbsValue> {
        match base {
            AbsBase::Local(i) => self.local.0.get_mut(i),
            AbsBase::Arg(i) => self.args.0.get_mut(i),
            AbsBase::Heap => None,
            AbsBase::Null => None,
        }
    }

    pub fn add_excludes<I: Iterator<Item = AbsPath>>(&mut self, paths: I) {
        for path in paths {
            self.excludes.insert(path);
        }
    }

    pub fn add_null_excludes<I: Iterator<Item = AbsPath>>(&mut self, paths: I) {
        for path in paths {
            self.null_excludes.insert(path);
        }
    }

    pub fn add_reads<I: Iterator<Item = AbsPath>>(&mut self, paths: I) {
        for path in paths {
            if !self.writes.contains(&path) {
                self.reads.insert(path);
            }
        }
    }

    pub fn add_writes<I: Iterator<Item = AbsPath>>(
        &mut self,
        paths: I,
        ptr_params_inv: &FxHashMap<Local, ArgIdx>,
    ) -> (BTreeSet<AbsPath>, BTreeSet<Local>) {
        let mut res = BTreeSet::new();
        let mut nonnull_cands = BTreeSet::new();
        let mut locals = self.writes.iter().map(|p| p.base).collect::<FxHashSet<_>>();

        for path in paths {
            if !self.reads.contains(&path) && !self.excludes.contains(&path) {
                let l = path.base;
                let arg = ptr_params_inv.get(&l).unwrap();
                if !locals.contains(&l) && self.nulls.is_top(*arg) {
                    nonnull_cands.insert(l);
                    locals.insert(l);
                }
                self.writes.insert(path.clone());
                res.insert(path);
            }
        }

        (res, nonnull_cands)
    }

    pub fn add_null(&mut self, path: AbsPath, arg: ArgIdx, n: AbsNull) {
        if !self.reads.contains(&path) && !self.excludes.contains(&path) {
            self.nulls.set(arg, n);
        }
    }

    pub fn add_nonnulls<I: Iterator<Item = Local>>(&mut self, locals: I) {
        self.nonnulls.extend(locals);
    }
}

rustc_index::newtype_index! {
    #[orderable]
    #[debug_format = "arg{}"]
    pub struct ArgIdx {}
}

#[derive(Clone)]
pub struct AbsArgs(IndexVec<ArgIdx, AbsValue>);

impl std::fmt::Debug for AbsArgs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

impl AbsArgs {
    #[inline]
    fn bot() -> Self {
        Self(IndexVec::new())
    }

    fn join(&self, other: &Self) -> Self {
        let indices = if self.0.len() > other.0.len() {
            self.0.indices()
        } else {
            other.0.indices()
        };
        Self(
            indices
                .map(|i| match (self.0.get(i), other.0.get(i)) {
                    (Some(v1), Some(v2)) => v1.join(v2),
                    (Some(v), None) | (None, Some(v)) => v.clone(),
                    _ => unreachable!(),
                })
                .collect(),
        )
    }

    fn widen(&self, other: &Self) -> Self {
        let indices = if self.0.len() > other.0.len() {
            self.0.indices()
        } else {
            other.0.indices()
        };
        Self(
            indices
                .map(|i| match (self.0.get(i), other.0.get(i)) {
                    (Some(v1), Some(v2)) => v1.widen(v2),
                    (Some(v), None) | (None, Some(v)) => v.clone(),
                    _ => unreachable!(),
                })
                .collect(),
        )
    }

    fn ord(&self, other: &Self) -> bool {
        self.0.len() <= other.0.len() && self.0.iter().zip(other.0.iter()).all(|(x, y)| x.ord(y))
    }

    pub fn push(&mut self, v: AbsValue) -> ArgIdx {
        let idx = self.0.next_index();
        self.0.push(v);
        idx
    }

    pub fn get(&self, i: ArgIdx) -> &AbsValue {
        &self.0[i]
    }

    pub fn get_mut(&mut self, i: ArgIdx) -> &mut AbsValue {
        &mut self.0[i]
    }

    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn next_index(&self) -> ArgIdx {
        self.0.next_index()
    }

    pub fn iter(&self) -> impl Iterator<Item = &AbsValue> {
        self.0.iter()
    }

    pub fn iter_enumerated(&self) -> impl Iterator<Item = (ArgIdx, &AbsValue)> {
        self.0.iter_enumerated()
    }
}

#[derive(Clone)]
pub struct AbsLocal(IndexVec<Local, AbsValue>);

impl std::fmt::Debug for AbsLocal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

impl AbsLocal {
    #[inline]
    fn bot() -> Self {
        Self(IndexVec::new())
    }

    fn join(&self, other: &Self) -> Self {
        let indices = if self.0.len() > other.0.len() {
            self.0.indices()
        } else {
            other.0.indices()
        };
        Self(
            indices
                .map(|i| match (self.0.get(i), other.0.get(i)) {
                    (Some(v1), Some(v2)) => v1.join(v2),
                    (Some(v), None) | (None, Some(v)) => v.clone(),
                    _ => unreachable!(),
                })
                .collect(),
        )
    }

    fn widen(&self, other: &Self) -> Self {
        let indices = if self.0.len() > other.0.len() {
            self.0.indices()
        } else {
            other.0.indices()
        };
        Self(
            indices
                .map(|i| match (self.0.get(i), other.0.get(i)) {
                    (Some(v1), Some(v2)) => v1.widen(v2),
                    (Some(v), None) | (None, Some(v)) => v.clone(),
                    _ => unreachable!(),
                })
                .collect(),
        )
    }

    fn ord(&self, other: &Self) -> bool {
        let mut indices = if self.0.len() > other.0.len() {
            self.0.indices()
        } else {
            other.0.indices()
        };
        indices.all(|i| {
            let v1 = self.0.get(i).unwrap_or(&V_BOT);
            let v2 = other.0.get(i).unwrap_or(&V_BOT);
            v1.ord(v2)
        })
    }

    pub fn get(&self, i: Local) -> &AbsValue {
        self.0.get(i).unwrap_or(&V_BOT)
    }

    pub fn get_mut(&mut self, i: Local) -> &mut AbsValue {
        while self.0.next_index() <= i {
            self.0.push(AbsValue::bot());
        }
        &mut self.0[i]
    }

    pub fn set(&mut self, i: Local, v: AbsValue) {
        while self.0.next_index() < i {
            self.0.push(AbsValue::bot());
        }
        if self.0.next_index() == i {
            self.0.push(v);
        } else {
            self.0[i] = v;
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = &AbsValue> {
        self.0.iter()
    }

    pub fn clear_dead_locals(&mut self, dead_locals: &DenseBitSet<Local>) {
        for l in dead_locals.iter() {
            if l >= self.0.next_index() {
                break;
            }
            self.0[l] = AbsValue::bot();
        }
    }
}

lazy_static! {
    static ref V_BOT: AbsValue = AbsValue::new(AbsVal::bot());
    static ref V_TOP: AbsValue = AbsValue::new(AbsVal::top());
    static ref V_TOP_INT: AbsValue = AbsValue::new(AbsVal::top_int());
    static ref V_TOP_UINT: AbsValue = AbsValue::new(AbsVal::top_uint());
    static ref V_TOP_FLOAT: AbsValue = AbsValue::new(AbsVal::top_float());
    static ref V_TOP_BOOL: AbsValue = AbsValue::new(AbsVal::top_bool());
    static ref V_TOP_LIST: AbsValue = AbsValue::new(AbsVal::top_list());
    static ref V_TOP_PTR: AbsValue = AbsValue::new(AbsVal::top_ptr());
    static ref V_TOP_OPTION: AbsValue = AbsValue::new(AbsVal::top_option());
    static ref V_TOP_FN: AbsValue = AbsValue::new(AbsVal::top_fn());
    static ref V_TRUE: AbsValue = AbsValue::new(AbsVal::alpha_bool(true));
    static ref V_FALSE: AbsValue = AbsValue::new(AbsVal::alpha_bool(false));
    static ref V_HEAP: AbsValue = AbsValue::new(AbsVal::heap());
    static ref V_NULL: AbsValue = AbsValue::new(AbsVal::null());
    static ref V_HEAP_OR_NULL: AbsValue = AbsValue::new(AbsVal::heap_or_null());
    static ref V_NONE: AbsValue = AbsValue::new(AbsVal::none());
}

#[repr(transparent)]
#[derive(Clone)]
pub struct AbsValue(Arc<AbsVal>);

impl std::fmt::Debug for AbsValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl Deref for AbsValue {
    type Target = AbsVal;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl AbsValue {
    #[inline]
    fn new(val: AbsVal) -> Self {
        Self(Arc::new(val))
    }

    #[inline]
    pub fn bot() -> Self {
        V_BOT.clone()
    }

    #[inline]
    pub fn top() -> Self {
        V_TOP.clone()
    }

    #[inline]
    pub fn top_int() -> Self {
        V_TOP_INT.clone()
    }

    #[inline]
    pub fn top_uint() -> Self {
        V_TOP_UINT.clone()
    }

    #[inline]
    pub fn top_float() -> Self {
        V_TOP_FLOAT.clone()
    }

    #[inline]
    pub fn top_bool() -> Self {
        V_TOP_BOOL.clone()
    }

    #[inline]
    pub fn top_list() -> Self {
        V_TOP_LIST.clone()
    }

    #[inline]
    pub fn top_ptr() -> Self {
        V_TOP_PTR.clone()
    }

    #[inline]
    pub fn top_option() -> Self {
        V_TOP_OPTION.clone()
    }

    #[inline]
    pub fn top_fn() -> Self {
        V_TOP_FN.clone()
    }

    #[inline]
    pub fn bool_true() -> Self {
        V_TRUE.clone()
    }

    #[inline]
    pub fn bool_false() -> Self {
        V_FALSE.clone()
    }

    #[inline]
    pub fn heap() -> Self {
        V_HEAP.clone()
    }

    #[inline]
    pub fn null() -> Self {
        V_NULL.clone()
    }

    #[inline]
    pub fn heap_or_null() -> Self {
        V_HEAP_OR_NULL.clone()
    }

    #[inline]
    pub fn none() -> Self {
        V_NONE.clone()
    }

    pub fn alpha_int(n: i128) -> Self {
        Self::new(AbsVal::alpha_int(n))
    }

    pub fn alpha_uint(n: u128) -> Self {
        Self::new(AbsVal::alpha_uint(n))
    }

    pub fn alpha_float(f: f64) -> Self {
        Self::new(AbsVal::alpha_float(f))
    }

    #[inline]
    pub fn alpha_bool(b: bool) -> Self {
        if b {
            V_TRUE.clone()
        } else {
            V_FALSE.clone()
        }
    }

    pub fn alpha_list(l: Vec<AbsValue>) -> Self {
        Self::new(AbsVal::alpha_list(l))
    }

    pub fn alpha_ptr(p: AbsPlace) -> Self {
        Self::new(AbsVal::alpha_ptr(p))
    }

    pub fn alpha_fn(f: DefId) -> Self {
        Self::new(AbsVal::alpha_fn(f))
    }

    pub fn int(intv: AbsInt) -> Self {
        if intv.is_top() {
            V_TOP_INT.clone()
        } else if intv.is_bot() {
            V_BOT.clone()
        } else {
            Self::new(AbsVal::int(intv))
        }
    }

    pub fn uint(uintv: AbsUint) -> Self {
        if uintv.is_top() {
            V_TOP_UINT.clone()
        } else if uintv.is_bot() {
            V_BOT.clone()
        } else {
            Self::new(AbsVal::uint(uintv))
        }
    }

    pub fn float(floatv: AbsFloat) -> Self {
        if floatv.is_top() {
            V_TOP_FLOAT.clone()
        } else if floatv.is_bot() {
            V_BOT.clone()
        } else {
            Self::new(AbsVal::float(floatv))
        }
    }

    #[inline]
    pub fn boolean(boolv: AbsBool) -> Self {
        match boolv {
            AbsBool::Top => V_TOP_BOOL.clone(),
            AbsBool::True => V_TRUE.clone(),
            AbsBool::False => V_FALSE.clone(),
            AbsBool::Bot => V_BOT.clone(),
        }
    }

    pub fn list(listv: AbsList) -> Self {
        if listv.is_top() {
            V_TOP.clone()
        } else if listv.is_bot() {
            V_BOT.clone()
        } else {
            Self::new(AbsVal::list(listv))
        }
    }

    pub fn ptr(ptrv: AbsPtr) -> Self {
        if ptrv.is_top() {
            V_TOP_PTR.clone()
        } else if ptrv.is_bot() {
            V_BOT.clone()
        } else {
            Self::new(AbsVal::ptr(ptrv))
        }
    }

    pub fn option(optionv: AbsOption) -> Self {
        match optionv {
            AbsOption::Top => V_TOP_OPTION.clone(),
            AbsOption::None => V_NONE.clone(),
            AbsOption::Some(v) => Self::some(v),
            AbsOption::Bot => V_BOT.clone(),
        }
    }

    pub fn func(fnv: AbsFn) -> Self {
        if fnv.is_top() {
            V_TOP_FN.clone()
        } else if fnv.is_bot() {
            V_BOT.clone()
        } else {
            Self::new(AbsVal::func(fnv))
        }
    }

    pub fn some(v: AbsValue) -> Self {
        Self::new(AbsVal::some(v))
    }

    pub fn arg(i: ArgIdx) -> Self {
        Self::ptr(AbsPtr::arg(i))
    }

    #[inline]
    fn iub(iub: Iub) -> Self {
        match (iub.0.is_bot(), iub.1.is_bot(), iub.2.is_bot()) {
            (_, true, true) => Self::int(iub.0),
            (true, _, true) => Self::uint(iub.1),
            (true, true, _) => Self::boolean(iub.2),
            _ => Self::new(AbsVal::iub(iub)),
        }
    }

    #[inline]
    fn iuf(iuf: Iuf) -> Self {
        match (iuf.0.is_bot(), iuf.1.is_bot(), iuf.2.is_bot()) {
            (_, true, true) => Self::int(iuf.0),
            (true, _, true) => Self::uint(iuf.1),
            (true, true, _) => Self::float(iuf.2),
            _ => Self::new(AbsVal::iuf(iuf)),
        }
    }

    pub fn not(&self) -> Self {
        Self::iub(self.0.not())
    }

    pub fn neg(&self) -> Self {
        Self::iuf(self.0.neg())
    }

    pub fn to_i8(&self) -> Self {
        Self::int(self.0.to_i8())
    }

    pub fn to_i16(&self) -> Self {
        Self::int(self.0.to_i16())
    }

    pub fn to_i32(&self) -> Self {
        Self::int(self.0.to_i32())
    }

    pub fn to_i64(&self) -> Self {
        Self::int(self.0.to_i64())
    }

    pub fn to_i128(&self) -> Self {
        Self::int(self.0.to_i128())
    }

    pub fn to_u8(&self) -> Self {
        Self::uint(self.0.to_u8())
    }

    pub fn to_u16(&self) -> Self {
        Self::uint(self.0.to_u16())
    }

    pub fn to_u32(&self) -> Self {
        Self::uint(self.0.to_u32())
    }

    pub fn to_u64(&self) -> Self {
        Self::uint(self.0.to_u64())
    }

    pub fn to_u128(&self) -> Self {
        Self::uint(self.0.to_u128())
    }

    pub fn to_f32(&self) -> Self {
        Self::float(self.0.to_f32())
    }

    pub fn to_f64(&self) -> Self {
        Self::float(self.0.to_f64())
    }

    pub fn add(&self, other: &Self) -> Self {
        Self::iuf(self.0.add(&other.0))
    }

    pub fn sub(&self, other: &Self) -> Self {
        Self::iuf(self.0.sub(&other.0))
    }

    pub fn mul(&self, other: &Self) -> Self {
        Self::iuf(self.0.mul(&other.0))
    }

    pub fn div(&self, other: &Self) -> Self {
        Self::iuf(self.0.div(&other.0))
    }

    pub fn rem(&self, other: &Self) -> Self {
        Self::iuf(self.0.rem(&other.0))
    }

    pub fn bit_xor(&self, other: &Self) -> Self {
        Self::iub(self.0.bit_xor(&other.0))
    }

    pub fn bit_and(&self, other: &Self) -> Self {
        Self::iub(self.0.bit_and(&other.0))
    }

    pub fn bit_or(&self, other: &Self) -> Self {
        Self::iub(self.0.bit_or(&other.0))
    }

    pub fn shl(&self, other: &Self) -> Self {
        Self::iub(self.0.shl(&other.0))
    }

    pub fn shr(&self, other: &Self) -> Self {
        Self::iub(self.0.shr(&other.0))
    }

    pub fn eq(&self, other: &Self) -> Self {
        Self::boolean(self.0.eq(&other.0))
    }

    pub fn le(&self, other: &Self) -> Self {
        Self::boolean(self.0.le(&other.0))
    }

    pub fn lt(&self, other: &Self) -> Self {
        Self::boolean(self.0.lt(&other.0))
    }

    pub fn ne(&self, other: &Self) -> Self {
        Self::boolean(self.0.ne(&other.0))
    }

    pub fn ge(&self, other: &Self) -> Self {
        Self::boolean(self.0.ge(&other.0))
    }

    pub fn gt(&self, other: &Self) -> Self {
        Self::boolean(self.0.gt(&other.0))
    }

    pub fn join(&self, other: &Self) -> Self {
        if self.is_top() || other.is_top() {
            Self::top()
        } else if Arc::ptr_eq(&self.0, &other.0) || other.is_bot() {
            self.clone()
        } else if self.is_bot() {
            other.clone()
        } else {
            let intv = self.intv.join(&other.intv);
            let uintv = self.uintv.join(&other.uintv);
            let floatv = self.floatv.join(&other.floatv);
            let boolv = self.boolv.join(other.boolv);
            let listv = self.listv.join(&other.listv);
            let ptrv = self.ptrv.join(&other.ptrv);
            let optionv = self.optionv.join(&other.optionv);
            let fnv = self.fnv.join(&other.fnv);
            let is_bots = (
                intv.is_bot(),
                uintv.is_bot(),
                floatv.is_bot(),
                boolv.is_bot(),
                listv.is_bot(),
                ptrv.is_bot(),
                optionv.is_bot(),
                fnv.is_bot(),
            );
            match is_bots {
                (_, true, true, true, true, true, true, true) => Self::int(intv),
                (true, _, true, true, true, true, true, true) => Self::uint(uintv),
                (true, true, _, true, true, true, true, true) => Self::float(floatv),
                (true, true, true, _, true, true, true, true) => Self::boolean(boolv),
                (true, true, true, true, _, true, true, true) => Self::list(listv),
                (true, true, true, true, true, _, true, true) => Self::ptr(ptrv),
                (true, true, true, true, true, true, _, true) => Self::option(optionv),
                (true, true, true, true, true, true, true, _) => Self::func(fnv),
                _ => Self::new(AbsVal {
                    intv,
                    uintv,
                    floatv,
                    boolv,
                    listv,
                    ptrv,
                    optionv,
                    fnv,
                }),
            }
        }
    }

    pub fn widen(&self, other: &Self) -> Self {
        if self.is_top() || other.is_top() {
            Self::top()
        } else if Arc::ptr_eq(&self.0, &other.0) || other.is_bot() {
            self.clone()
        } else if self.is_bot() {
            other.clone()
        } else {
            let intv = self.intv.widen(&other.intv);
            let uintv = self.uintv.widen(&other.uintv);
            let floatv = self.floatv.widen(&other.floatv);
            let boolv = self.boolv.widen(other.boolv);
            let listv = self.listv.widen(&other.listv);
            let ptrv = self.ptrv.widen(&other.ptrv);
            let optionv = self.optionv.widen(&other.optionv);
            let fnv = self.fnv.widen(&other.fnv);
            let is_bots = (
                intv.is_bot(),
                uintv.is_bot(),
                floatv.is_bot(),
                boolv.is_bot(),
                listv.is_bot(),
                ptrv.is_bot(),
                optionv.is_bot(),
                fnv.is_bot(),
            );
            match is_bots {
                (_, true, true, true, true, true, true, true) => Self::int(intv),
                (true, _, true, true, true, true, true, true) => Self::uint(uintv),
                (true, true, _, true, true, true, true, true) => Self::float(floatv),
                (true, true, true, _, true, true, true, true) => Self::boolean(boolv),
                (true, true, true, true, _, true, true, true) => Self::list(listv),
                (true, true, true, true, true, _, true, true) => Self::ptr(ptrv),
                (true, true, true, true, true, true, _, true) => Self::option(optionv),
                (true, true, true, true, true, true, true, _) => Self::func(fnv),
                _ => Self::new(AbsVal {
                    intv,
                    uintv,
                    floatv,
                    boolv,
                    listv,
                    ptrv,
                    optionv,
                    fnv,
                }),
            }
        }
    }

    pub fn subst(&self, map: &BTreeMap<ArgIdx, AbsPtr>) -> Self {
        Self::new(self.0.subst(map))
    }

    pub fn make_mut(this: &mut Self) -> &mut AbsVal {
        Arc::make_mut(&mut this.0)
    }
}

#[derive(Clone)]
pub struct AbsVal {
    pub intv: AbsInt,
    pub uintv: AbsUint,
    pub floatv: AbsFloat,
    pub boolv: AbsBool,
    pub listv: AbsList,
    pub ptrv: AbsPtr,
    pub optionv: AbsOption,
    pub fnv: AbsFn,
}

impl std::fmt::Debug for AbsVal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_top() {
            return write!(f, "⊤");
        }

        let mut not_bot = false;
        if !self.intv.is_bot() {
            write!(f, "{:?}", self.intv)?;
            not_bot = true;
        }
        if !self.uintv.is_bot() {
            if not_bot {
                write!(f, " | ")?;
            }
            write!(f, "{:?}", self.uintv)?;
            not_bot = true;
        }
        if !self.floatv.is_bot() {
            if not_bot {
                write!(f, " | ")?;
            }
            write!(f, "{:?}", self.floatv)?;
            not_bot = true;
        }
        if !self.boolv.is_bot() {
            if not_bot {
                write!(f, " | ")?;
            }
            write!(f, "{:?}", self.boolv)?;
            not_bot = true;
        }
        if !self.listv.is_bot() {
            if not_bot {
                write!(f, " | ")?;
            }
            write!(f, "{:?}", self.listv)?;
            not_bot = true;
        }
        if !self.ptrv.is_bot() {
            if not_bot {
                write!(f, " | ")?;
            }
            write!(f, "{:?}", self.ptrv)?;
            not_bot = true;
        }
        if !self.optionv.is_bot() {
            if not_bot {
                write!(f, " | ")?;
            }
            write!(f, "{:?}", self.optionv)?;
            not_bot = true;
        }
        if !self.fnv.is_bot() {
            if not_bot {
                write!(f, " | ")?;
            }
            write!(f, "{:?}", self.fnv)?;
            not_bot = true;
        }
        if !not_bot {
            write!(f, "⊥")?;
        }
        Ok(())
    }
}

type Iub = (AbsInt, AbsUint, AbsBool);
type Iuf = (AbsInt, AbsUint, AbsFloat);

impl AbsVal {
    #[inline]
    fn top() -> Self {
        Self {
            intv: AbsInt::top(),
            uintv: AbsUint::top(),
            floatv: AbsFloat::top(),
            boolv: AbsBool::top(),
            listv: AbsList::top(),
            ptrv: AbsPtr::top(),
            optionv: AbsOption::top(),
            fnv: AbsFn::top(),
        }
    }

    #[inline]
    fn bot() -> Self {
        Self {
            intv: AbsInt::bot(),
            uintv: AbsUint::bot(),
            floatv: AbsFloat::bot(),
            boolv: AbsBool::bot(),
            listv: AbsList::bot(),
            ptrv: AbsPtr::bot(),
            optionv: AbsOption::bot(),
            fnv: AbsFn::bot(),
        }
    }

    #[inline]
    pub fn ord(&self, other: &Self) -> bool {
        self.intv.ord(&other.intv)
            && self.uintv.ord(&other.uintv)
            && self.floatv.ord(&other.floatv)
            && self.boolv.ord(other.boolv)
            && self.listv.ord(&other.listv)
            && self.ptrv.ord(&other.ptrv)
            && self.optionv.ord(&other.optionv)
            && self.fnv.ord(&other.fnv)
    }

    #[inline]
    pub fn is_top(&self) -> bool {
        self.intv.is_top()
            && self.uintv.is_top()
            && self.floatv.is_top()
            && self.boolv.is_top()
            && self.listv.is_top()
            && self.ptrv.is_top()
            && self.optionv.is_top()
            && self.fnv.is_top()
    }

    #[inline]
    pub fn is_bot(&self) -> bool {
        self.intv.is_bot()
            && self.uintv.is_bot()
            && self.floatv.is_bot()
            && self.boolv.is_bot()
            && self.listv.is_bot()
            && self.ptrv.is_bot()
            && self.optionv.is_bot()
            && self.fnv.is_bot()
    }

    #[inline]
    fn top_int() -> Self {
        Self {
            intv: AbsInt::top(),
            ..Self::bot()
        }
    }

    #[inline]
    fn top_uint() -> Self {
        Self {
            uintv: AbsUint::top(),
            ..Self::bot()
        }
    }

    #[inline]
    fn top_float() -> Self {
        Self {
            floatv: AbsFloat::top(),
            ..Self::bot()
        }
    }

    #[inline]
    fn top_bool() -> Self {
        Self {
            boolv: AbsBool::top(),
            ..Self::bot()
        }
    }

    #[inline]
    fn top_list() -> Self {
        Self {
            listv: AbsList::top(),
            ..Self::bot()
        }
    }

    #[inline]
    fn top_ptr() -> Self {
        Self {
            ptrv: AbsPtr::top(),
            ..Self::bot()
        }
    }

    #[inline]
    fn top_option() -> Self {
        Self {
            optionv: AbsOption::top(),
            ..Self::bot()
        }
    }

    #[inline]
    fn top_fn() -> Self {
        Self {
            fnv: AbsFn::top(),
            ..Self::bot()
        }
    }

    #[inline]
    fn heap() -> Self {
        Self::ptr(AbsPtr::heap())
    }

    #[inline]
    fn null() -> Self {
        Self::ptr(AbsPtr::null())
    }

    #[inline]
    fn heap_or_null() -> Self {
        Self::ptr(AbsPtr::heap_or_null())
    }

    #[inline]
    fn alpha_int(n: i128) -> Self {
        Self {
            intv: AbsInt::alpha(n),
            ..Self::bot()
        }
    }

    #[inline]
    fn alpha_uint(n: u128) -> Self {
        Self {
            uintv: AbsUint::alpha(n),
            ..Self::bot()
        }
    }

    #[inline]
    fn alpha_float(f: f64) -> Self {
        Self {
            floatv: AbsFloat::alpha(f),
            ..Self::bot()
        }
    }

    #[inline]
    fn alpha_bool(b: bool) -> Self {
        Self {
            boolv: AbsBool::alpha(b),
            ..Self::bot()
        }
    }

    #[inline]
    fn alpha_list(l: Vec<AbsValue>) -> Self {
        Self {
            listv: AbsList::List(l),
            ..Self::bot()
        }
    }

    #[inline]
    fn alpha_ptr(p: AbsPlace) -> Self {
        Self {
            ptrv: AbsPtr::alpha(p),
            ..Self::bot()
        }
    }

    #[inline]
    fn alpha_fn(f: DefId) -> Self {
        Self {
            fnv: AbsFn::alpha(f),
            ..Self::bot()
        }
    }

    #[inline]
    fn int(intv: AbsInt) -> Self {
        Self {
            intv,
            ..Self::bot()
        }
    }

    #[inline]
    fn uint(uintv: AbsUint) -> Self {
        Self {
            uintv,
            ..Self::bot()
        }
    }

    #[inline]
    fn float(floatv: AbsFloat) -> Self {
        Self {
            floatv,
            ..Self::bot()
        }
    }

    #[inline]
    fn list(listv: AbsList) -> Self {
        Self {
            listv,
            ..Self::bot()
        }
    }

    #[inline]
    fn ptr(ptrv: AbsPtr) -> Self {
        Self {
            ptrv,
            ..Self::bot()
        }
    }

    #[inline]
    fn option(optionv: AbsOption) -> Self {
        Self {
            optionv,
            ..Self::bot()
        }
    }

    #[inline]
    fn none() -> Self {
        Self::option(AbsOption::None)
    }

    #[inline]
    fn some(v: AbsValue) -> Self {
        Self::option(AbsOption::Some(v))
    }

    #[inline]
    fn func(fnv: AbsFn) -> Self {
        Self { fnv, ..Self::bot() }
    }

    #[inline]
    fn iub(iub: Iub) -> Self {
        let (intv, uintv, boolv) = iub;
        Self {
            intv,
            uintv,
            boolv,
            ..Self::bot()
        }
    }

    #[inline]
    fn iuf(iuf: Iuf) -> Self {
        let (intv, uintv, floatv) = iuf;
        Self {
            intv,
            uintv,
            floatv,
            ..Self::bot()
        }
    }

    #[inline]
    fn not(&self) -> Iub {
        (self.intv.not(), self.uintv.not(), self.boolv.not())
    }

    #[inline]
    fn neg(&self) -> Iuf {
        (self.intv.neg(), AbsUint::bot(), self.floatv.neg())
    }

    #[inline]
    fn to_i8(&self) -> AbsInt {
        self.intv
            .to_i8()
            .join(&self.uintv.to_i8())
            .join(&self.floatv.to_i8())
            .join(&self.boolv.to_int())
    }

    #[inline]
    fn to_i16(&self) -> AbsInt {
        self.intv
            .to_i16()
            .join(&self.uintv.to_i16())
            .join(&self.floatv.to_i16())
            .join(&self.boolv.to_int())
    }

    #[inline]
    fn to_i32(&self) -> AbsInt {
        self.intv
            .to_i32()
            .join(&self.uintv.to_i32())
            .join(&self.floatv.to_i32())
            .join(&self.boolv.to_int())
    }

    #[inline]
    fn to_i64(&self) -> AbsInt {
        self.intv
            .to_i64()
            .join(&self.uintv.to_i64())
            .join(&self.floatv.to_i64())
            .join(&self.boolv.to_int())
    }

    #[inline]
    fn to_i128(&self) -> AbsInt {
        self.intv
            .join(&self.uintv.to_i128())
            .join(&self.floatv.to_i128())
            .join(&self.boolv.to_int())
    }

    #[inline]
    fn to_u8(&self) -> AbsUint {
        self.intv
            .to_u8()
            .join(&self.uintv.to_u8())
            .join(&self.floatv.to_u8())
            .join(&self.boolv.to_uint())
    }

    #[inline]
    fn to_u16(&self) -> AbsUint {
        self.intv
            .to_u16()
            .join(&self.uintv.to_u16())
            .join(&self.floatv.to_u16())
            .join(&self.boolv.to_uint())
    }

    #[inline]
    fn to_u32(&self) -> AbsUint {
        self.intv
            .to_u32()
            .join(&self.uintv.to_u32())
            .join(&self.floatv.to_u32())
            .join(&self.boolv.to_uint())
    }

    #[inline]
    fn to_u64(&self) -> AbsUint {
        self.intv
            .to_u64()
            .join(&self.uintv.to_u64())
            .join(&self.floatv.to_u64())
            .join(&self.boolv.to_uint())
    }

    #[inline]
    fn to_u128(&self) -> AbsUint {
        self.intv
            .to_u128()
            .join(&self.uintv)
            .join(&self.floatv.to_u128())
            .join(&self.boolv.to_uint())
    }

    #[inline]
    fn to_f32(&self) -> AbsFloat {
        self.intv
            .to_f32()
            .join(&self.uintv.to_f32())
            .join(&self.floatv.to_f32())
    }

    #[inline]
    fn to_f64(&self) -> AbsFloat {
        self.intv
            .to_f64()
            .join(&self.uintv.to_f64())
            .join(&self.floatv)
    }

    #[inline]
    fn add(&self, other: &Self) -> Iuf {
        (
            self.intv.add(&other.intv),
            self.uintv.add(&other.uintv),
            self.floatv.add(&other.floatv),
        )
    }

    #[inline]
    fn sub(&self, other: &Self) -> Iuf {
        (
            self.intv.sub(&other.intv),
            self.uintv.sub(&other.uintv),
            self.floatv.sub(&other.floatv),
        )
    }

    #[inline]
    fn mul(&self, other: &Self) -> Iuf {
        (
            self.intv.mul(&other.intv),
            self.uintv.mul(&other.uintv),
            self.floatv.mul(&other.floatv),
        )
    }

    #[inline]
    fn div(&self, other: &Self) -> Iuf {
        (
            self.intv.div(&other.intv),
            self.uintv.div(&other.uintv),
            self.floatv.div(&other.floatv),
        )
    }

    #[inline]
    fn rem(&self, other: &Self) -> Iuf {
        (
            self.intv.rem(&other.intv),
            self.uintv.rem(&other.uintv),
            self.floatv.rem(&other.floatv),
        )
    }

    #[inline]
    fn bit_xor(&self, other: &Self) -> Iub {
        (
            self.intv.bit_xor(&other.intv),
            self.uintv.bit_xor(&other.uintv),
            self.boolv.bit_xor(other.boolv),
        )
    }

    #[inline]
    fn bit_and(&self, other: &Self) -> Iub {
        (
            self.intv.bit_and(&other.intv),
            self.uintv.bit_and(&other.uintv),
            self.boolv.bit_and(other.boolv),
        )
    }

    #[inline]
    fn bit_or(&self, other: &Self) -> Iub {
        (
            self.intv.bit_or(&other.intv),
            self.uintv.bit_or(&other.uintv),
            self.boolv.bit_or(other.boolv),
        )
    }

    #[inline]
    fn shl(&self, other: &Self) -> Iub {
        (
            self.intv
                .shl(&other.intv)
                .join(&self.intv.shlu(&other.uintv)),
            self.uintv
                .shl(&other.uintv)
                .join(&self.uintv.shli(&other.intv)),
            AbsBool::bot(),
        )
    }

    #[inline]
    fn shr(&self, other: &Self) -> Iub {
        (
            self.intv
                .shr(&other.intv)
                .join(&self.intv.shru(&other.uintv)),
            self.uintv
                .shr(&other.uintv)
                .join(&self.uintv.shri(&other.intv)),
            AbsBool::bot(),
        )
    }

    #[inline]
    fn eq(&self, other: &Self) -> AbsBool {
        self.intv
            .eq(&other.intv)
            .join(self.uintv.eq(&other.uintv))
            .join(self.floatv.eq(&other.floatv))
            .join(self.boolv.eq(other.boolv))
            .join(self.ptrv.compare(&other.ptrv))
    }

    #[inline]
    fn lt(&self, other: &Self) -> AbsBool {
        self.intv
            .lt(&other.intv)
            .join(self.uintv.lt(&other.uintv))
            .join(self.floatv.lt(&other.floatv))
            .join(self.ptrv.compare(&other.ptrv))
    }

    #[inline]
    fn le(&self, other: &Self) -> AbsBool {
        self.intv
            .le(&other.intv)
            .join(self.uintv.le(&other.uintv))
            .join(self.floatv.le(&other.floatv))
            .join(self.ptrv.compare(&other.ptrv))
    }

    #[inline]
    fn ne(&self, other: &Self) -> AbsBool {
        self.intv
            .ne(&other.intv)
            .join(self.uintv.ne(&other.uintv))
            .join(self.floatv.ne(&other.floatv))
            .join(self.boolv.ne(other.boolv))
            .join(self.ptrv.compare(&other.ptrv))
    }

    #[inline]
    fn ge(&self, other: &Self) -> AbsBool {
        self.intv
            .ge(&other.intv)
            .join(self.uintv.ge(&other.uintv))
            .join(self.floatv.ge(&other.floatv))
            .join(self.ptrv.compare(&other.ptrv))
    }

    #[inline]
    fn gt(&self, other: &Self) -> AbsBool {
        self.intv
            .gt(&other.intv)
            .join(self.uintv.gt(&other.uintv))
            .join(self.floatv.gt(&other.floatv))
            .join(self.ptrv.compare(&other.ptrv))
    }

    #[inline]
    fn subst(&self, map: &BTreeMap<ArgIdx, AbsPtr>) -> Self {
        Self {
            ptrv: self.ptrv.subst(map),
            listv: self.listv.subst(map),
            ..self.clone()
        }
    }
}

const MAX_SIZE: usize = 11;

#[derive(Clone, Serialize, Deserialize)]
pub enum AbsInt {
    Top,
    Set(BTreeSet<i128>),
}

impl std::fmt::Debug for AbsInt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Top => write!(f, "⊤_i"),
            Self::Set(s) => match s.len() {
                0 => write!(f, "⊥_i"),
                1 => write!(f, "{}_i", s.first().unwrap()),
                _ => {
                    write!(f, "{{")?;
                    for (i, n) in s.iter().enumerate() {
                        if i != 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", n)?;
                    }
                    write!(f, "}}_i")
                }
            },
        }
    }
}

impl AbsInt {
    #[inline]
    fn top() -> Self {
        Self::Top
    }

    #[inline]
    fn bot() -> Self {
        Self::alphas(BTreeSet::new())
    }

    #[inline]
    pub fn is_top(&self) -> bool {
        matches!(self, Self::Top)
    }

    #[inline]
    pub fn is_bot(&self) -> bool {
        if let Self::Set(s) = self {
            s.is_empty()
        } else {
            false
        }
    }

    fn alpha(n: i128) -> Self {
        Self::alphas([n].into_iter().collect())
    }

    fn alphas(set: BTreeSet<i128>) -> Self {
        if set.len() > MAX_SIZE {
            Self::Top
        } else {
            Self::Set(set)
        }
    }

    pub fn gamma(&self) -> Option<&BTreeSet<i128>> {
        if let Self::Set(s) = self {
            Some(s)
        } else {
            None
        }
    }

    fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Top, _) | (_, Self::Top) => Self::Top,
            (Self::Set(s1), Self::Set(s2)) => Self::alphas(s1.union(s2).cloned().collect()),
        }
    }

    fn widen(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Top, _) | (_, Self::Top) => Self::Top,
            (Self::Set(s1), Self::Set(s2)) => {
                if s2.is_subset(s1) {
                    self.clone()
                } else if s1.is_empty() {
                    other.clone()
                } else {
                    Self::Top
                }
            }
        }
    }

    fn ord(&self, other: &Self) -> bool {
        match (self, other) {
            (_, Self::Top) => true,
            (Self::Top, _) => false,
            (Self::Set(s1), Self::Set(s2)) => s1.is_subset(s2),
        }
    }

    fn unary<F: Fn(i128) -> i128>(&self, f: F) -> Self {
        match self {
            Self::Top => Self::Top,
            Self::Set(s) => Self::alphas(s.iter().map(|n| f(*n)).collect()),
        }
    }

    fn not(&self) -> Self {
        self.unary(|n| !n)
    }

    fn neg(&self) -> Self {
        self.unary(|n| -n)
    }

    fn to_i8(&self) -> Self {
        self.unary(|n| n as i8 as i128)
    }

    fn to_i16(&self) -> Self {
        self.unary(|n| n as i16 as i128)
    }

    fn to_i32(&self) -> Self {
        self.unary(|n| n as i32 as i128)
    }

    fn to_i64(&self) -> Self {
        self.unary(|n| n as i64 as i128)
    }

    fn unaryu<F: Fn(i128) -> u128>(&self, f: F) -> AbsUint {
        match self {
            Self::Top => AbsUint::Top,
            Self::Set(s) => AbsUint::alphas(s.iter().map(|n| f(*n)).collect()),
        }
    }

    fn to_u8(&self) -> AbsUint {
        self.unaryu(|n| n as u8 as u128)
    }

    fn to_u16(&self) -> AbsUint {
        self.unaryu(|n| n as u16 as u128)
    }

    fn to_u32(&self) -> AbsUint {
        self.unaryu(|n| n as u32 as u128)
    }

    pub fn to_u64(&self) -> AbsUint {
        self.unaryu(|n| n as u64 as u128)
    }

    fn to_u128(&self) -> AbsUint {
        self.unaryu(|n| n as u128)
    }

    fn unaryf<F: Fn(i128) -> f64>(&self, f: F) -> AbsFloat {
        match self {
            Self::Top => AbsFloat::Top,
            Self::Set(s) => AbsFloat::alphas(s.iter().map(|n| f(*n)).collect()),
        }
    }

    fn to_f32(&self) -> AbsFloat {
        self.unaryf(|n| n as f32 as f64)
    }

    fn to_f64(&self) -> AbsFloat {
        self.unaryf(|n| n as f64)
    }

    fn binary<F: Fn(i128, i128) -> i128>(&self, other: &Self, f: F) -> Self {
        match (self, other) {
            (Self::Top, _) | (_, Self::Top) => Self::Top,
            (Self::Set(s1), Self::Set(s2)) => {
                let mut set = BTreeSet::new();
                for n1 in s1 {
                    for n2 in s2 {
                        set.insert(f(*n1, *n2));
                    }
                }
                Self::alphas(set)
            }
        }
    }

    pub fn add(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 + n2)
    }

    fn sub(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 - n2)
    }

    fn mul(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 * n2)
    }

    fn binary_nz<F: Fn(i128, i128) -> i128>(&self, other: &Self, f: F) -> Self {
        match (self, other) {
            (Self::Top, _) | (_, Self::Top) => Self::Top,
            (Self::Set(s1), Self::Set(s2)) => {
                let mut set = BTreeSet::new();
                for n1 in s1 {
                    for n2 in s2 {
                        if *n2 != 0 {
                            set.insert(f(*n1, *n2));
                        }
                    }
                }
                Self::alphas(set)
            }
        }
    }

    fn div(&self, other: &Self) -> Self {
        self.binary_nz(other, |n1, n2| n1 / n2)
    }

    fn rem(&self, other: &Self) -> Self {
        self.binary_nz(other, |n1, n2| n1 % n2)
    }

    fn bit_xor(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 ^ n2)
    }

    fn bit_and(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 & n2)
    }

    fn bit_or(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 | n2)
    }

    fn shl(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 << n2)
    }

    fn shr(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 >> n2)
    }

    fn binaryu<F: Fn(i128, u128) -> i128>(&self, other: &AbsUint, f: F) -> Self {
        match (self, other) {
            (Self::Top, _) | (_, AbsUint::Top) => Self::Top,
            (Self::Set(s1), AbsUint::Set(s2)) => {
                let mut set = BTreeSet::new();
                for n1 in s1 {
                    for n2 in s2 {
                        set.insert(f(*n1, *n2));
                    }
                }
                Self::alphas(set)
            }
        }
    }

    fn shlu(&self, other: &AbsUint) -> Self {
        self.binaryu(other, |n1, n2| n1 << n2)
    }

    fn shru(&self, other: &AbsUint) -> Self {
        self.binaryu(other, |n1, n2| n1 >> n2)
    }

    fn binaryb<F: Fn(i128, i128) -> bool>(&self, other: &Self, f: F) -> AbsBool {
        match (self, other) {
            (Self::Top, _) | (_, Self::Top) => AbsBool::Top,
            (Self::Set(s1), Self::Set(s2)) => {
                let mut set = BTreeSet::new();
                for n1 in s1 {
                    for n2 in s2 {
                        set.insert(f(*n1, *n2));
                    }
                }
                AbsBool::alphas(set)
            }
        }
    }

    fn eq(&self, other: &Self) -> AbsBool {
        self.binaryb(other, |n1, n2| n1 == n2)
    }

    fn lt(&self, other: &Self) -> AbsBool {
        self.binaryb(other, |n1, n2| n1 < n2)
    }

    fn le(&self, other: &Self) -> AbsBool {
        self.binaryb(other, |n1, n2| n1 <= n2)
    }

    fn ne(&self, other: &Self) -> AbsBool {
        self.binaryb(other, |n1, n2| n1 != n2)
    }

    fn ge(&self, other: &Self) -> AbsBool {
        self.binaryb(other, |n1, n2| n1 >= n2)
    }

    fn gt(&self, other: &Self) -> AbsBool {
        self.binaryb(other, |n1, n2| n1 > n2)
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum AbsUint {
    Top,
    Set(BTreeSet<u128>),
}

impl std::fmt::Debug for AbsUint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Top => write!(f, "⊤_u"),
            Self::Set(s) => match s.len() {
                0 => write!(f, "⊥_u"),
                1 => write!(f, "{}_u", s.first().unwrap()),
                _ => {
                    write!(f, "{{")?;
                    for (i, n) in s.iter().enumerate() {
                        if i != 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", n)?;
                    }
                    write!(f, "}}_u")
                }
            },
        }
    }
}

impl AbsUint {
    #[inline]
    fn top() -> Self {
        Self::Top
    }

    #[inline]
    fn bot() -> Self {
        Self::alphas(BTreeSet::new())
    }

    #[inline]
    pub fn is_top(&self) -> bool {
        matches!(self, Self::Top)
    }

    #[inline]
    pub fn is_bot(&self) -> bool {
        if let Self::Set(s) = self {
            s.is_empty()
        } else {
            false
        }
    }

    pub fn alpha(n: u128) -> Self {
        Self::alphas([n].into_iter().collect())
    }

    fn alphas(set: BTreeSet<u128>) -> Self {
        if set.len() > MAX_SIZE {
            Self::Top
        } else {
            Self::Set(set)
        }
    }

    pub fn gamma(&self) -> Option<&BTreeSet<u128>> {
        if let Self::Set(s) = self {
            Some(s)
        } else {
            None
        }
    }

    fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Top, _) | (_, Self::Top) => Self::Top,
            (Self::Set(s1), Self::Set(s2)) => Self::alphas(s1.union(s2).cloned().collect()),
        }
    }

    fn widen(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Top, _) | (_, Self::Top) => Self::Top,
            (Self::Set(s1), Self::Set(s2)) => {
                if s2.is_subset(s1) {
                    self.clone()
                } else if s1.is_empty() {
                    other.clone()
                } else {
                    Self::Top
                }
            }
        }
    }

    fn ord(&self, other: &Self) -> bool {
        match (self, other) {
            (_, Self::Top) => true,
            (Self::Top, _) => false,
            (Self::Set(s1), Self::Set(s2)) => s1.is_subset(s2),
        }
    }

    fn unary<F: Fn(u128) -> u128>(&self, f: F) -> Self {
        match self {
            Self::Top => Self::Top,
            Self::Set(s) => Self::alphas(s.iter().map(|n| f(*n)).collect()),
        }
    }

    fn not(&self) -> Self {
        self.unary(|n| !n)
    }

    fn to_u8(&self) -> Self {
        self.unary(|n| n as u8 as u128)
    }

    fn to_u16(&self) -> Self {
        self.unary(|n| n as u16 as u128)
    }

    fn to_u32(&self) -> Self {
        self.unary(|n| n as u32 as u128)
    }

    fn to_u64(&self) -> Self {
        self.unary(|n| n as u64 as u128)
    }

    fn unaryi<F: Fn(u128) -> i128>(&self, f: F) -> AbsInt {
        match self {
            Self::Top => AbsInt::Top,
            Self::Set(s) => AbsInt::alphas(s.iter().map(|n| f(*n)).collect()),
        }
    }

    fn to_i8(&self) -> AbsInt {
        self.unaryi(|n| n as i8 as i128)
    }

    fn to_i16(&self) -> AbsInt {
        self.unaryi(|n| n as i16 as i128)
    }

    fn to_i32(&self) -> AbsInt {
        self.unaryi(|n| n as i32 as i128)
    }

    pub fn to_i64(&self) -> AbsInt {
        self.unaryi(|n| n as i64 as i128)
    }

    fn to_i128(&self) -> AbsInt {
        self.unaryi(|n| n as i128)
    }

    fn unaryf<F: Fn(u128) -> f64>(&self, f: F) -> AbsFloat {
        match self {
            Self::Top => AbsFloat::Top,
            Self::Set(s) => AbsFloat::alphas(s.iter().map(|n| f(*n)).collect()),
        }
    }

    fn to_f32(&self) -> AbsFloat {
        self.unaryf(|n| n as f32 as f64)
    }

    fn to_f64(&self) -> AbsFloat {
        self.unaryf(|n| n as f64)
    }

    fn binary<F: Fn(u128, u128) -> u128>(&self, other: &Self, f: F) -> Self {
        match (self, other) {
            (Self::Top, _) | (_, Self::Top) => Self::Top,
            (Self::Set(s1), Self::Set(s2)) => {
                let mut set = BTreeSet::new();
                for n1 in s1 {
                    for n2 in s2 {
                        set.insert(f(*n1, *n2));
                    }
                }
                Self::alphas(set)
            }
        }
    }

    fn add(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 + n2)
    }

    fn sub(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 - n2)
    }

    fn mul(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 * n2)
    }

    fn binary_nz<F: Fn(u128, u128) -> u128>(&self, other: &Self, f: F) -> Self {
        match (self, other) {
            (Self::Top, _) | (_, Self::Top) => Self::Top,
            (Self::Set(s1), Self::Set(s2)) => {
                let mut set = BTreeSet::new();
                for n1 in s1 {
                    for n2 in s2 {
                        if *n2 != 0 {
                            set.insert(f(*n1, *n2));
                        }
                    }
                }
                Self::alphas(set)
            }
        }
    }

    fn div(&self, other: &Self) -> Self {
        self.binary_nz(other, |n1, n2| n1 / n2)
    }

    fn rem(&self, other: &Self) -> Self {
        self.binary_nz(other, |n1, n2| n1 % n2)
    }

    fn bit_xor(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 ^ n2)
    }

    fn bit_and(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 & n2)
    }

    fn bit_or(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 | n2)
    }

    fn shl(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 << n2)
    }

    fn shr(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 >> n2)
    }

    fn binaryi<F: Fn(u128, i128) -> u128>(&self, other: &AbsInt, f: F) -> Self {
        match (self, other) {
            (Self::Top, _) | (_, AbsInt::Top) => Self::Top,
            (Self::Set(s1), AbsInt::Set(s2)) => {
                let mut set = BTreeSet::new();
                for n1 in s1 {
                    for n2 in s2 {
                        set.insert(f(*n1, *n2));
                    }
                }
                Self::alphas(set)
            }
        }
    }

    fn shli(&self, other: &AbsInt) -> Self {
        self.binaryi(other, |n1, n2| n1 << n2)
    }

    fn shri(&self, other: &AbsInt) -> Self {
        self.binaryi(other, |n1, n2| n1 >> n2)
    }

    fn binaryb<F: Fn(u128, u128) -> bool>(&self, other: &Self, f: F) -> AbsBool {
        match (self, other) {
            (Self::Top, _) | (_, Self::Top) => AbsBool::Top,
            (Self::Set(s1), Self::Set(s2)) => {
                let mut set = BTreeSet::new();
                for n1 in s1 {
                    for n2 in s2 {
                        set.insert(f(*n1, *n2));
                    }
                }
                AbsBool::alphas(set)
            }
        }
    }

    fn eq(&self, other: &Self) -> AbsBool {
        self.binaryb(other, |n1, n2| n1 == n2)
    }

    fn lt(&self, other: &Self) -> AbsBool {
        self.binaryb(other, |n1, n2| n1 < n2)
    }

    fn le(&self, other: &Self) -> AbsBool {
        self.binaryb(other, |n1, n2| n1 <= n2)
    }

    fn ne(&self, other: &Self) -> AbsBool {
        self.binaryb(other, |n1, n2| n1 != n2)
    }

    fn ge(&self, other: &Self) -> AbsBool {
        self.binaryb(other, |n1, n2| n1 >= n2)
    }

    fn gt(&self, other: &Self) -> AbsBool {
        self.binaryb(other, |n1, n2| n1 > n2)
    }
}

#[derive(Clone)]
pub enum AbsFloat {
    Top,
    Set(BTreeSet<u64>),
}

impl std::fmt::Debug for AbsFloat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Top => write!(f, "⊤_f"),
            Self::Set(s) => match s.len() {
                0 => write!(f, "⊥_f"),
                1 => write!(f, "{}_f", f64::from_bits(*s.first().unwrap())),
                _ => {
                    write!(f, "{{")?;
                    for (i, n) in s.iter().enumerate() {
                        if i != 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", f64::from_bits(*n))?;
                    }
                    write!(f, "}}_f")
                }
            },
        }
    }
}

impl AbsFloat {
    #[inline]
    fn top() -> Self {
        Self::Top
    }

    fn new(set: BTreeSet<u64>) -> Self {
        if set.len() > MAX_SIZE {
            Self::Top
        } else {
            Self::Set(set)
        }
    }

    #[inline]
    pub fn is_top(&self) -> bool {
        matches!(self, Self::Top)
    }

    #[inline]
    fn bot() -> Self {
        Self::new(BTreeSet::new())
    }

    #[inline]
    pub fn is_bot(&self) -> bool {
        if let Self::Set(s) = self {
            s.is_empty()
        } else {
            false
        }
    }

    fn alpha(n: f64) -> Self {
        Self::new([n.to_bits()].into_iter().collect())
    }

    fn alphas(v: Vec<f64>) -> Self {
        Self::new(v.into_iter().map(|n| n.to_bits()).collect())
    }

    pub fn gamma(&self) -> Option<Vec<f64>> {
        if let Self::Set(s) = self {
            Some(s.iter().map(|n| f64::from_bits(*n)).collect())
        } else {
            None
        }
    }

    fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Top, _) | (_, Self::Top) => Self::Top,
            (Self::Set(s1), Self::Set(s2)) => Self::new(s1.union(s2).cloned().collect()),
        }
    }

    fn widen(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Top, _) | (_, Self::Top) => Self::Top,
            (Self::Set(s1), Self::Set(s2)) => {
                if s2.is_subset(s1) {
                    self.clone()
                } else if s1.is_empty() {
                    other.clone()
                } else {
                    Self::Top
                }
            }
        }
    }

    fn ord(&self, other: &Self) -> bool {
        match (self, other) {
            (_, Self::Top) => true,
            (Self::Top, _) => false,
            (Self::Set(s1), Self::Set(s2)) => s1.is_subset(s2),
        }
    }

    fn unary<F: Fn(f64) -> f64>(&self, f: F) -> Self {
        match self {
            Self::Top => Self::Top,
            Self::Set(s) => Self::new(s.iter().map(|n| f(f64::from_bits(*n)).to_bits()).collect()),
        }
    }

    fn neg(&self) -> Self {
        self.unary(|n| -n)
    }

    fn to_f32(&self) -> Self {
        self.unary(|n| n as f32 as f64)
    }

    fn unaryi<F: Fn(f64) -> i128>(&self, f: F) -> AbsInt {
        match self {
            Self::Top => AbsInt::Top,
            Self::Set(s) => AbsInt::alphas(s.iter().map(|n| f(f64::from_bits(*n))).collect()),
        }
    }

    fn to_i8(&self) -> AbsInt {
        self.unaryi(|n| n as i8 as i128)
    }

    fn to_i16(&self) -> AbsInt {
        self.unaryi(|n| n as i16 as i128)
    }

    fn to_i32(&self) -> AbsInt {
        self.unaryi(|n| n as i32 as i128)
    }

    fn to_i64(&self) -> AbsInt {
        self.unaryi(|n| n as i64 as i128)
    }

    fn to_i128(&self) -> AbsInt {
        self.unaryi(|n| n as i128)
    }

    fn unaryu<F: Fn(f64) -> u128>(&self, f: F) -> AbsUint {
        match self {
            Self::Top => AbsUint::Top,
            Self::Set(s) => AbsUint::alphas(s.iter().map(|n| f(f64::from_bits(*n))).collect()),
        }
    }

    fn to_u8(&self) -> AbsUint {
        self.unaryu(|n| n as u8 as u128)
    }

    fn to_u16(&self) -> AbsUint {
        self.unaryu(|n| n as u16 as u128)
    }

    fn to_u32(&self) -> AbsUint {
        self.unaryu(|n| n as u32 as u128)
    }

    fn to_u64(&self) -> AbsUint {
        self.unaryu(|n| n as u64 as u128)
    }

    fn to_u128(&self) -> AbsUint {
        self.unaryu(|n| n as u128)
    }

    fn binary<F: Fn(f64, f64) -> f64>(&self, other: &Self, f: F) -> Self {
        match (self, other) {
            (Self::Top, _) | (_, Self::Top) => Self::Top,
            (Self::Set(s1), Self::Set(s2)) => {
                let mut set = BTreeSet::new();
                for n1 in s1 {
                    for n2 in s2 {
                        set.insert(f(f64::from_bits(*n1), f64::from_bits(*n2)).to_bits());
                    }
                }
                Self::new(set)
            }
        }
    }

    fn add(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 + n2)
    }

    fn sub(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 - n2)
    }

    fn mul(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 * n2)
    }

    fn div(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 / n2)
    }

    fn rem(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 % n2)
    }

    fn binaryb<F: Fn(f64, f64) -> bool>(&self, other: &Self, f: F) -> AbsBool {
        match (self, other) {
            (Self::Top, _) | (_, Self::Top) => AbsBool::Top,
            (Self::Set(s1), Self::Set(s2)) => {
                let mut set = BTreeSet::new();
                for n1 in s1 {
                    for n2 in s2 {
                        set.insert(f(f64::from_bits(*n1), f64::from_bits(*n2)));
                    }
                }
                AbsBool::alphas(set)
            }
        }
    }

    fn eq(&self, other: &Self) -> AbsBool {
        self.binaryb(other, |n1, n2| n1 == n2)
    }

    fn lt(&self, other: &Self) -> AbsBool {
        self.binaryb(other, |n1, n2| n1 < n2)
    }

    fn le(&self, other: &Self) -> AbsBool {
        self.binaryb(other, |n1, n2| n1 <= n2)
    }

    fn ne(&self, other: &Self) -> AbsBool {
        self.binaryb(other, |n1, n2| n1 != n2)
    }

    fn ge(&self, other: &Self) -> AbsBool {
        self.binaryb(other, |n1, n2| n1 >= n2)
    }

    fn gt(&self, other: &Self) -> AbsBool {
        self.binaryb(other, |n1, n2| n1 > n2)
    }
}

#[derive(Clone, Copy, Serialize, Deserialize)]
pub enum AbsBool {
    Top,
    True,
    False,
    Bot,
}

impl std::fmt::Debug for AbsBool {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Top => write!(f, "⊤_b"),
            Self::True => write!(f, "#t"),
            Self::False => write!(f, "#f"),
            Self::Bot => write!(f, "⊥_b"),
        }
    }
}

impl AbsBool {
    #[inline]
    fn top() -> Self {
        Self::Top
    }

    #[inline]
    fn bot() -> Self {
        Self::Bot
    }

    #[inline]
    pub fn is_top(self) -> bool {
        matches!(self, Self::Top)
    }

    #[inline]
    pub fn is_bot(self) -> bool {
        matches!(self, Self::Bot)
    }

    fn alpha(b: bool) -> Self {
        if b {
            Self::True
        } else {
            Self::False
        }
    }

    pub fn gamma(self) -> Vec<bool> {
        match self {
            Self::Top => vec![true, false],
            Self::True => vec![true],
            Self::False => vec![false],
            Self::Bot => vec![],
        }
    }

    pub fn alphas(set: BTreeSet<bool>) -> Self {
        if set.len() == 2 {
            Self::Top
        } else if set.contains(&true) {
            Self::True
        } else if set.contains(&false) {
            Self::False
        } else {
            Self::Bot
        }
    }

    fn join(self, other: Self) -> Self {
        match (self, other) {
            (Self::True, Self::True) => Self::True,
            (Self::False, Self::False) => Self::False,
            (Self::Bot, v) | (v, Self::Bot) => v,
            _ => Self::Top,
        }
    }

    fn widen(self, other: Self) -> Self {
        self.join(other)
    }

    fn ord(self, other: Self) -> bool {
        matches!(
            (self, other),
            (_, Self::Top) | (Self::Bot, _) | (Self::True, Self::True) | (Self::False, Self::False)
        )
    }

    fn not(self) -> Self {
        match self {
            Self::Top => Self::Top,
            Self::True => Self::False,
            Self::False => Self::True,
            Self::Bot => Self::Bot,
        }
    }

    fn to_int(self) -> AbsInt {
        match self {
            Self::Top => AbsInt::alphas((0..=1).collect()),
            Self::True => AbsInt::alpha(1),
            Self::False => AbsInt::alpha(0),
            Self::Bot => AbsInt::bot(),
        }
    }

    fn to_uint(self) -> AbsUint {
        match self {
            Self::Top => AbsUint::alphas((0..=1).collect()),
            Self::True => AbsUint::alpha(1),
            Self::False => AbsUint::alpha(0),
            Self::Bot => AbsUint::bot(),
        }
    }

    fn eq(self, other: Self) -> AbsBool {
        match (self, other) {
            (Self::Bot, _) | (_, Self::Bot) => Self::Bot,
            (Self::True, Self::True) | (Self::False, Self::False) => Self::True,
            (Self::True, Self::False) | (Self::False, Self::True) => Self::False,
            _ => Self::Top,
        }
    }

    fn ne(self, other: Self) -> AbsBool {
        match (self, other) {
            (Self::Bot, _) | (_, Self::Bot) => Self::Bot,
            (Self::True, Self::True) | (Self::False, Self::False) => Self::False,
            (Self::True, Self::False) | (Self::False, Self::True) => Self::True,
            _ => Self::Top,
        }
    }

    fn bit_xor(self, other: Self) -> Self {
        match (self, other) {
            (Self::Bot, _) | (_, Self::Bot) => Self::Bot,
            (Self::True, Self::True) | (Self::False, Self::False) => Self::False,
            (Self::True, Self::False) | (Self::False, Self::True) => Self::True,
            _ => Self::Top,
        }
    }

    fn bit_and(self, other: Self) -> Self {
        match (self, other) {
            (Self::Bot, _) | (_, Self::Bot) => Self::Bot,
            (Self::False, _) | (_, Self::False) => Self::False,
            (Self::True, Self::True) => Self::True,
            _ => Self::Top,
        }
    }

    fn bit_or(self, other: Self) -> Self {
        match (self, other) {
            (Self::Bot, _) | (_, Self::Bot) => Self::Bot,
            (Self::True, _) | (_, Self::True) => Self::True,
            (Self::False, Self::False) => Self::False,
            _ => Self::Top,
        }
    }
}

#[derive(Clone)]
pub enum AbsList {
    Top,
    List(Vec<AbsValue>),
    Bot,
}

impl std::fmt::Debug for AbsList {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Top => write!(f, "⊤_l"),
            Self::List(l) => {
                write!(f, "[")?;
                for (i, v) in l.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{:?}", v)?;
                }
                write!(f, "]")
            }
            Self::Bot => write!(f, "⊥_l"),
        }
    }
}

impl AbsList {
    #[inline]
    fn top() -> Self {
        Self::Top
    }

    #[inline]
    fn bot() -> Self {
        Self::Bot
    }

    #[inline]
    pub fn is_top(&self) -> bool {
        matches!(self, Self::Top)
    }

    #[inline]
    pub fn is_bot(&self) -> bool {
        matches!(self, Self::Bot)
    }

    fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Bot, v) | (v, Self::Bot) => v.clone(),
            (Self::List(l1), Self::List(l2)) if l1.len() == l2.len() => Self::List(
                l1.iter()
                    .zip(l2.iter())
                    .map(|(v1, v2)| v1.join(v2))
                    .collect(),
            ),
            _ => Self::Top,
        }
    }

    fn widen(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Bot, v) | (v, Self::Bot) => v.clone(),
            (Self::List(l1), Self::List(l2)) if l1.len() == l2.len() => Self::List(
                l1.iter()
                    .zip(l2.iter())
                    .map(|(v1, v2)| v1.widen(v2))
                    .collect(),
            ),
            _ => Self::Top,
        }
    }

    fn ord(&self, other: &Self) -> bool {
        match (self, other) {
            (_, Self::Top) | (Self::Bot, _) => true,
            (Self::List(l1), Self::List(l2)) if l1.len() == l2.len() => {
                l1.iter().zip(l2.iter()).all(|(v1, v2)| v1.ord(v2))
            }
            _ => false,
        }
    }

    pub fn get_mut(&mut self, i: usize) -> Option<&mut AbsValue> {
        if let Self::List(l) = self {
            l.get_mut(i)
        } else {
            None
        }
    }

    fn subst(&self, map: &BTreeMap<ArgIdx, AbsPtr>) -> Self {
        match self {
            Self::Top => Self::Top,
            Self::List(l) => Self::List(l.iter().map(|v| v.subst(map)).collect()),
            Self::Bot => Self::Bot,
        }
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct AbsPlace {
    pub base: AbsBase,
    pub projections: Vec<AbsProjElem>,
}

impl std::fmt::Debug for AbsPlace {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.base)?;
        for elem in &self.projections {
            write!(f, "{:?}", elem)?;
        }
        Ok(())
    }
}

impl AbsPlace {
    #[inline]
    fn heap() -> Self {
        Self {
            base: AbsBase::Heap,
            projections: Vec::new(),
        }
    }

    #[inline]
    fn null() -> Self {
        Self {
            base: AbsBase::Null,
            projections: Vec::new(),
        }
    }

    fn arg(i: ArgIdx) -> Self {
        Self {
            base: AbsBase::Arg(i),
            projections: Vec::new(),
        }
    }

    #[inline]
    pub fn is_null(&self) -> bool {
        self.base == AbsBase::Null
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum AbsBase {
    Local(Local),
    Arg(ArgIdx),
    Heap,
    Null,
}

impl std::fmt::Debug for AbsBase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Local(i) => write!(f, "_{}", i.index()),
            Self::Arg(i) => write!(f, "A{}", i.index()),
            Self::Heap => write!(f, "H"),
            Self::Null => write!(f, "null"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum AbsProjElem {
    Field(FieldIdx),
    Index(AbsUint),
}

impl std::fmt::Debug for AbsProjElem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Field(i) => write!(f, ".{}", i.index()),
            Self::Index(i) => write!(f, "[{:?}]", i),
        }
    }
}

#[derive(Clone)]
pub enum AbsPtr {
    Top,
    Set(BTreeSet<AbsPlace>),
}

impl std::fmt::Debug for AbsPtr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Top => write!(f, "⊤_p"),
            Self::Set(s) => match s.len() {
                0 => write!(f, "⊥_p"),
                1 => write!(f, "{:?}", s.first().unwrap()),
                _ => {
                    write!(f, "{{")?;
                    for (i, ptr) in s.iter().enumerate() {
                        if i != 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{:?}", ptr)?;
                    }
                    write!(f, "}}")
                }
            },
        }
    }
}

impl AbsPtr {
    #[inline]
    pub fn top() -> Self {
        Self::Top
    }

    #[inline]
    fn bot() -> Self {
        Self::Set(BTreeSet::new())
    }

    #[inline]
    pub fn is_top(&self) -> bool {
        matches!(self, Self::Top)
    }

    #[inline]
    pub fn is_bot(&self) -> bool {
        if let Self::Set(s) = self {
            s.is_empty()
        } else {
            false
        }
    }

    fn alpha(n: AbsPlace) -> Self {
        Self::alphas([n].into_iter().collect())
    }

    pub fn alphas(set: BTreeSet<AbsPlace>) -> Self {
        if set.len() > MAX_SIZE {
            Self::Top
        } else {
            Self::Set(set)
        }
    }

    pub fn gamma(&self) -> Option<&BTreeSet<AbsPlace>> {
        if let Self::Set(s) = self {
            Some(s)
        } else {
            None
        }
    }

    fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Top, _) | (_, Self::Top) => Self::Top,
            (Self::Set(s1), Self::Set(s2)) => Self::alphas(s1.union(s2).cloned().collect()),
        }
    }

    fn widen(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Top, _) | (_, Self::Top) => Self::Top,
            (Self::Set(s1), Self::Set(s2)) => {
                if s2.is_subset(s1) {
                    self.clone()
                } else if s1.is_empty() {
                    other.clone()
                } else {
                    Self::Top
                }
            }
        }
    }

    fn ord(&self, other: &Self) -> bool {
        match (self, other) {
            (_, Self::Top) => true,
            (Self::Top, _) => false,
            (Self::Set(s1), Self::Set(s2)) => s1.is_subset(s2),
        }
    }

    fn compare(&self, other: &Self) -> AbsBool {
        match (self, other) {
            (Self::Set(s), _) | (_, Self::Set(s)) if s.is_empty() => AbsBool::Bot,
            _ => AbsBool::Top,
        }
    }

    #[inline]
    fn heap() -> Self {
        Self::alpha(AbsPlace::heap())
    }

    #[inline]
    fn null() -> Self {
        Self::alpha(AbsPlace::null())
    }

    #[inline]
    fn heap_or_null() -> Self {
        Self::alphas([AbsPlace::heap(), AbsPlace::null()].into_iter().collect())
    }

    #[inline]
    pub fn arg(i: ArgIdx) -> Self {
        Self::alpha(AbsPlace::arg(i))
    }

    #[inline]
    pub fn is_null(&self) -> bool {
        let Self::Set(ptrs) = self else { return false };
        if ptrs.len() != 1 {
            return false;
        }
        matches!(ptrs.first().unwrap().base, AbsBase::Null)
    }

    pub fn get_arg(&self) -> Option<ArgIdx> {
        if let Self::Set(ptrs) = self {
            if ptrs.len() == 1 {
                if let AbsBase::Arg(i) = &ptrs.first().unwrap().base {
                    return Some(*i);
                }
            }
        }
        None
    }

    fn subst(&self, map: &BTreeMap<ArgIdx, Self>) -> Self {
        if let Self::Set(ptrs) = self {
            ptrs.iter()
                .map(|place| {
                    let alloc = match &place.base {
                        AbsBase::Local(_) => return Self::bot(),
                        AbsBase::Arg(i) => i,
                        AbsBase::Heap => return Self::heap(),
                        AbsBase::Null => return Self::null(),
                    };
                    let ptrs = if let AbsPtr::Set(ptrs) = &map[alloc] {
                        ptrs
                    } else {
                        return AbsPtr::Top;
                    };
                    Self::Set(
                        ptrs.iter()
                            .cloned()
                            .map(|mut new_place| {
                                new_place.projections.extend(place.projections.clone());
                                new_place
                            })
                            .collect(),
                    )
                })
                .reduce(|ptr1, ptr2| ptr1.join(&ptr2))
                .unwrap_or(AbsPtr::bot())
        } else {
            AbsPtr::Top
        }
    }
}

#[derive(Clone)]
pub enum AbsOption {
    Top,
    Some(AbsValue),
    None,
    Bot,
}

impl std::fmt::Debug for AbsOption {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Top => write!(f, "⊤_o"),
            Self::Some(v) => write!(f, "Some({:?})", v),
            Self::None => write!(f, "None"),
            Self::Bot => write!(f, "⊥_o"),
        }
    }
}

impl AbsOption {
    #[inline]
    fn top() -> Self {
        Self::Top
    }

    #[inline]
    fn bot() -> Self {
        Self::Bot
    }

    #[inline]
    pub fn is_top(&self) -> bool {
        matches!(self, Self::Top)
    }

    #[inline]
    pub fn is_bot(&self) -> bool {
        matches!(self, Self::Bot)
    }

    fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Bot, v) | (v, Self::Bot) => v.clone(),
            (Self::None, Self::None) => Self::None,
            (Self::Some(v1), Self::Some(v2)) => Self::Some(v1.join(v2)),
            _ => Self::Top,
        }
    }

    fn widen(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Bot, v) | (v, Self::Bot) => v.clone(),
            (Self::None, Self::None) => Self::None,
            (Self::Some(v1), Self::Some(v2)) => Self::Some(v1.widen(v2)),
            _ => Self::Top,
        }
    }

    fn ord(&self, other: &Self) -> bool {
        match (self, other) {
            (_, Self::Top) | (Self::Bot, _) | (Self::None, Self::None) => true,
            (Self::Some(v1), Self::Some(v2)) => v1.ord(v2),
            _ => false,
        }
    }

    #[inline]
    pub fn is_none(&self) -> bool {
        matches!(self, Self::None)
    }
}

#[derive(Clone)]
pub enum AbsFn {
    Top,
    Set(FxHashSet<DefId>),
}

impl std::fmt::Debug for AbsFn {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Top => write!(f, "⊤_fn"),
            Self::Set(s) => match s.len() {
                0 => write!(f, "⊥_fn"),
                1 => write!(f, "{:?}", s.iter().next().unwrap()),
                _ => {
                    write!(f, "{{")?;
                    for (i, n) in s.iter().enumerate() {
                        if i != 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{:?}", n)?;
                    }
                    write!(f, "}}")
                }
            },
        }
    }
}

impl AbsFn {
    #[inline]
    fn top() -> Self {
        Self::Top
    }

    #[inline]
    fn bot() -> Self {
        Self::Set(FxHashSet::default())
    }

    #[inline]
    pub fn is_top(&self) -> bool {
        matches!(self, Self::Top)
    }

    #[inline]
    pub fn is_bot(&self) -> bool {
        if let Self::Set(s) = self {
            s.is_empty()
        } else {
            false
        }
    }

    fn alpha(n: DefId) -> Self {
        Self::alphas([n].into_iter().collect())
    }

    fn alphas(set: FxHashSet<DefId>) -> Self {
        if set.len() > MAX_SIZE {
            Self::Top
        } else {
            Self::Set(set)
        }
    }

    pub fn gamma(&self) -> Option<&FxHashSet<DefId>> {
        if let Self::Set(s) = self {
            Some(s)
        } else {
            None
        }
    }

    fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Top, _) | (_, Self::Top) => Self::Top,
            (Self::Set(s1), Self::Set(s2)) => Self::alphas(s1.union(s2).cloned().collect()),
        }
    }

    fn widen(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Top, _) | (_, Self::Top) => Self::Top,
            (Self::Set(s1), Self::Set(s2)) => {
                if s2.is_subset(s1) {
                    self.clone()
                } else if s1.is_empty() {
                    other.clone()
                } else {
                    Self::Top
                }
            }
        }
    }

    fn ord(&self, other: &Self) -> bool {
        match (self, other) {
            (_, Self::Top) => true,
            (Self::Top, _) => false,
            (Self::Set(s1), Self::Set(s2)) => s1.is_subset(s2),
        }
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct AbsPath {
    pub base: Local,
    pub projections: Vec<FieldIdx>,
}

impl std::fmt::Debug for AbsPath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.base.index())?;
        for idx in self.projections.iter() {
            write!(f, ".{}", idx.index())?;
        }
        Ok(())
    }
}

impl AbsPath {
    pub fn new(base: Local, projections: Vec<FieldIdx>) -> Self {
        Self { base, projections }
    }

    pub fn from_place(
        place: &AbsPlace,
        ptr_params: &IndexVec<ArgIdx, Local>,
    ) -> Option<(Self, bool)> {
        let arg = if let AbsBase::Arg(arg) = place.base {
            arg
        } else {
            return None;
        };
        let param = ptr_params[arg];
        let mut projections = vec![];
        let mut array_access = false;
        for proj in place.projections.iter() {
            match proj {
                AbsProjElem::Field(idx) => projections.push(*idx),
                AbsProjElem::Index(_) => {
                    array_access = true;
                    break;
                }
            }
        }
        Some((Self::new(param, projections), array_access))
    }

    pub fn as_vec(&self) -> Vec<usize> {
        let mut v = vec![self.base.index()];
        v.extend(self.projections.iter().map(|idx| idx.index()));
        v
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum MustPathSet {
    All,
    Set(BTreeSet<AbsPath>),
}

impl std::fmt::Debug for MustPathSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MustPathSet::All => write!(f, "All"),
            MustPathSet::Set(s) => write!(f, "{:?}", s),
        }
    }
}

impl MustPathSet {
    #[inline]
    pub fn top() -> Self {
        Self::Set(BTreeSet::new())
    }

    #[inline]
    fn bot() -> Self {
        Self::All
    }

    #[inline]
    pub fn is_bot(&self) -> bool {
        matches!(self, Self::All)
    }

    pub fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (s, Self::All) | (Self::All, s) => s.clone(),
            (Self::Set(s1), Self::Set(s2)) => Self::Set(s1.intersection(s2).cloned().collect()),
        }
    }

    fn widen(&self, other: &Self) -> Self {
        self.join(other)
    }

    fn ord(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::All, _) => true,
            (_, Self::All) => false,
            (Self::Set(s1), Self::Set(s2)) => s2.is_subset(s1),
        }
    }

    #[inline]
    pub fn insert(&mut self, place: AbsPath) {
        if let Self::Set(set) = self {
            set.insert(place);
        }
    }

    #[inline]
    pub fn remove(&mut self, base: &BTreeSet<Local>) {
        if let Self::Set(set) = self {
            set.retain(|p| !base.contains(&p.base));
        }
    }

    #[inline]
    pub fn contains(&self, place: &AbsPath) -> bool {
        match self {
            Self::All => true,
            Self::Set(set) => set.contains(place),
        }
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        match self {
            Self::All => false,
            Self::Set(set) => set.is_empty(),
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        match self {
            Self::All => panic!(),
            Self::Set(set) => set.len(),
        }
    }

    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = &AbsPath> {
        match self {
            Self::All => panic!(),
            Self::Set(set) => set.iter(),
        }
    }

    #[inline]
    pub fn into_inner(self) -> BTreeSet<AbsPath> {
        match self {
            Self::All => panic!(),
            Self::Set(set) => set,
        }
    }

    #[inline]
    pub fn as_set(&self) -> &BTreeSet<AbsPath> {
        match self {
            Self::All => panic!(),
            Self::Set(set) => set,
        }
    }

    #[inline]
    pub fn as_vec(&self) -> Vec<&AbsPath> {
        match self {
            Self::All => panic!(),
            Self::Set(set) => set.iter().collect(),
        }
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct MayPathSet(BTreeSet<AbsPath>);

impl std::fmt::Debug for MayPathSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

impl MayPathSet {
    #[inline]
    fn bot() -> Self {
        Self(BTreeSet::new())
    }

    fn join(&self, other: &Self) -> Self {
        Self(self.0.union(&other.0).cloned().collect())
    }

    #[inline]
    fn widen(&self, other: &Self) -> Self {
        self.join(other)
    }

    #[inline]
    fn ord(&self, other: &Self) -> bool {
        self.0.is_subset(&other.0)
    }

    #[inline]
    pub fn insert(&mut self, place: AbsPath) {
        self.0.insert(place);
    }

    #[inline]
    pub fn remove(&mut self, base: &BTreeSet<Local>) {
        self.0.retain(|p| !base.contains(&p.base));
    }

    #[inline]
    pub fn contains(&self, place: &AbsPath) -> bool {
        self.0.contains(place)
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = &AbsPath> {
        self.0.iter()
    }

    #[inline]
    pub fn into_inner(self) -> BTreeSet<AbsPath> {
        self.0
    }

    #[inline]
    pub fn as_set(&self) -> &BTreeSet<AbsPath> {
        &self.0
    }

    #[inline]
    pub fn as_vec(&self) -> Vec<&AbsPath> {
        self.0.iter().collect()
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum AbsNull {
    Top,
    Null,
    Nonnull,
}

impl std::fmt::Debug for AbsNull {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Top => write!(f, "⊤"),
            Self::Null => write!(f, "null"),
            Self::Nonnull => write!(f, "nonnull"),
        }
    }
}

impl AbsNull {
    fn top() -> Self {
        Self::Top
    }

    pub fn null() -> Self {
        Self::Null
    }

    pub fn nonnull() -> Self {
        Self::Nonnull
    }

    fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Null, Self::Null) => Self::Null,
            (Self::Nonnull, Self::Nonnull) => Self::Nonnull,
            _ => Self::Top,
        }
    }

    fn ord(&self, other: &Self) -> bool {
        matches!(
            (self, other),
            (_, Self::Top) | (Self::Null, Self::Null) | (Self::Nonnull, Self::Nonnull)
        )
    }

    fn widen(&self, other: &Self) -> Self {
        self.join(other)
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct AbsNulls(IndexVec<ArgIdx, AbsNull>);

impl PartialOrd for AbsNulls {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AbsNulls {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.raw.cmp(&other.0.raw)
    }
}

impl std::fmt::Debug for AbsNulls {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

impl AbsNulls {
    #[inline]
    pub fn bot() -> Self {
        Self(IndexVec::new())
    }

    pub fn join(&self, other: &Self) -> Self {
        let indices = if self.0.len() > other.0.len() {
            self.0.indices()
        } else {
            other.0.indices()
        };
        Self(
            indices
                .map(|i| match (self.0.get(i), other.0.get(i)) {
                    (Some(n1), Some(n2)) => n1.join(n2),
                    (Some(n), None) | (None, Some(n)) => *n,
                    (None, None) => unreachable!(),
                })
                .collect(),
        )
    }

    pub fn widen(&self, other: &Self) -> Self {
        let indices = if self.0.len() > other.0.len() {
            self.0.indices()
        } else {
            other.0.indices()
        };
        Self(
            indices
                .map(|i| match (self.0.get(i), other.0.get(i)) {
                    (Some(n1), Some(n2)) => n1.widen(n2),
                    (Some(n), None) | (None, Some(n)) => *n,
                    (None, None) => unreachable!(),
                })
                .collect(),
        )
    }

    pub fn ord(&self, other: &Self) -> bool {
        self.0.len() <= other.0.len()
            && self.0.iter().zip(other.0.iter()).all(|(n1, n2)| n1.ord(n2))
    }

    pub fn push_top(&mut self) {
        self.0.push(AbsNull::top());
    }

    pub fn get(&self, arg: ArgIdx) -> &AbsNull {
        &self.0[arg]
    }

    pub fn set(&mut self, arg: ArgIdx, n: AbsNull) {
        while self.0.next_index() < arg {
            self.0.push(AbsNull::top());
        }
        if self.0.next_index() == arg {
            self.0.push(n);
        } else {
            self.0[arg] = n;
        }
    }

    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn next_index(&self) -> ArgIdx {
        self.0.next_index()
    }

    pub fn iter(&self) -> impl Iterator<Item = &AbsNull> {
        self.0.iter()
    }

    pub fn iter_enumerated(&self) -> impl Iterator<Item = (ArgIdx, &AbsNull)> {
        self.0.iter_enumerated()
    }

    pub fn is_null(&self, arg: ArgIdx) -> bool {
        if let Some(n) = self.0.get(arg) {
            matches!(n, AbsNull::Null)
        } else {
            false
        }
    }

    pub fn is_nonnull(&self, arg: ArgIdx) -> bool {
        if let Some(n) = self.0.get(arg) {
            matches!(n, AbsNull::Nonnull)
        } else {
            false
        }
    }

    pub fn is_top(&self, arg: ArgIdx) -> bool {
        if let Some(n) = self.0.get(arg) {
            matches!(n, AbsNull::Top)
        } else {
            false
        }
    }
}

#[derive(Clone)]
pub enum MustLocalSet {
    All,
    Set(BTreeSet<Local>),
}

impl std::fmt::Debug for MustLocalSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MustLocalSet::All => write!(f, "All"),
            MustLocalSet::Set(s) => write!(f, "{:?}", s),
        }
    }
}

impl MustLocalSet {
    #[inline]
    pub fn top() -> Self {
        Self::Set(BTreeSet::new())
    }

    #[inline]
    fn bot() -> Self {
        Self::All
    }

    #[inline]
    pub fn is_bot(&self) -> bool {
        matches!(self, Self::All)
    }

    pub fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (s, Self::All) | (Self::All, s) => s.clone(),
            (Self::Set(s1), Self::Set(s2)) => Self::Set(s1.intersection(s2).cloned().collect()),
        }
    }

    fn widen(&self, other: &Self) -> Self {
        self.join(other)
    }

    fn ord(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::All, _) => true,
            (_, Self::All) => false,
            (Self::Set(s1), Self::Set(s2)) => s2.is_subset(s1),
        }
    }

    #[inline]
    pub fn insert(&mut self, l: Local) {
        if let Self::Set(set) = self {
            set.insert(l);
        }
    }

    #[inline]
    pub fn extend(&mut self, locals: impl IntoIterator<Item = Local>) {
        if let Self::Set(set) = self {
            set.extend(locals);
        }
    }

    #[inline]
    pub fn contains(&self, l: Local) -> bool {
        match self {
            Self::All => true,
            Self::Set(set) => set.contains(&l),
        }
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        match self {
            Self::All => false,
            Self::Set(set) => set.is_empty(),
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        match self {
            Self::All => panic!(),
            Self::Set(set) => set.len(),
        }
    }

    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = &Local> {
        match self {
            Self::All => panic!(),
            Self::Set(set) => set.iter(),
        }
    }

    #[inline]
    pub fn into_inner(self) -> BTreeSet<Local> {
        match self {
            Self::All => panic!(),
            Self::Set(set) => set,
        }
    }
}
