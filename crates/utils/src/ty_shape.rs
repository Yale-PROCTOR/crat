use rustc_abi::FieldIdx;
use rustc_hash::FxHashMap;
use rustc_hir::{
    BodyId, ExprKind, FnRetTy, ImplItemKind, ImplItemRef, ItemKind, QPath, StmtKind,
    TyKind as HirTyKind,
};
use rustc_middle::{
    mir::{
        Body, Location, Operand, Place, PlaceElem,
        visit::{PlaceContext, Visitor},
    },
    ty::{Ty, TyCtxt, TyKind, TypingEnv},
};
use rustc_span::def_id::{DefId, LocalDefId};
use typed_arena::Arena;

pub struct TyShapes<'a, 'tcx> {
    pub bitfields: FxHashMap<LocalDefId, BitField>,
    pub tys: FxHashMap<Ty<'tcx>, &'a TyShape<'a, 'tcx>>,
    arena: &'a Arena<TyShape<'a, 'tcx>>,
}

impl std::fmt::Debug for TyShapes<'_, '_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TyShapes")
            .field("bitfields", &self.bitfields)
            .field("tys", &self.tys)
            .finish()
    }
}

#[derive(Debug)]
pub struct BitField {
    /// field name to field index
    pub name_to_idx: FxHashMap<String, FieldIdx>,
    /// field index to field name and type
    pub fields: FxHashMap<FieldIdx, (String, String)>,
}

impl BitField {
    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        self.fields.len()
    }
}

pub fn get_ty_shapes<'a, 'tcx>(
    arena: &'a Arena<TyShape<'a, 'tcx>>,
    tcx: TyCtxt<'tcx>,
    use_optimized_mir: bool,
) -> TyShapes<'a, 'tcx> {
    let mut tss = TyShapes {
        bitfields: FxHashMap::default(),
        tys: FxHashMap::default(),
        arena,
    };
    compute_bitfields(&mut tss, tcx);
    compute_ty_shapes(&mut tss, tcx, use_optimized_mir);
    tss
}

fn compute_bitfields<'tcx>(tss: &mut TyShapes<'_, 'tcx>, tcx: TyCtxt<'tcx>) {
    for item_id in tcx.hir_free_items() {
        let item = tcx.hir_item(item_id);
        let ItemKind::Impl(imp) = item.kind else { continue };
        if imp.of_trait.is_some()
            || imp.items.is_empty()
            || !tcx.is_automatically_derived(item.owner_id.to_def_id())
        {
            continue;
        }
        let self_ty = tcx.type_of(item.owner_id.def_id).instantiate_identity();
        let TyKind::Adt(adt, _) = self_ty.kind() else { continue };
        let Some(struct_id) = adt.did().as_local() else { continue };
        if !adt.is_struct() {
            continue;
        }

        let first_index = adt.non_enum_variant().fields.len();
        // BitfieldStruct emits a setter and getter for each bitfield in declaration order.
        let Some(fields) = imp
            .items
            .chunks(2)
            .map(|pair| bitfield_accessor_pair(pair, tcx))
            .collect::<Option<Vec<_>>>()
        else {
            continue;
        };

        tss.bitfields.insert(
            struct_id,
            BitField {
                name_to_idx: fields
                    .iter()
                    .enumerate()
                    .map(|(i, (name, _))| (name.clone(), FieldIdx::from_usize(first_index + i)))
                    .collect(),
                fields: fields
                    .into_iter()
                    .enumerate()
                    .map(|(i, field)| (FieldIdx::from_usize(first_index + i), field))
                    .collect(),
            },
        );
    }
}

fn bitfield_accessor_pair<'tcx>(
    pair: &[ImplItemRef],
    tcx: TyCtxt<'tcx>,
) -> Option<(String, String)> {
    let [setter, getter] = pair else { return None };
    let name = getter.ident.name.to_ident_string();
    if setter.ident.name.as_str().strip_prefix("set_") != Some(name.as_str()) {
        return None;
    }
    let ImplItemKind::Fn(_, setter_body) = tcx.hir_impl_item(setter.id).kind else { return None };
    let ImplItemKind::Fn(signature, getter_body) = tcx.hir_impl_item(getter.id).kind else {
        return None;
    };
    let FnRetTy::Return(ty) = signature.decl.output else { return None };
    let HirTyKind::Path(QPath::Resolved(_, path)) = ty.kind else { return None };
    if !calls_bitfield_helper(setter_body, "set_field", tcx)
        || !calls_bitfield_helper(getter_body, "get_field", tcx)
    {
        return None;
    }
    let ty = path
        .segments
        .iter()
        .map(|segment| segment.ident.name.to_ident_string())
        .intersperse("::".to_string())
        .collect();
    Some((name, ty))
}

fn calls_bitfield_helper<'tcx>(body: BodyId, helper: &str, tcx: TyCtxt<'tcx>) -> bool {
    let body = tcx.hir_body(body);
    let ExprKind::Block(block, _) = body.value.kind else { return false };
    let Some(call) = block.expr.or_else(|| match block.stmts.last()?.kind {
        StmtKind::Semi(call) => Some(call),
        _ => None,
    }) else {
        return false;
    };
    let typeck = tcx.typeck(body.value.hir_id.owner);
    let callee = match call.kind {
        ExprKind::Call(callee, _) => match typeck.expr_ty(callee).kind() {
            TyKind::FnDef(def_id, _) => Some(*def_id),
            _ => None,
        },
        ExprKind::MethodCall(..) => typeck.type_dependent_def_id(call.hir_id),
        _ => None,
    };
    callee.is_some_and(|callee| {
        tcx.item_name(callee).as_str() == helper
            && tcx.trait_of_item(callee).is_some_and(|trait_id| {
                !trait_id.is_local()
                    && tcx.crate_name(trait_id.krate).as_str() == "c2rust_bitfields"
                    && tcx.item_name(trait_id).as_str() == "FieldType"
            })
    })
}

fn compute_ty_shapes<'tcx>(
    tss: &mut TyShapes<'_, 'tcx>,
    tcx: TyCtxt<'tcx>,
    use_optimized_mir: bool,
) {
    for item_id in tcx.hir_free_items() {
        let item = tcx.hir_item(item_id);
        let local_def_id = item.owner_id.def_id;
        let def_id = local_def_id.to_def_id();
        let body = match item.kind {
            ItemKind::Fn { ident, .. } if ident.name.as_str() != "main" => {
                if use_optimized_mir {
                    tcx.optimized_mir(local_def_id)
                } else {
                    &tcx.mir_drops_elaborated_and_const_checked(local_def_id)
                        .borrow()
                }
            }
            ItemKind::Static(_, _, _, _) => {
                if use_optimized_mir {
                    tcx.mir_for_ctfe(def_id)
                } else {
                    &tcx.mir_drops_elaborated_and_const_checked(local_def_id)
                        .borrow()
                }
            }
            _ => continue,
        };
        for local_decl in body.local_decls.iter() {
            compute_ty_shape(local_decl.ty, def_id, tss, tcx);
            if let Some(ty) = unwrap_ptr(local_decl.ty) {
                compute_ty_shape(ty, def_id, tss, tcx);
            }
        }
        ShapeCollector {
            tss,
            tcx,
            owner: def_id,
            body,
        }
        .visit_body(body);
    }
}

struct ShapeCollector<'a, 'b, 'tcx> {
    tss: &'b mut TyShapes<'a, 'tcx>,
    tcx: TyCtxt<'tcx>,
    owner: DefId,
    body: &'b Body<'tcx>,
}

impl<'tcx> Visitor<'tcx> for ShapeCollector<'_, '_, 'tcx> {
    fn visit_operand(&mut self, operand: &Operand<'tcx>, location: Location) {
        compute_ty_shape(
            operand.ty(&self.body.local_decls, self.tcx),
            self.owner,
            self.tss,
            self.tcx,
        );
        self.super_operand(operand, location);
    }

    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        compute_ty_shape(
            place.ty(&self.body.local_decls, self.tcx).ty,
            self.owner,
            self.tss,
            self.tcx,
        );
        for element in place.projection {
            if let PlaceElem::Field(_, ty)
            | PlaceElem::Subtype(ty)
            | PlaceElem::OpaqueCast(ty)
            | PlaceElem::UnwrapUnsafeBinder(ty) = element
            {
                compute_ty_shape(ty, self.owner, self.tss, self.tcx);
            }
        }
        self.super_place(place, context, location);
    }
}

fn compute_ty_shape<'a, 'tcx>(
    ty: Ty<'tcx>,
    owner: DefId,
    tss: &mut TyShapes<'a, 'tcx>,
    tcx: TyCtxt<'tcx>,
) -> &'a TyShape<'a, 'tcx> {
    if let Some(ts) = tss.tys.get(&ty) {
        return ts;
    }
    let ts = match ty.kind() {
        TyKind::Adt(adt_def, generic_args) => {
            if ty.is_c_void(tcx) {
                tss.arena.alloc(TyShape::Primitive(ty))
            } else {
                let tys = adt_def.variants().iter().flat_map(|variant| {
                    variant
                        .fields
                        .iter()
                        .map(|field| field.ty(tcx, generic_args))
                });
                let bitfield_len = adt_def
                    .did()
                    .as_local()
                    .and_then(|local_def_id| tss.bitfields.get(&local_def_id))
                    .map(|fields| fields.len())
                    .unwrap_or_default();
                let is_union = adt_def.is_union();
                compute_ty_shape_many(tys, bitfield_len, is_union, owner, tss, tcx)
            }
        }
        TyKind::Array(ty, len) => {
            let t = compute_ty_shape(*ty, owner, tss, tcx);
            match len.try_to_target_usize(tcx) {
                Some(len) => tss.arena.alloc(TyShape::Array(t, len as usize)),
                None => tss.arena.alloc(TyShape::Slice(t)),
            }
        }
        TyKind::Slice(ty) => {
            let t = compute_ty_shape(*ty, owner, tss, tcx);
            tss.arena.alloc(TyShape::Slice(t))
        }
        TyKind::Tuple(tys) => compute_ty_shape_many(tys.iter(), 0, false, owner, tss, tcx),
        TyKind::Closure(_, args) => compute_ty_shape_many(
            args.as_closure().upvar_tys().iter(),
            0,
            false,
            owner,
            tss,
            tcx,
        ),
        TyKind::Alias(..) => {
            match tcx.try_normalize_erasing_regions(TypingEnv::post_analysis(tcx, owner), ty) {
                Ok(revealed) if revealed != ty => compute_ty_shape(revealed, owner, tss, tcx),
                _ => tss.arena.alloc(TyShape::Primitive(ty)),
            }
        }
        _ => tss.arena.alloc(TyShape::Primitive(ty)),
    };
    tss.tys.insert(ty, ts);
    assert_ne!(ts.len(), 0);
    ts
}

#[inline]
fn compute_ty_shape_many<'a, 'tcx, I: Iterator<Item = Ty<'tcx>>>(
    tys: I,
    bitfield_len: usize,
    is_union: bool,
    owner: DefId,
    tss: &mut TyShapes<'a, 'tcx>,
    tcx: TyCtxt<'tcx>,
) -> &'a TyShape<'a, 'tcx> {
    let mut len = 0;
    let mut fields = vec![];
    for ty in tys {
        let ts = compute_ty_shape(ty, owner, tss, tcx);
        fields.push((len, ts));
        len += ts.len();
    }
    for _ in 0..bitfield_len {
        fields.push((len, tss.arena.alloc(TyShape::Primitive(tcx.types.u8))));
        len += 1;
    }
    if len == 0 {
        tss.arena.alloc(TyShape::Primitive(tcx.types.unit))
    } else {
        tss.arena.alloc(TyShape::Struct(len, fields, is_union))
    }
}

#[inline]
pub fn unwrap_ptr(ty: Ty<'_>) -> Option<Ty<'_>> {
    match ty.kind() {
        TyKind::Ref(_, ty, _) | TyKind::RawPtr(ty, ..) => Some(*ty),
        _ => None,
    }
}

#[allow(variant_size_differences)]
pub enum TyShape<'a, 'tcx> {
    Primitive(Ty<'tcx>),
    Array(&'a TyShape<'a, 'tcx>, usize),
    Slice(&'a TyShape<'a, 'tcx>),
    Struct(usize, Vec<(usize, &'a TyShape<'a, 'tcx>)>, bool),
}

impl std::fmt::Debug for TyShape<'_, '_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Primitive(ty) => write!(f, "{ty:?}"),
            Self::Array(t, len) => write!(f, "[{t:?}; {len}]"),
            Self::Slice(t) => write!(f, "[{t:?}]"),
            Self::Struct(len, fields, is_union) => {
                write!(f, "{{{len}")?;
                for (i, ts) in fields {
                    let sep = if *i == 0 { ";" } else { "," };
                    write!(f, "{sep} {i}: {ts:?}")?;
                }
                write!(f, "}}")?;
                if *is_union {
                    write!(f, "u")?;
                }
                Ok(())
            }
        }
    }
}

impl TyShape<'_, '_> {
    #[inline]
    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        match self {
            Self::Primitive(_) => 1,
            Self::Array(t, _) | Self::Slice(t) => t.len(),
            Self::Struct(len, _, _) => *len,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn symbolic_array_lengths_keep_element_shape_without_a_concrete_extent() {
        crate::compilation::run_compiler_on_str(
            "pub fn repeat<T: Copy, const N: usize>(value: T) -> [T; N] { [value; N] }",
            |tcx| {
                let arena = Arena::new();
                let shapes = get_ty_shapes(&arena, tcx, false);
                assert!(shapes.tys.iter().any(|(ty, shape)| {
                    matches!(ty.kind(), TyKind::Array(..))
                        && matches!(shape, TyShape::Slice(element) if element.len() == 1)
                }));
            },
        )
        .unwrap();
    }

    fn flags_type(tcx: TyCtxt<'_>) -> Ty<'_> {
        let flags = tcx
            .hir_free_items()
            .find(|item_id| {
                tcx.hir_item(*item_id)
                    .kind
                    .ident()
                    .is_some_and(|ident| ident.name.as_str() == "Flags")
            })
            .unwrap();
        tcx.type_of(flags.owner_id.def_id).instantiate_identity()
    }

    #[test]
    fn empty_generated_impl_retains_only_physical_fields() {
        crate::compilation::run_compiler_on_str(
            r#"
#[repr(C)]
pub struct Flags {
    pub ready_busy: [u8; 1],
    pub c2rust_padding: [u8; 7],
}
#[automatically_derived]
impl Flags {}
pub fn keep(value: Flags) -> Flags { value }
"#,
            |tcx| {
                let arena = Arena::new();
                let shapes = get_ty_shapes(&arena, tcx, false);
                assert!(shapes.bitfields.is_empty());
                let TyShape::Struct(len, fields, false) = shapes.tys[&flags_type(tcx)] else {
                    panic!("expected physical struct fields");
                };
                assert_eq!(*len, 2);
                assert_eq!(fields.len(), 2);
                assert!(matches!(fields[0].1, TyShape::Array(_, 1)));
                assert!(matches!(fields[1].1, TyShape::Array(_, 7)));
            },
        )
        .unwrap();
    }

    fn assert_bitfields(source: &str, array_lengths: &[usize], expected: &[(&str, &str)]) {
        crate::compilation::run_compiler_on_str(source, |tcx| {
            let arena = Arena::new();
            let shapes = get_ty_shapes(&arena, tcx, false);
            let flags = flags_type(tcx);
            let TyKind::Adt(adt, _) = flags.kind() else { panic!("expected Flags struct") };
            let bitfields = &shapes.bitfields[&adt.did().expect_local()];
            assert_eq!(bitfields.len(), expected.len());
            assert_eq!(bitfields.name_to_idx.len(), expected.len());
            for (ordinal, &(name, ty)) in expected.iter().enumerate() {
                let index = FieldIdx::from_usize(array_lengths.len() + ordinal);
                assert_eq!(bitfields.name_to_idx[name], index);
                assert_eq!(bitfields.fields[&index], (name.to_owned(), ty.to_owned()));
            }

            let TyShape::Struct(len, fields, false) = shapes.tys[&flags] else {
                panic!("expected physical and logical struct fields");
            };
            assert_eq!(*len, array_lengths.len() + expected.len());
            assert_eq!(fields.len(), *len);
            for ((_, shape), &length) in fields.iter().zip(array_lengths) {
                assert!(matches!(shape, TyShape::Array(_, n) if *n == length));
            }
            for (_, shape) in &fields[array_lengths.len()..] {
                assert!(matches!(shape, TyShape::Primitive(ty) if *ty == tcx.types.u8));
            }
        })
        .unwrap();
    }

    #[test]
    fn bitfields_with_an_ordinary_byte_array_retain_logical_fields() {
        assert_bitfields(
            r#"
use c2rust_bitfields::BitfieldStruct;
#[repr(C)]
#[derive(BitfieldStruct)]
pub struct Flags {
    pub checksum: [u8; 32],
    #[bitfield(name = "ready", ty = "u8", bits = "0..=0")]
    #[bitfield(name = "busy", ty = "libc::c_uint", bits = "1..=1")]
    pub ready_busy: [u8; 1],
    #[bitfield(padding)]
    pub c2rust_padding: [u8; 7],
}
pub fn read(value: Flags) -> u8 { value.ready() }
"#,
            &[32, 1, 7],
            &[("ready", "u8"), ("busy", "libc::c_uint")],
        );
    }

    #[test]
    fn renamed_bitfield_storage_retains_logical_fields_in_an_expanded_impl() {
        assert_bitfields(
            r#"
use c2rust_bitfields::FieldType;
#[repr(C)]
pub struct Flags {
    pub flags: [u8; 2],
}
#[automatically_derived]
impl Flags {
    pub fn set_ready(&mut self, value: u8) {
        value.set_field(&mut self.flags, (0, 0));
    }
    pub fn ready(&self) -> u8 {
        <u8 as FieldType>::get_field(&self.flags, (0, 0))
    }
}
pub fn read(value: Flags) -> u8 { value.ready() }
"#,
            &[2],
            &[("ready", "u8")],
        );
    }

    #[test]
    fn similar_generated_methods_without_bitfield_helpers_are_ignored() {
        crate::compilation::run_compiler_on_str(
            r#"
pub struct Flags {
    pub ready: [u8; 1],
}
#[automatically_derived]
impl Flags {
    pub fn set_ready(&mut self, value: u8) { self.ready[0] = value; }
    pub fn ready(&self) -> u8 { self.ready[0] }
}
pub fn read(value: Flags) -> u8 { value.ready() }
"#,
            |tcx| {
                let arena = Arena::new();
                let shapes = get_ty_shapes(&arena, tcx, false);
                assert!(shapes.bitfields.is_empty());
            },
        )
        .unwrap();
    }
}
