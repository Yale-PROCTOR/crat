//! Syntactic access observations. Equal field declarations do not equate cells.

use rustc_middle::{
    mir::{AggregateKind, CastKind, Operand, Place, Rvalue},
    ty::TyCtxt,
};

use super::export::{PlaceKey, ProjKey};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub(crate) struct PlaceSyntax {
    pub(crate) local: u32,
    pub(crate) projection: Vec<ProjKey>,
}
impl From<Place<'_>> for PlaceSyntax {
    fn from(place: Place<'_>) -> Self {
        let key = PlaceKey::from_place(place);
        Self {
            local: key.local.as_u32(),
            projection: key.proj,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub(crate) enum OperandSyntax {
    Copy {
        place: PlaceSyntax,
    },
    Move {
        place: PlaceSyntax,
    },
    /// Zero is numeric evidence; pointer context decides whether it is None.
    Constant {
        description: String,
        zero: bool,
    },
}

fn operand<'tcx>(value: &Operand<'tcx>, tcx: TyCtxt<'tcx>) -> OperandSyntax {
    match value {
        Operand::Copy(place) => OperandSyntax::Copy {
            place: (*place).into(),
        },
        Operand::Move(place) => OperandSyntax::Move {
            place: (*place).into(),
        },
        Operand::Constant(_) => OperandSyntax::Constant {
            description: format!("{value:?}"),
            zero: super::source_events::operand_is_null(value, &[], tcx),
        },
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub(crate) enum Expression {
    Value {
        operand: OperandSyntax,
    },
    Cast {
        cast: String,
        operand: OperandSyntax,
        target_type: String,
    },
    Borrow {
        borrow: String,
        place: PlaceSyntax,
    },
    RawAddress {
        mutability: String,
        place: PlaceSyntax,
    },
    CopyForDeref {
        place: PlaceSyntax,
    },
    Aggregate {
        structure: Option<String>,
        description: String,
        operands: Vec<OperandSyntax>,
    },
    Call {
        operands: Vec<OperandSyntax>,
    },
    Unrepresented {
        description: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub(crate) struct Syntax {
    pub(crate) destination: PlaceSyntax,
    pub(crate) expression: Expression,
    pub(crate) immediate_origin: ImmediateOrigin,
}

/// Immediate evidence only. Transport must close all incoming alternatives.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum ImmediateOrigin {
    Borrow,
    Null,
    Transfer,
    Aggregate,
    CallNeedsSummary,
    Unknown,
}

pub(crate) fn assignment<'tcx>(
    destination: Place<'tcx>,
    value: &Rvalue<'tcx>,
    tcx: TyCtxt<'tcx>,
    pointer_result: bool,
) -> Syntax {
    let null_literal = pointer_result
        && match value {
            Rvalue::Use(value @ Operand::Constant(_))
            | Rvalue::Cast(_, value @ Operand::Constant(_), _) => {
                super::source_events::operand_is_null(value, &[], tcx)
            }
            _ => false,
        };
    let immediate_origin = if null_literal {
        ImmediateOrigin::Null
    } else {
        match value {
            Rvalue::Ref(..) | Rvalue::RawPtr(..) => ImmediateOrigin::Borrow,
            Rvalue::Use(Operand::Copy(_) | Operand::Move(_))
            | Rvalue::CopyForDeref(_)
            | Rvalue::Cast(CastKind::PtrToPtr, Operand::Copy(_) | Operand::Move(_), _) => {
                ImmediateOrigin::Transfer
            }
            Rvalue::Aggregate(..) => ImmediateOrigin::Aggregate,
            _ => ImmediateOrigin::Unknown,
        }
    };
    let expression = match value {
        Rvalue::Use(value) => Expression::Value {
            operand: operand(value, tcx),
        },
        Rvalue::Cast(kind, value, ty) => Expression::Cast {
            cast: format!("{kind:?}"),
            operand: operand(value, tcx),
            target_type: format!("{ty:?}"),
        },
        Rvalue::Ref(_, kind, place) => Expression::Borrow {
            borrow: format!("{kind:?}"),
            place: (*place).into(),
        },
        Rvalue::RawPtr(kind, place) => Expression::RawAddress {
            mutability: format!("{kind:?}"),
            place: (*place).into(),
        },
        Rvalue::CopyForDeref(place) => Expression::CopyForDeref {
            place: (*place).into(),
        },
        Rvalue::Aggregate(kind, values) => Expression::Aggregate {
            structure: match kind.as_ref() {
                AggregateKind::Adt(did, _, _, _, _) if tcx.adt_def(*did).is_struct() => {
                    Some(tcx.def_path_str(*did))
                }
                _ => None,
            },
            description: format!("{kind:?}"),
            operands: values.iter().map(|v| operand(v, tcx)).collect(),
        },
        other => Expression::Unrepresented {
            description: format!("{other:?}"),
        },
    };
    Syntax {
        destination: destination.into(),
        expression,
        immediate_origin,
    }
}

pub(crate) fn call<'a, 'tcx: 'a>(
    destination: Place<'tcx>,
    args: impl Iterator<Item = &'a Operand<'tcx>>,
    tcx: TyCtxt<'tcx>,
) -> Syntax {
    Syntax {
        destination: destination.into(),
        expression: Expression::Call {
            operands: args.map(|a| operand(a, tcx)).collect(),
        },
        immediate_origin: ImmediateOrigin::CallNeedsSummary,
    }
}
