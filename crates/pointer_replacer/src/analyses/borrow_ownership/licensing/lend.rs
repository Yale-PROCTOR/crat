//! L01¹⁰, the lend (rule 5): era-5c 066's certificate, R579-2 / R580-1.
//!
//! A raw-pointer formal is LENDABLE when its derivation closure (copies, casts,
//! field and element addresses, deriving library calls, interior-pointer libc
//! results) is never freed, never stored as a value (into memory or an
//! aggregate), never returned, and every call receiving a member is to a
//! lendable local formal, a libc callee on the no-retain table, a deriving or
//! read-only library method, or (R580-1) an indirect callee under R481's tier-2
//! retention waiver, receipted per site. Greatest fixpoint over local callees.
//!
//! A lendable formal takes era 5b's existing Borrowed role at every call (the
//! caller's token passes through, the formal is a zero view): the certificate
//! widens `borrows_parameter`, nothing else. Off by default (`CRAT_ERA5C_LEND`).

use std::collections::{BTreeMap, BTreeSet};

use rustc_middle::mir::{Local, Operand, Rvalue, StatementKind};
use serde::{Deserialize, Serialize};

use crate::{
    analyses::mir::{CallKind, TerminatorExt},
    utils::rustc::RustProgram,
};

/// R580-1: the waiver every indirect-call site of a lent formal carries.
pub(crate) const WAIVER_ID: &str = "retention-waiver:tier-2@2026-09-21";

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Plan {
    /// `(function, formal local)` pairs that lend.
    pub(crate) lendable: BTreeSet<(String, u32)>,
    /// The indirect calls a lendable formal's closure reaches (R580-1).
    pub(crate) waivers: Vec<WaiverSite>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub(crate) struct WaiverSite {
    pub(crate) caller: String,
    pub(crate) formal: u32,
    pub(crate) block: u32,
    pub(crate) statement: usize,
    pub(crate) argument: usize,
}

impl WaiverSite {
    pub(crate) fn receipt(&self) -> String {
        format!(
            "lend-waiver(tier-2, kind=indirect-call, site={}:bb{}[{}]:arg{})",
            self.caller, self.block, self.statement, self.argument
        )
    }
}

impl Plan {
    /// Argument `index` (0-based) of `function` lends.
    pub(crate) fn lends(&self, function: &str, index: usize) -> bool {
        self.lendable
            .contains(&(function.to_owned(), (index + 1) as u32))
    }
}

/// `CRAT_ERA5C_LEND=on|off` (fail-loud, absent = off).
pub(crate) fn lend() -> bool {
    match std::env::var("CRAT_ERA5C_LEND").ok().as_deref() {
        None | Some("off") => false,
        Some("on") => true,
        Some(other) => panic!("CRAT_ERA5C_LEND must be `on` or `off`, got {other:?}"),
    }
}

/// W63's fault hooks (`CRAT_E5C_W63_FAULT`), carried by the identity.
pub(crate) fn fault(name: &str) -> bool {
    std::env::var("CRAT_E5C_W63_FAULT").ok().as_deref() == Some(name)
}

/// W64's fault hooks (`CRAT_E5C_W64_FAULT`), carried by the identity:
/// `full-window` (070's whole-window lend), `interior-zero`,
/// `no-interior-equal`, `drop-plan`.
pub(crate) fn w64_fault(name: &str) -> bool {
    std::env::var("CRAT_E5C_W64_FAULT").ok().as_deref() == Some(name)
}

/// libc callees that neither free nor retain a pointer argument.
const NO_RETAIN: &[&str] = &[
    "strlen",
    "strcmp",
    "strncmp",
    "strcasecmp",
    "strncasecmp",
    "strcpy",
    "strncpy",
    "strcat",
    "strncat",
    "memcpy",
    "memmove",
    "memset",
    "memcmp",
    "printf",
    "fprintf",
    "sprintf",
    "snprintf",
    "vsnprintf",
    "vfprintf",
    "puts",
    "fputs",
    "fputc",
    "putc",
    "fwrite",
    "fread",
    "fgets",
    "fgetc",
    "getc",
    "sscanf",
    "fscanf",
    "atoi",
    "atol",
    "atof",
    "strtol",
    "strtoul",
    "strtod",
    "strtoll",
    "strtoull",
    "fflush",
    "ferror",
    "feof",
    "fseek",
    "ftell",
    "rewind",
    "strspn",
    "strcspn",
    "qsort",
    "bsearch",
];
/// libc callees whose result points into an argument.
const INTERIOR: &[&str] = &["strchr", "strrchr", "strstr", "strpbrk", "memchr"];

/// The certificate over `program`'s local functions.
pub(crate) fn collect(program: &RustProgram<'_>) -> Plan {
    let tcx = program.tcx;
    let name = |f: rustc_span::def_id::LocalDefId| tcx.def_path_str(f.to_def_id());
    let pointer_formals = |f: rustc_span::def_id::LocalDefId| -> Vec<Local> {
        let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
        (1..=body.arg_count)
            .map(Local::from_usize)
            .filter(|&l| body.local_decls[l].ty.is_raw_ptr())
            .collect()
    };
    let waived = !fault("no-waiver");
    let mut consumer: BTreeMap<(String, u32), String> = BTreeMap::new();
    let mut sites: BTreeMap<(String, u32), BTreeSet<WaiverSite>> = BTreeMap::new();
    loop {
        let before = consumer.len();
        for &f in &program.functions {
            let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
            for formal in pointer_formals(f) {
                let key = (name(f), formal.as_u32());
                if consumer.contains_key(&key) {
                    continue;
                }
                let mut closure = BTreeSet::from([formal]);
                let mut reason: Option<String> = None;
                let mut indirect = BTreeSet::new();
                let in_closure = |op: &Operand<'_>, c: &BTreeSet<Local>| {
                    op.place()
                        .is_some_and(|p| p.projection.is_empty() && c.contains(&p.local))
                };
                loop {
                    let size = closure.len();
                    for (block, data) in body.basic_blocks.iter_enumerated() {
                        for statement in &data.statements {
                            let StatementKind::Assign(assign) = &statement.kind else {
                                continue;
                            };
                            let (dest, rvalue) = &**assign;
                            let derived = match rvalue {
                                Rvalue::Use(op) | Rvalue::Cast(_, op, _) => {
                                    in_closure(op, &closure)
                                }
                                Rvalue::RawPtr(_, place) | Rvalue::Ref(_, _, place) => {
                                    place.is_indirect_first_projection()
                                        && closure.contains(&place.local)
                                }
                                _ => false,
                            };
                            if derived {
                                if !dest.projection.is_empty() {
                                    reason.get_or_insert("store".into());
                                } else if dest.local.as_u32() == 0 {
                                    reason.get_or_insert("return".into());
                                } else {
                                    closure.insert(dest.local);
                                }
                            }
                            if let Rvalue::Aggregate(_, ops) = rvalue
                                && ops.iter().any(|op| in_closure(op, &closure))
                            {
                                reason.get_or_insert("aggregate".into());
                            }
                        }
                        let Some(call) = data.terminator().as_call(tcx) else {
                            continue;
                        };
                        let hits: Vec<usize> = call
                            .args
                            .iter()
                            .enumerate()
                            .filter(|(_, a)| in_closure(&a.node, &closure))
                            .map(|(i, _)| i)
                            .collect();
                        if hits.is_empty() {
                            continue;
                        }
                        let mut derives = false;
                        match &call.func {
                            CallKind::FreeStanding(g) | CallKind::Impl(g) => {
                                let gbody = tcx.mir_drops_elaborated_and_const_checked(*g).borrow();
                                for &i in &hits {
                                    let k = (name(*g), (i + 1) as u32);
                                    let pointer = i < gbody.arg_count
                                        && gbody.local_decls[Local::from_usize(i + 1)]
                                            .ty
                                            .is_raw_ptr();
                                    if !pointer {
                                        reason.get_or_insert(format!(
                                            "callee-nonpointer:{}#{}",
                                            k.0, k.1
                                        ));
                                    } else if consumer.contains_key(&k) {
                                        reason.get_or_insert(format!(
                                            "consuming-callee:{}#{}",
                                            k.0, k.1
                                        ));
                                    }
                                }
                            }
                            CallKind::LibC(symbol) => {
                                let s = symbol.as_str();
                                if s == "free" || s == "realloc" {
                                    reason.get_or_insert(format!("frees:{s}"));
                                } else if INTERIOR.contains(&s) {
                                    derives = true;
                                } else if !NO_RETAIN.contains(&s) {
                                    reason.get_or_insert(format!("unknown-libc:{s}"));
                                }
                            }
                            CallKind::RustLib(did) => {
                                let s = tcx.item_name(*did);
                                match s.as_str() {
                                    "offset" | "add" | "sub" | "wrapping_offset"
                                    | "wrapping_add" | "wrapping_sub" | "cast" | "cast_mut"
                                    | "cast_const" | "as_ptr" | "as_mut_ptr" => derives = true,
                                    // read-only, including an `Option` field read in place
                                    "is_null" | "offset_from" | "addr" | "eq" | "ne"
                                    | "is_some" | "is_none" | "expect" | "unwrap" => {}
                                    other => {
                                        reason.get_or_insert(format!("rust-lib:{other}"));
                                    }
                                }
                            }
                            CallKind::Closure | CallKind::Dynamic => {
                                if waived {
                                    for &argument in &hits {
                                        indirect.insert(WaiverSite {
                                            caller: key.0.clone(),
                                            formal: key.1,
                                            block: block.as_u32(),
                                            statement: data.statements.len(),
                                            argument,
                                        });
                                    }
                                } else {
                                    reason.get_or_insert("indirect".into());
                                }
                            }
                        }
                        if derives && call.destination.projection.is_empty() {
                            if call.destination.local.as_u32() == 0 {
                                reason.get_or_insert("return".into());
                            } else {
                                closure.insert(call.destination.local);
                            }
                        }
                    }
                    if closure.len() == size {
                        break;
                    }
                }
                match reason {
                    Some(reason) => {
                        sites.remove(&key);
                        consumer.insert(key, reason);
                    }
                    None => {
                        sites.insert(key, indirect);
                    }
                }
            }
        }
        if consumer.len() == before {
            break;
        }
    }
    let mut plan = Plan::default();
    for &f in &program.functions {
        for formal in pointer_formals(f) {
            let key = (name(f), formal.as_u32());
            if !consumer.contains_key(&key) {
                plan.waivers
                    .extend(sites.get(&key).into_iter().flatten().cloned());
                plan.lendable.insert(key);
            }
        }
    }
    plan.waivers.sort();
    plan
}
