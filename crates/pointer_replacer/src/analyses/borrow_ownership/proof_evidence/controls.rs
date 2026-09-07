//! H02/H10: existing admission controls around the recording-only exporters.
use std::collections::BTreeMap;

use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::mir::VarDebugInfoContents;

use crate::{
    analyses::borrow_ownership::{
        SlotKind,
        construction::{CopyLendMode, construct_bo_into, verify_bo_construction_counting},
        crate_slots::CrateSlots,
        export,
        mutability_facts::MutFacts,
        origin_evidence,
        origins::compute_origins,
        proof_evidence::ProofEvidence,
        solver::{KindSolver, SlotRef},
    },
    utils::rustc::RustProgram,
};
const DECL: &str = "unsafe extern \"C\" {fn malloc(n:usize)->*mut core::ffi::c_void;fn free(p:*mut core::ffi::c_void);}";
fn control(code: &str, own: &[&str], nonown: &[&str], refs: &[&str]) {
    let code = format!("{DECL}{code}");
    ::utils::compilation::run_compiler_on_str(&code,|tcx| {
        let mut functions=Vec::new();let mut structs=Vec::new();
        for owner in tcx.hir_crate(()).owners.iter() {
            let Some(owner)=owner.as_owner() else{continue};let OwnerNode::Item(item)=owner.node() else{continue};
            match item.kind {ItemKind::Fn{..}=>functions.push(item.owner_id.def_id),ItemKind::Struct(..)=>structs.push(item.owner_id.def_id),_=>{}}
        }
        let program=RustProgram{tcx,functions,structs};let slots=CrateSlots::build(&program);
        let origins=compute_origins(&program);let mutability=MutFacts::from_program(&program);
        let run=|| {
            let solver=KindSolver::new(&slots);
            let c=construct_bo_into(&program,&slots,&origins,&mutability,&solver,CopyLendMode::Baseline).unwrap();
            let assertions=solver.hard_assertion_count();
            let (model,rounds)=verify_bo_construction_counting(&program,&slots,&origins,&solver,&c,&mutability);
            (model.expect("existing control must remain admitted"),c.stats,c.selectors.keys().to_vec(),rounds,assertions)
        };
        let plain=run();let (captured,export)=export::with_bo_export(run);
        assert_eq!(plain,captured,"complete model, emission stats, exact selectors, ordinary replay and hard constraints remain unchanged");
        let evidence=ProofEvidence::from_export(tcx,&export);evidence.validate().unwrap();assert!(evidence.licensing_deferred);
        let origin=origin_evidence::collect(&program,&slots,&origins,Some(&export));assert!(!origin.functions.is_empty());
        assert!(export.demand_evidence.is_some());
        let did=*program.functions.iter().find(|d|tcx.item_name(d.to_def_id()).as_str()=="f").unwrap();
        let body=tcx.mir_drops_elaborated_and_const_checked(did).borrow();
        let named:BTreeMap<_,_>=body.var_debug_info.iter().filter_map(|v| {
            let VarDebugInfoContents::Place(p)=v.value else{return None};let local=p.as_local()?;
            let id=slots.fn_local_slots[&did].slot_for_local_depth(local,0)?;
            Some((v.name.to_string(),plain.0[&SlotRef::Local(did,id)]))
        }).collect();
        for name in own {assert_eq!(named[*name],SlotKind::Owning,"existing owner {name}");}
        for name in nonown {assert_eq!(named[*name],SlotKind::Raw,"unchanged anti-licensing subject {name}");}
        for name in refs {assert_eq!(named[*name],SlotKind::Ref,"existing Ref/Ref subject {name}");}
    }).unwrap_or_else(|error|error.raise());
}
#[test]
fn e5_l_evidence_mfa2_branching_reader_does_not_gain_ownership() {
    control(
        "pub unsafe fn f()->i32{let p=malloc(4) as *mut i32;let q=p;let r=p;let value=*q;free(r as *mut core::ffi::c_void);value}",
        &[],
        &["p", "q", "r"],
        &[],
    );
}
#[test]
fn e5_l_evidence_s02_stack_and_allocation_versions_do_not_gain_ownership() {
    control(
        "pub struct Holder{ptr:*mut i32} pub unsafe fn f()->i32{let mut stack=1;let mut holder=Holder{ptr:&mut stack};let mut p=malloc(4) as *mut i32;let owner=p;let mut q=p;let first=*q;p=holder.ptr;q=p;let second=*q;free(owner as *mut core::ffi::c_void);first+second}",
        &[],
        &["owner", "p", "q"],
        &[],
    );
}
#[test]
fn e5_l_evidence_linear_owner_chain_keeps_existing_ownership() {
    control(
        "pub unsafe fn f(){let p=malloc(4) as *mut i32;let q=p;free(q as *mut core::ffi::c_void);}",
        &["p", "q"],
        &[],
        &[],
    );
}
#[test]
fn e5_l_evidence_ref_ref_keeps_existing_reference_choices() {
    control(
        "pub unsafe fn f(p:*const i32)->i32{let q=p;*q}",
        &[],
        &[],
        &["p", "q"],
    );
}
