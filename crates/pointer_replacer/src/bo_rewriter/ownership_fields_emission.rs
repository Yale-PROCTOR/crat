//! Typed emission plans over supplied grants. This is not a grant producer or
//! an AST parser. Expressions/types are compiler-rendered inputs at integration.
use super::{
    EvidenceKey,
    lifecycle::{CloseKind, ClosePlan},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    Raw,
    Ref,
    Owning,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GrantStatus {
    Candidate,
    Selected,
    Retracted,
}
#[derive(Clone, Debug)]
pub struct Grant {
    pub key: EvidenceKey,
    pub kind: Kind,
    pub status: GrantStatus,
    pub transport: Option<EvidenceKey>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Span {
    pub start: u32,
    pub end: u32,
}
#[derive(Clone, Debug)]
pub struct ReferenceInterval {
    /// Same-generation regions may overlap. Disjoint subregions require a
    /// future region proof; this consumer intentionally covers whole payloads.
    pub generation: u64,
    pub live: Span,
    pub protected: Option<Span>,
}
#[derive(Clone, Debug)]
pub struct OwnCallFacts {
    pub key: EvidenceKey,
    pub call: Span,
    pub protector: Span,
    pub whole_payload: bool,
    pub references: Vec<ReferenceInterval>,
    pub reference_inventory: Option<EvidenceKey>,
    pub helper_lowering: Option<EvidenceKey>,
    pub permission: Option<EvidenceKey>,
    pub transfer_cleanup: Option<EvidenceKey>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EmitHold {
    Grant,
    Transport,
    CallIdentity,
    CallSpan,
    Payload,
    LiveReference,
    Protector,
    MissingEvidence(&'static str),
    WrongClose,
    SinkIdentity,
    Construction,
}

/// Private validated permit, returned only after exact-key evidence checks.
#[derive(Clone, Debug)]
pub struct OwnCallPermit {
    key: EvidenceKey,
}

pub fn admit_call(grant: &Grant, facts: &OwnCallFacts) -> Result<OwnCallPermit, EmitHold> {
    if grant.kind != Kind::Owning || grant.status != GrantStatus::Selected {
        return Err(EmitHold::Grant);
    }
    if grant.transport != Some(grant.key) {
        return Err(EmitHold::Transport);
    }
    if grant.key != facts.key {
        return Err(EmitHold::CallIdentity);
    }
    if facts.call.start >= facts.call.end || facts.protector != facts.call {
        return Err(EmitHold::CallSpan);
    }
    if !facts.whole_payload {
        return Err(EmitHold::Payload);
    }
    for (name, evidence) in [
        ("reference-inventory", facts.reference_inventory),
        ("helper-lowering", facts.helper_lowering),
        ("permission", facts.permission),
        ("transfer-cleanup", facts.transfer_cleanup),
    ] {
        if evidence != Some(facts.key) {
            return Err(EmitHold::MissingEvidence(name));
        }
    }
    let overlaps = |span: Span| {
        span.start < span.end && span.start < facts.call.end && facts.call.start < span.end
    };
    for reference in &facts.references {
        if reference.live.start > reference.live.end
            || reference.protected.is_some_and(|s| s.start > s.end)
        {
            return Err(EmitHold::CallSpan);
        }
        if reference.generation != facts.key.generation {
            continue;
        }
        if overlaps(reference.live) {
            return Err(EmitHold::LiveReference);
        }
        if reference.protected.is_some_and(overlaps) {
            return Err(EmitHold::Protector);
        }
    }
    Ok(OwnCallPermit { key: facts.key })
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OwnerType {
    pub pointee: String,
    pub optional: bool,
}
impl OwnerType {
    pub fn render(&self) -> String {
        let boxed = format!("Box<{}>", self.pointee);
        if self.optional {
            format!("Option<{boxed}>")
        } else {
            boxed
        }
    }
}
#[derive(Clone, Debug)]
pub enum OwnerInput {
    /// Pure transfer. No borrowed lifetime origin or in-body allocator needed.
    Transfer {
        expression: String,
    },
    /// Valid typed construction already established at the allocation site.
    Construct {
        value: String,
        layout: Option<EvidenceKey>,
        initialization: Option<EvidenceKey>,
    },
    Null,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Emitted {
    pub code: String,
    pub key: EvidenceKey,
    pub receipt: &'static str,
}

pub fn receiver(
    permit: &OwnCallPermit,
    name: &str,
    ty: &OwnerType,
    input: &OwnerInput,
) -> Result<Emitted, EmitHold> {
    let expression = match input {
        OwnerInput::Transfer { expression } => expression.clone(),
        OwnerInput::Construct {
            value,
            layout,
            initialization,
        } => {
            if *layout != Some(permit.key) || *initialization != Some(permit.key) {
                return Err(EmitHold::Construction);
            }
            let boxed = format!("Box::new({value})");
            if ty.optional {
                format!("Some({boxed})")
            } else {
                boxed
            }
        }
        OwnerInput::Null if ty.optional => "None".into(),
        OwnerInput::Null => return Err(EmitHold::Construction),
    };
    Ok(Emitted {
        code: format!("let mut {name}: {} = {expression};", ty.render()),
        key: permit.key,
        receipt: "owning-receiver",
    })
}

/// Local-only suppression carrier. Fields keep the declared Option<Box<_>>
/// interface; field/aggregate cleanup needs a separate transaction lowering.
#[derive(Clone, Debug)]
pub struct LeakLocal {
    key: EvidenceKey,
    name: String,
    ty: OwnerType,
    suppressed_closes: Vec<ClosePlan>,
}

/// Complete adapter-supplied implicit-exit inventory for one local generation.
/// A single scope/overwrite receipt cannot authorize unconditional suppression.
#[derive(Clone, Debug)]
pub struct LeakCoverage {
    pub local: EvidenceKey,
    pub completeness: Option<EvidenceKey>,
    pub closes: Vec<ClosePlan>,
}

impl LeakCoverage {
    fn validate(&self) -> Result<(), EmitHold> {
        if self.completeness != Some(self.local) {
            return Err(EmitHold::MissingEvidence("leak-exit-inventory"));
        }
        let mut scope = false;
        let mut unwind = false;
        for plan in &self.closes {
            match plan {
                ClosePlan::LeakRecursive { key, kind } if same_generation(*key, self.local) => {
                    match kind {
                        CloseKind::ScopeExit => scope = true,
                        CloseKind::Unwind => unwind = true,
                        CloseKind::Overwrite => {}
                    }
                }
                _ => return Err(EmitHold::WrongClose),
            }
        }
        if !scope {
            return Err(EmitHold::MissingEvidence("leak-scope-coverage"));
        }
        if !unwind {
            return Err(EmitHold::MissingEvidence("leak-unwind-coverage"));
        }
        Ok(())
    }
}

fn same_generation(a: EvidenceKey, b: EvidenceKey) -> bool {
    a.model == b.model
        && a.configuration == b.configuration
        && a.generation == b.generation
        && a.site.owner == b.site.owner
}

pub fn leak_local(
    coverage: &LeakCoverage,
    name: &str,
    ty: OwnerType,
    initializer: &str,
) -> Result<(LeakLocal, Emitted), EmitHold> {
    coverage.validate()?;
    let key = coverage.local;
    let code = format!(
        "let mut {name}: std::mem::ManuallyDrop<{}> = std::mem::ManuallyDrop::new({initializer});",
        ty.render()
    );
    Ok((
        LeakLocal {
            key,
            name: name.into(),
            ty,
            suppressed_closes: coverage.closes.clone(),
        },
        Emitted {
            code,
            key,
            receipt: "waiver-leak(recursive-drop)",
        },
    ))
}

impl LeakLocal {
    pub fn suppressed_closes(&self) -> &[ClosePlan] {
        &self.suppressed_closes
    }

    /// Old and replacement generations each have their own admitted leak plan.
    /// RHS is wrapped before installation; unwinding it cannot drop the old
    /// ManuallyDrop payload. The supplying lowering witness still covers RHS
    /// internal temporaries, which are not protected by this local wrapper.
    pub fn overwrite(
        &mut self,
        old: &ClosePlan,
        new: &LeakCoverage,
        initializer: &str,
    ) -> Result<Emitted, EmitHold> {
        let ClosePlan::LeakRecursive {
            key: old_key,
            kind: CloseKind::Overwrite,
        } = old
        else {
            return Err(EmitHold::WrongClose);
        };
        new.validate()?;
        let new_key = &new.local;
        if !same_generation(self.key, *old_key)
            || old_key.model != new_key.model
            || old_key.configuration != new_key.configuration
            || old_key.site.owner != new_key.site.owner
            || old_key.generation == new_key.generation
        {
            return Err(EmitHold::WrongClose);
        }
        self.key = *new_key;
        self.suppressed_closes = new.closes.clone();
        Ok(Emitted {
            code: format!(
                "{} = std::mem::ManuallyDrop::new({initializer});",
                self.name
            ),
            key: *old_key,
            receipt: old.receipt(),
        })
    }

    /// A C free still consumes exactly once. Safe into_inner moves initialized
    /// storage; it never moves a ManuallyDrop<Box<_>> that has been destroyed.
    pub fn free(
        self,
        permit: &OwnCallPermit,
        sink: EvidenceKey,
        allocator_layout: Option<EvidenceKey>,
    ) -> Result<Emitted, EmitHold> {
        if !same_generation(self.key, sink) {
            return Err(EmitHold::SinkIdentity);
        }
        if self.ty.optional {
            explicit_free(permit, sink, &self.name, true, allocator_layout)
        } else {
            let expression = format!("std::mem::ManuallyDrop::into_inner({})", self.name);
            explicit_free(permit, sink, &expression, false, allocator_layout)
        }
    }
}

pub fn consume_argument(
    permit: &OwnCallPermit,
    expression: &str,
    optional_storage: bool,
) -> Emitted {
    Emitted {
        code: if optional_storage {
            format!("({expression}).take()")
        } else {
            expression.into()
        },
        key: permit.key,
        receipt: "owning-argument-move",
    }
}

/// The integration adapter resolves transparent free-site casts to this sink.
/// This function never matches by count, source order or variable spelling.
pub fn explicit_free(
    permit: &OwnCallPermit,
    sink: EvidenceKey,
    owner: &str,
    optional_storage: bool,
    allocator_layout: Option<EvidenceKey>,
) -> Result<Emitted, EmitHold> {
    if permit.key != sink || allocator_layout != Some(sink) {
        return Err(EmitHold::SinkIdentity);
    }
    let argument = consume_argument(permit, owner, optional_storage);
    Ok(Emitted {
        code: format!("drop({});", argument.code),
        key: sink,
        receipt: "c-free-site-drop",
    })
}
