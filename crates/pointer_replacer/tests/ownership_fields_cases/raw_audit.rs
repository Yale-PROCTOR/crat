use ownership_fields::raw_audit::*;

use super::*;
fn audit() -> RawAudit {
    let hash = [7; 32];
    RawAudit {
        source_hash: hash,
        complete_inventory: Some(hash),
        occurrences: vec![],
        compile: TreeCheck {
            source_hash: hash,
            passed: true,
        },
        custody: TreeCheck {
            source_hash: hash,
            passed: true,
        },
        literal_exceptions: BTreeSet::new(),
    }
}
#[test]
fn only_the_exact_printf_literal_cast_can_be_exempted() {
    let mut a = audit();
    let literal = PrintfLiteralCast {
        site: site(0),
        callee: OwnerId(9),
        argument: 0,
        literal: [3; 32],
    };
    a.literal_exceptions.insert(literal.clone());
    a.occurrences.push(RawOccurrence {
        site: site(0),
        kind: RawKind::LiteralCast(literal),
    });
    assert_eq!(bst_emitted_zero_raw(&a), Ok(()));
    a.occurrences[0].kind = RawKind::DeclarationType;
    assert_eq!(
        bst_emitted_zero_raw(&a),
        Err(RawAuditHold::Residual(site(0)))
    );
}
#[test]
fn inferred_raw_operation_and_mismatched_compile_tree_fail_the_gate() {
    let mut a = audit();
    a.occurrences.push(RawOccurrence {
        site: site(1),
        kind: RawKind::InferredPointer,
    });
    assert_eq!(
        bst_emitted_zero_raw(&a),
        Err(RawAuditHold::Residual(site(1)))
    );
    a.occurrences.clear();
    a.compile.source_hash = [8; 32];
    assert_eq!(bst_emitted_zero_raw(&a), Err(RawAuditHold::Compile));
}
