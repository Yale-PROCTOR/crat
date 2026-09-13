use super::{RewriteOutcome, decision::DecisionTable};
use crate::analyses::borrow_ownership::a5_overlap::{A5Mode, WholeProgramAttestation};

const INPUT: &str = r#"
pub unsafe fn read_pair(a: *mut i32, b: *const i32) -> bool { *a == *b }
pub unsafe fn caller(p: *mut i32) -> bool { let answer = read_pair(&mut *p, &*p); *p = 7; answer }
"#;

fn run(inject: &(dyn Fn(&mut DecisionTable) + Sync)) -> RewriteOutcome {
    super::rewrite_core_injected(
        ::utils::compilation::str_to_input(INPUT),
        None,
        8,
        inject,
        false,
        false,
        false,
        Some((
            A5Mode::PreciseReplay,
            Some(WholeProgramAttestation::FrozenBenchmarkGraph),
        )),
    )
}

fn execute(source: &str) -> Vec<u8> {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let root = std::env::temp_dir().join(format!(
        "crat-wave5p-runtime-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&root).unwrap();
    let source = format!(
        "{source}\nfn main() {{ for initial in [i32::MIN, -1, 0, 1, i32::MAX] {{ let mut value = initial; let result = unsafe {{ caller(&mut value) }}; println!(\"{{result}}:{{value}}\"); }} }}"
    );
    std::fs::write(root.join("main.rs"), source).unwrap();
    let compile = std::process::Command::new("rustc")
        .args(["--edition=2024", "-Awarnings"])
        .arg(root.join("main.rs"))
        .arg("-o")
        .arg(root.join("run"))
        .output()
        .unwrap();
    assert!(
        compile.status.success(),
        "{}",
        String::from_utf8_lossy(&compile.stderr)
    );
    let output = std::process::Command::new(root.join("run"))
        .output()
        .unwrap();
    assert!(output.status.success());
    std::fs::remove_dir_all(root).unwrap();
    output.stdout
}

#[test]
fn w5p_emitted_shared_pair_and_runtime_agree() {
    let RewriteOutcome::Emitted {
        source,
        raw_boundary_artifacts,
        ..
    } = run(&|_| {})
    else {
        panic!("shared pair must emit");
    };
    println!(
        "SHARED EMITTED\n{source}\nRECEIPTS\n{}",
        raw_boundary_artifacts.shared_pair_receipts
    );
    let compact = source.split_whitespace().collect::<String>();
    assert!(
        compact.contains("a:&i32") && compact.contains("b:&i32"),
        "{source}"
    );
    assert!(compact.contains("read_pair(&(*p),&*p)"), "{source}");
    assert!(
        raw_boundary_artifacts
            .shared_pair_receipts
            .contains("\tapplied\t")
    );
    assert_eq!(execute(INPUT), execute(&source));
}

#[test]
fn w5p_missing_and_stale_consumed_evidence_holds_output() {
    let faults: Vec<Box<dyn Fn(&mut DecisionTable) + Sync>> = vec![
        Box::new(|table| {
            table.seams.shared_required.clear();
        }),
        Box::new(|table| {
            table.seams.overlap_proofs[0].shared_permission = None;
        }),
        Box::new(|table| {
            table.seams.shared_required[0].seal.push('x');
        }),
        Box::new(|table| {
            table
                .seams
                .edits
                .retain(|edit| edit.spec.shared_address.is_none());
        }),
        Box::new(|table| {
            table
                .seams
                .edits
                .iter_mut()
                .find_map(|edit| edit.spec.shared_address.as_mut())
                .unwrap()
                .original
                .push('x');
        }),
    ];
    for (index, fault) in faults.into_iter().enumerate() {
        let result = run(&*fault);
        let RewriteOutcome::Degraded { reason, .. } = result else {
            panic!("corrupt shared permission must hold");
        };
        assert!(
            reason.contains("shared-pair:")
                || (index == 3
                    && reason.contains("callee-parameter-input-custody:MappingInvariant")),
            "{index}: {reason}"
        );
    }
}

#[test]
fn w5p_reverted_callee_withdraws_shared_argument_and_signature() {
    ::utils::compilation::run_compiler_on_str(INPUT, |tcx| {
        let capture = super::ast_transform::capture_ast(tcx).unwrap();
        let (table, _) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        let callee = table.seams.shared_required[0]
            .request
            .left
            .callee
            .as_local()
            .unwrap();
        let withheld = [super::bridge_receipt::SignatureClassId::of(callee)]
            .into_iter()
            .collect();
        let reverts = super::ast_transform::revert_set_from_classes_and_atoms(
            &withheld,
            &Default::default(),
            &table,
        )
        .unwrap();
        let (files, _, _, _) = super::ast_transform::ast_emitted_files_from(
            tcx, &capture, &reverts, None, &table, None,
        )
        .unwrap();
        let source = files.values().cloned().collect::<String>();
        let compact = source.split_whitespace().collect::<String>();
        assert!(
            compact.contains("a:*muti32") && compact.contains("b:*consti32"),
            "{source}"
        );
        assert!(
            !compact.contains("read_pair(&(*p),"),
            "the shared-address plan must retract: {source}"
        );
        assert!(
            compact.contains("from_mut") && compact.contains("from_ref"),
            "the existing raw-call bridges remain: {source}"
        );
        let receipt = super::shared_pair_ast::terminal(
            &table.seams.shared_required,
            &withheld,
            &Default::default(),
        );
        assert!(receipt.contains("\tretracted\t"));
    })
    .unwrap();
}
