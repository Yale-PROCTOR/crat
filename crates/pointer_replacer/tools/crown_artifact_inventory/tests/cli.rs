use std::{
    env, fs,
    path::{Path, PathBuf},
    process::{self, Command, Output},
    sync::atomic::{AtomicU64, Ordering},
};

const OUTPUT_FILES: [&str; 5] = [
    "2026-07-27-crown-code-counts.csv",
    "2026-07-27-crown-site-conversion-rates.csv",
    "2026-07-27-crown-json-claims.csv",
    "2026-07-27-crown-paper-declaration-consistency.csv",
    "2026-07-27-crown-official-metric-consistency.csv",
];

static NEXT_TEMP_DIR: AtomicU64 = AtomicU64::new(0);

struct Fixture {
    root: PathBuf,
    original: PathBuf,
    transformed: PathBuf,
    output: PathBuf,
}

impl Fixture {
    fn new() -> Self {
        let root = env::temp_dir().join(format!(
            "crown-artifact-inventory-{}-{}",
            process::id(),
            NEXT_TEMP_DIR.fetch_add(1, Ordering::Relaxed)
        ));
        let original = root.join("original");
        let transformed = root.join("transformed");
        let output = root.join("output");
        let original_program = original.join("avl");
        let transformed_program = transformed.join("avl");
        let analysis_results = transformed_program.join("analysis_results");

        fs::create_dir_all(&original_program).unwrap();
        fs::create_dir_all(&analysis_results).unwrap();
        fs::write(original_program.join("src.rs"), "fn original() {}\n").unwrap();
        fs::write(transformed_program.join("src.rs"), "fn transformed() {}\n").unwrap();
        fs::write(
            transformed.join("evaluation.tsv"),
            concat!(
                "Benchmark Name,#Unsafe Mutable Non-Array Pointers,,,#Unsafe Mutable Non-Array Usages,,\n",
                "avl,2414,1711,29.1%,0,0,NaN%\n"
            ),
        )
        .unwrap();

        let empty_qualifiers = r#"{"fn_data": {}, "struct_data": {}}"#;
        for name in ["ownership", "mutability", "fatness"] {
            fs::write(
                analysis_results.join(format!("{name}.json")),
                empty_qualifiers,
            )
            .unwrap();
        }
        fs::write(
            analysis_results.join("statistics.json"),
            r#"{
                "num_unsafe_ptrs": 0,
                "num_non_arr_unsafe_ptrs": 0,
                "num_mut_unsafe_ptrs": 0,
                "num_non_arr_mut_unsafe_ptrs": 0,
                "num_unsafe_usages": 0,
                "num_non_arr_unsafe_usages": 0,
                "num_mut_unsafe_usages": 0,
                "num_non_arr_mut_unsafe_usages": 0,
                "num_owning_ptrs_detected": 0
            }"#,
        )
        .unwrap();

        Self {
            root,
            original,
            transformed,
            output,
        }
    }

    fn run(&self) -> Output {
        Command::new(env!("CARGO_BIN_EXE_crown_artifact_inventory"))
            .arg(&self.original)
            .arg(&self.transformed)
            .arg(&self.output)
            .output()
            .unwrap()
    }

    fn analysis_path(&self, name: &str) -> PathBuf {
        self.transformed.join("avl/analysis_results").join(name)
    }

    fn transformed_rust_path(&self) -> PathBuf {
        self.transformed.join("avl/src.rs")
    }

    fn original_rust_path(&self) -> PathBuf {
        self.original.join("avl/src.rs")
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

fn assert_no_authoritative_output(path: &Path) {
    assert!(
        !path.exists(),
        "failed inventory must not create the output directory: {}",
        path.display()
    );
}

#[test]
fn writes_all_authoritative_csvs_for_complete_inputs() {
    let fixture = Fixture::new();

    let result = fixture.run();

    assert!(result.status.success(), "{}", stderr(&result));
    for name in OUTPUT_FILES {
        assert!(
            fixture.output.join(name).is_file(),
            "missing successful output {name}"
        );
    }
}

#[test]
fn rejects_missing_required_analysis_input_before_writing_csvs() {
    let fixture = Fixture::new();
    fs::remove_file(fixture.analysis_path("fatness.json")).unwrap();

    let result = fixture.run();

    assert!(!result.status.success());
    let error = stderr(&result);
    assert!(error.contains("missing required analysis JSON"), "{error}");
    assert!(error.contains("fatness"), "{error}");
    assert_no_authoritative_output(&fixture.output);
}

#[test]
fn rejects_unparseable_rust_input_before_writing_csvs() {
    let fixture = Fixture::new();
    fs::write(fixture.transformed_rust_path(), "fn broken(").unwrap();

    let result = fixture.run();

    assert!(!result.status.success());
    let error = stderr(&result);
    assert!(error.contains("unparseable Rust input"), "{error}");
    assert!(error.contains("transformed:src.rs"), "{error}");
    assert_no_authoritative_output(&fixture.output);
}

#[test]
fn rejects_unparseable_analysis_json_before_writing_csvs() {
    let fixture = Fixture::new();
    fs::write(fixture.analysis_path("fatness.json"), "{").unwrap();

    let result = fixture.run();

    assert!(!result.status.success());
    let error = stderr(&result);
    assert!(error.contains("invalid analysis JSON"), "{error}");
    assert_no_authoritative_output(&fixture.output);
}

#[test]
fn rejects_empty_rust_inputs_before_writing_csvs() {
    let fixture = Fixture::new();
    fs::remove_file(fixture.original_rust_path()).unwrap();
    fs::remove_file(fixture.transformed_rust_path()).unwrap();

    let result = fixture.run();

    assert!(!result.status.success());
    let error = stderr(&result);
    assert!(
        error.contains("missing required Rust input files"),
        "{error}"
    );
    assert_no_authoritative_output(&fixture.output);
}

#[test]
fn rejects_mismatched_rust_file_sets_before_writing_csvs() {
    let fixture = Fixture::new();
    fs::write(fixture.original.join("avl/extra.rs"), "fn extra() {}\n").unwrap();

    let result = fixture.run();

    assert!(!result.status.success());
    let error = stderr(&result);
    assert!(
        error.contains("Rust input file sets do not match"),
        "{error}"
    );
    assert_no_authoritative_output(&fixture.output);
}
