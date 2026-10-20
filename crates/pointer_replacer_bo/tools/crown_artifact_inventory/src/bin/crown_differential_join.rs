use std::{env, path::PathBuf};

use crown_artifact_inventory::differential_join::{run, JoinInputs};

fn main() -> Result<(), String> {
    let arguments = env::args_os().skip(1).collect::<Vec<_>>();
    if arguments.len() != 7 {
        return Err("usage: crown_differential_join <raw-root> <transformed-root> <p2-root> <a4-root> <source-reference-root> <preregistered-inputs> <output>".to_owned());
    }
    let inputs = JoinInputs {
        raw_root: PathBuf::from(&arguments[0]),
        transformed_root: PathBuf::from(&arguments[1]),
        p2_root: PathBuf::from(&arguments[2]),
        a4_root: PathBuf::from(&arguments[3]),
        source_reference_root: PathBuf::from(&arguments[4]),
        preregistered_inputs: PathBuf::from(&arguments[5]),
        output: PathBuf::from(&arguments[6]),
    };
    let summary = run(&inputs)?;
    println!("manifest={}", summary.manifest);
    println!("rows={}", summary.rows);
    println!("boxed={}", summary.boxed);
    println!("hard_unsat={}", summary.hard_unsat);
    println!("force_sat={}", summary.force_sat);
    Ok(())
}
