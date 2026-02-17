#![allow(non_snake_case)]

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{ItemKind, OwnerNode, def_id::DefId};
use rustc_middle::{mir::Local, ty::TyCtxt};
use rustc_span::def_id::LocalDefId;

use crate::{
    analyses::{
        output_params::compute_output_params,
        ownership::{
            AnalysisKind, CrateCtxt,
            ssa::AnalysisResults,
            whole_program::WholeProgramAnalysis,
        },
        type_qualifier::foster::mutability::mutability_analysis,
    },
    utils::rustc::RustProgram,
};

fn run_compiler<F: FnOnce(TyCtxt<'_>) + Send>(code: &str, f: F) {
    ::utils::compilation::run_compiler_on_str(code, f).unwrap_or_else(|e| e.raise());
}

fn collect_program(tcx: TyCtxt<'_>) -> RustProgram<'_> {
    let mut functions = Vec::new();
    let mut structs = Vec::new();

    for maybe_owner in tcx.hir_crate(()).owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let OwnerNode::Item(item) = owner.node() else {
            continue;
        };

        match item.kind {
            ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
            ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
            _ => {}
        }
    }

    RustProgram {
        tcx,
        functions,
        structs,
    }
}

fn analyze_program<'tcx>(
    program: &RustProgram<'tcx>,
) -> crate::analyses::ownership::whole_program::WholeProgramResults<'tcx> {
    let mutability_result = mutability_analysis(program);
    let aliases: FxHashMap<LocalDefId, FxHashMap<Local, FxHashSet<Local>>> = FxHashMap::default();
    let output_params = compute_output_params(program, &mutability_result, &aliases);
    let crate_ctxt = CrateCtxt::new(program);

    <WholeProgramAnalysis as AnalysisKind>::analyze(crate_ctxt, &output_params)
        .expect("ownership analysis should succeed")
}

pub(super) fn run_ownership_case(case_name: &str, code: &str) {
    run_compiler(code, |tcx| {
        let program = collect_program(tcx);
        let results = analyze_program(&program);
        let fns = program
            .functions
            .iter()
            .map(|did| did.to_def_id())
            .collect::<Vec<DefId>>();

        println!("== {case_name} ==");
        results.print_fn_sigs(program.tcx, &fns);
    });
}

pub mod aabb_lib;
pub mod agglom_lib;
pub mod arity_lib;
pub mod arr_del_lib;
pub mod arr_ins_lib;
pub mod arr_push_lib;
pub mod arrayfunc_lib;
pub mod basename_lib;
pub mod betagamma_lib;
pub mod buffapp_lib;
pub mod cJSON_lib;
pub mod call_predict_lib;
pub mod capsule_lib;
pub mod char_to_bool;
pub mod charinbuf_lib;
pub mod checkshift_lib;
pub mod circle_collide_lib;
pub mod cleanup_lib;
pub mod complexmode_lib;
pub mod confusion_lib;
pub mod container_of;
pub mod convert_pix_lib;
pub mod dataentry_lib;
pub mod decode_base64_lib;
pub mod doubleneg_lib;
pub mod encode_base64_lib;
pub mod envy_lib;
pub mod fallcalc_lib;
pub mod file_queue_lib;
pub mod findrep_lib;
pub mod gen_ray_lib;
pub mod generic_foreach;
pub mod get_predict_func_lib;
pub mod gjk_cache_lib;
pub mod gjk_lib;
pub mod goto_lib;
pub mod gotomach_lib;
pub mod hashmap_tree;
pub mod hatch_lib;
pub mod helxo_lib;
pub mod hm_geti_lib;
pub mod inreftree_lib;
pub mod intput_lib;
pub mod jumpnode_lib;
pub mod lines_in_buffer_lib;
pub mod load_png_mem_lib;
pub mod macrodepth_add_5;
pub mod macrodepth_mul_4;
pub mod macrodepth_sub_6;
pub mod mathop_lib;
pub mod matrix_mult_lib;
pub mod matrixsum_lib;
pub mod maxnmin_lib;
pub mod memchra2_lib;
pub mod memcpy_fun_buffers;
pub mod memmove;
pub mod modeselect_lib;
pub mod mutable_duplication_dag;
pub mod omni_collide_lib;
pub mod omni_manifold_lib;
pub mod overunder_lib;
pub mod parse_number_lib;
pub mod parse_uname_lib;
pub mod pinflate_lib;
pub mod pointer_comparison_ascii_art;
pub mod poly_ray_lib;
pub mod qmath;
pub mod rdg_genstdout_lib;
pub mod reverse_collide_lib;
pub mod search_and_replace_lib;
pub mod sh_geti_lib;
pub mod sh_puts_lib;
pub mod siphash_lib;
pub mod spec_ray_lib;
pub mod static_vars_fpts;
pub mod str_dups_lib;
pub mod str_put_lib;
pub mod strcmp;
pub mod strcpy;
pub mod strdup_lib;
pub mod task_manager_lib;
pub mod tu_linkage;
pub mod underhanded_c_luggage;
pub mod underhanded_c_nuke_lib;
pub mod unfilter_lib;
pub mod utf8_lib;
