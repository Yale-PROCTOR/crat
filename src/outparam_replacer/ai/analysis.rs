use std::path::Path;

use rustc_middle::ty::TyCtxt;

pub struct AnalysisResult {}

pub fn write_analysis_result(_path: &Path, _result: &AnalysisResult) {
    todo!()
}

pub fn analyze(
    _config: &crate::outparam_replacer::Config,
    _verbose: bool,
    _tcx: TyCtxt<'_>,
) -> AnalysisResult {
    todo!()
}
