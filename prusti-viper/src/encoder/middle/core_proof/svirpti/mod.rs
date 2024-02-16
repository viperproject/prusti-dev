use crate::encoder::{errors::SpannedEncodingResult, Encoder};
use vir_crate::low as vir_low;

mod smt;

#[derive(Debug)]
pub(super) struct VerificationResult {}

pub(super) fn verify_program(
    encoder: &mut Encoder,
    program: vir_low::Program,
) -> SpannedEncodingResult<VerificationResult> {
    let mut smt_solver = smt::SmtSolver::default().unwrap();
    let result = smt_solver.check_sat().unwrap();
    assert!(result.is_sat());
    unimplemented!();
}
