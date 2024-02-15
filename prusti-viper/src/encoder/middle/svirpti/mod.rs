use crate::encoder::Encoder;
use prusti_common::vir::program::Program;
use vir_crate::low as vir_low;

mod smt;

pub(crate) fn verify_core_proof_programs(
    encoder: &mut Encoder,
) -> prusti_interface::data::VerificationResult {
    let programs = encoder.get_core_proof_programs();
    for program in programs {
        let Program::Low(program) = program else {
            unimplemented!("TODO: A proper error message here.");
        };
        let result = verify_program(encoder, program);
        unimplemented!();
    }
    unimplemented!();
}

struct VerificationResult {}

fn verify_program(encoder: &mut Encoder, program: vir_low::Program) -> VerificationResult {
    let mut smt_solver = smt::SmtSolver::default().unwrap();
    let result = smt_solver.check_sat().unwrap();
    assert!(result.is_sat());
    unimplemented!();
}
