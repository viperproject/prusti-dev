//! A module that invokes the verifier `prusti-viper`

use crate::specs::typed;
use log::{debug, trace, warn};
use prusti_interface::{
    data::{VerificationResult, VerificationTask},
    environment::Environment,
};
use prusti_viper::verifier::Verifier;
use rustc_middle::ty::TyCtxt;
use prusti_interface::config::ConfigFlags;
use prusti_common::report::user;


pub fn verify<'tcx>(flags: ConfigFlags, tcx: TyCtxt<'tcx>, spec: typed::SpecificationMap<'tcx>) {
    trace!("[verify] enter");

    let env = Environment::new(tcx);

    if env.has_errors() {
        warn!("The compiler reported an error, so the program will not be verified.");
    } else {
        debug!("Specification consists of {} elements.", spec.len());

        debug!("Prepare verification task...");
        let annotated_procedures = env.get_annotated_procedures();
        let verification_task = VerificationTask {
            procedures: annotated_procedures,
        };
        debug!("Verification task: {:?}", &verification_task);

        user::message(format!(
            "Verification of {} items...",
            verification_task.procedures.len()
        ));

        if flags.print_collected_verfication_items {
            println!("Collected verification items {}:", verification_task.procedures.len());
            for procedure in &verification_task.procedures {
                println!("procedure: {} at {:?}", env.get_item_def_path(*procedure), env.get_item_span(*procedure));
            }
        }

        let verification_result = if verification_task.procedures.is_empty() {
            VerificationResult::Success
        } else {
            //         debug!("Dump borrow checker info...");
            //         env.dump_borrowck_info(&verification_task.procedures);

            let mut verifier = Verifier::new(&env, &spec);
            let verification_result = verifier.verify(&verification_task);
            debug!("Verifier returned {:?}", verification_result);

            verification_result
        };

        match verification_result {
            VerificationResult::Success => {
                user::message(format!(
                    "Successful verification of {} items",
                    verification_task.procedures.len()
                ));
            }
            VerificationResult::Failure => {
                user::message("Verification failed");
                debug_assert!(env.has_errors());
            }
        };
    }

    trace!("[verify] exit");
}
