//! A module that invokes the verifier `prusti-viper`

use log::{debug, warn};
use prusti_common::{config, report::user};
use prusti_interface::{
    data::{VerificationResult, VerificationTask},
    environment::Environment,
    specs::typed,
};
use prusti_viper::verifier::Verifier;

#[tracing::instrument(name = "prusti::verify", level = "debug", skip(env))]
pub fn verify(env: Environment<'_>, def_spec: typed::DefSpecificationMap) -> Environment<'_> {
    if env.diagnostic.has_errors() {
        warn!("The compiler reported an error, so the program will not be verified.");
        env
    } else {
        debug!("Prepare verification task...");
        // TODO: can we replace `get_annotated_procedures` with information
        // that is already in `def_spec`?
        let (annotated_procedures, types) = env.get_annotated_procedures_and_types();
        let verification_task = VerificationTask {
            procedures: annotated_procedures,
            types,
        };
        debug!("Verification task: {:?}", &verification_task);

        user::message(format!(
            "Verification of {} items...",
            verification_task.procedures.len()
        ));

        if config::print_collected_verification_items() {
            println!(
                "Collected verification items {}:",
                verification_task.procedures.len()
            );
            for procedure in &verification_task.procedures {
                println!(
                    "procedure: {} at {:?}",
                    env.name.get_item_def_path(*procedure),
                    env.query.get_def_span(procedure)
                );
            }
        }

        let verification_result =
            if verification_task.procedures.is_empty() && verification_task.types.is_empty() {
                VerificationResult::Success
            } else {
                debug!("Dump borrow checker info...");
                env.dump_borrowck_info(&verification_task.procedures);

                let mut verifier = Verifier::new(&env, def_spec);
                let verification_result = verifier.verify(&verification_task);
                debug!("Verifier returned {:?}", verification_result);

                verification_result
            };

        match verification_result {
            VerificationResult::Success => {
                if env.diagnostic.has_errors() {
                    user::message(
                        "Verification result is inconclusive because errors \
                                       were encountered during encoding.",
                    );
                } else {
                    user::message(format!(
                        "Successful verification of {} items",
                        verification_task.procedures.len()
                    ));
                }
            }
            VerificationResult::Failure => {
                user::message("Verification failed");
                assert!(
                    env.diagnostic.has_errors()
                        || config::internal_errors_as_warnings()
                        || (config::skip_unsupported_features()
                            && config::allow_unreachable_unsupported_code())
                );
            }
        };
        env
    }
}
