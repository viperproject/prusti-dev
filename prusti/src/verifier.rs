//! A module that invokes the verifier `prusti-viper`

use log::{debug, warn};
use prusti_utils::{config, report::user};
use prusti_interface::{
    data::{VerificationResult, VerificationTask},
    environment::Environment,
    specs::typed,
};
use prusti_rustc_interface::errors::MultiSpan;

#[tracing::instrument(name = "prusti::verify", level = "debug", skip(env))]
pub fn verify(env: Environment<'_>, def_spec: typed::DefSpecificationMap) {
    if env.diagnostic.has_errors() {
        warn!("The compiler reported an error, so the program will not be verified.");
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

        // encode the crate to a RequestWithContext
        // TODO: push RequestWithContext through (replace VerificationRequest
        //   which is constructed further inside `prusti_server`)
        let request = prusti_encoder::test_entrypoint(
            env.tcx(),
            env.body,
            def_spec,
        );
        let program = request.program;

        let mut results = prusti_server::verify_programs(vec![program]);
        assert_eq!(results.len(), 1); // TODO: eventually verify separate methods as separate programs again?

        let result = results.pop().unwrap().1;
        println!("verification result: {result:?}");

        let success = match result {
            viper::VerificationResult::Success => true,
            viper::VerificationResult::JavaException(_e) => false,
            viper::VerificationResult::ConsistencyErrors(_e) => false,
            viper::VerificationResult::Failure(errors) => {
                errors
                    .into_iter()
                    .flat_map(|error| prusti_encoder::backtranslate_error(
                            &error.full_id,
                            error.offending_pos_id.unwrap().parse::<usize>().unwrap(),
                            error.reason_pos_id.and_then(|id| id.parse::<usize>().ok()),
                        )
                        .expect("verification error could not be backtranslated")
                        .into_iter())
                    .for_each(|prusti_error| prusti_error.emit(&env.diagnostic));
                false
            }
        };
        if !success {
            // TODO: This will be unnecessary if diagnostic errors are emitted
            // earlier, it's useful for now to ensure that Prusti returns an
            // error code when verification fails
            env.diagnostic.span_err_with_help_and_notes(
                MultiSpan::new(),
                "Verification failed",
                &None,
                &[],
            );
        }

        //let verification_result =
        //    if verification_task.procedures.is_empty() && verification_task.types.is_empty() {
        //        VerificationResult::Success
        //    } else {
        //        debug!("Dump borrow checker info...");
        //        env.dump_borrowck_info(&verification_task.procedures);
        //
        //        let mut verifier = Verifier::new(&env, def_spec);
        //        let verification_result = verifier.verify(&verification_task);
        //        debug!("Verifier returned {:?}", verification_result);
        //
        //        verification_result
        //    };
        //
        //match verification_result {
        //    VerificationResult::Success => {
        //        if env.diagnostic.has_errors() {
        //            user::message(
        //                "Verification result is inconclusive because errors \
        //                               were encountered during encoding.",
        //            );
        //        } else {
        //            user::message(format!(
        //                "Successful verification of {} items",
        //                verification_task.procedures.len()
        //            ));
        //        }
        //    }
        //    VerificationResult::Failure => {
        //        user::message("Verification failed");
        //        assert!(
        //            env.diagnostic.has_errors()
        //                || config::internal_errors_as_warnings()
        //                || (config::skip_unsupported_features()
        //                    && config::allow_unreachable_unsupported_code())
        //        );
        //    }
        //};
    }
}
