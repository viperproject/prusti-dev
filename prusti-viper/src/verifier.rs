// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::Encoder;
use encoder::vir::ToViper;
use prusti_interface::data::VerificationResult;
use prusti_interface::data::VerificationTask;
use prusti_interface::environment::EnvironmentImpl;
use prusti_interface::verifier::VerificationContext as VerificationContextSpec;
use prusti_interface::verifier::Verifier as VerifierSpec;
use prusti_interface::verifier::VerifierBuilder as VerifierBuilderSpec;
use prusti_interface::report::Log;
use viper::{self, Viper, VerificationBackend};
use prusti_interface::specifications::{TypedSpecificationMap};
use prusti_filter::validators::{Validator, SupportStatus};
use prusti_interface::environment::Environment;

pub struct VerifierBuilder {
    viper: Viper,
}

impl VerifierBuilder {
    pub fn new() -> Self {
        VerifierBuilder {
            viper: Viper::new(),
        }
    }
}

impl Default for VerifierBuilder {
    fn default() -> Self {
        VerifierBuilder::new()
    }
}

impl<'v, 'r, 'a, 'tcx> VerifierBuilderSpec<'v, 'r, 'a, 'tcx> for VerifierBuilder
    where
        'r: 'v,
        'a: 'r,
        'tcx: 'a
{
    type VerificationContextImpl = VerificationContext<'v>;

    fn new_verification_context(&'v self) -> VerificationContext<'v> {
        let verification_ctx = self.viper.new_verification_context();
        VerificationContext::new(verification_ctx)
    }
}

pub struct VerificationContext<'v> {
    verification_ctx: viper::VerificationContext<'v>
}

impl<'v> VerificationContext<'v> {
    pub fn new(verification_ctx: viper::VerificationContext<'v>) -> Self {
        VerificationContext { verification_ctx }
    }
}

impl<'v, 'r, 'a, 'tcx> VerificationContextSpec<'v, 'r, 'a, 'tcx> for VerificationContext<'v>
    where
        'r: 'v,
        'a: 'r,
        'tcx: 'a
{
    type VerifierImpl = Verifier<'v, 'r, 'a, 'tcx>;

    fn new_verifier(&'v self, env: &'v EnvironmentImpl<'r, 'a, 'tcx>, spec: &'v TypedSpecificationMap) -> Verifier<'v, 'r, 'a, 'tcx> {
        let backend = VerificationBackend::Silicon;

        let mut verifier_args = vec![];
        if let VerificationBackend::Silicon = backend {
            verifier_args.extend(vec![
                "--printMethodCFGs",
                "--tempDirectory", "./log/viper_tmp",
                "--logLevel", "INFO",
                //"--printTranslatedProgram",
            ]);
        } else {
            verifier_args.extend(vec![
                "--disableAllocEncoding",
                "--print", "./log/boogie_program/program.bpl",
                "--boogieOpt", "/logPrefix ./log/viper_tmp"
            ]);
        }
        Verifier::new(
            self.verification_ctx.new_ast_utils(),
            self.verification_ctx.new_ast_factory(),
            self.verification_ctx.new_verifier_with_args(
                backend,
                verifier_args
            ),
            env,
            spec
        )
    }
}

pub struct Verifier<'v, 'r, 'a, 'tcx>
    where
        'r: 'v,
        'a: 'r,
        'tcx: 'a
{
    ast_utils: viper::AstUtils<'v>,
    ast_factory: viper::AstFactory<'v>,
    verifier: viper::Verifier<'v, viper::state::Started>,
    env: &'v EnvironmentImpl<'r, 'a, 'tcx>,
    spec: &'v TypedSpecificationMap,
    encoder: Encoder<'v, 'r, 'a, 'tcx>,
}

impl<'v, 'r, 'a, 'tcx> Verifier<'v, 'r, 'a, 'tcx> {
    pub fn new(
        ast_utils: viper::AstUtils<'v>,
        ast_factory: viper::AstFactory<'v>,
        verifier: viper::Verifier<'v, viper::state::Started>,
        env: &'v EnvironmentImpl<'r, 'a, 'tcx>,
        spec: &'v TypedSpecificationMap
    ) -> Self {
        Verifier {
            ast_utils,
            ast_factory,
            verifier,
            env,
            spec,
            encoder: Encoder::new(env, spec),
        }
    }
}

impl<'v, 'r, 'a, 'tcx> VerifierSpec for Verifier<'v, 'r, 'a, 'tcx> {
    fn verify(&mut self, task: &VerificationTask) -> VerificationResult {
        let validator = Validator::new(self.env.tcx());
        self.encoder.initialize();

        for &proc_id in &task.procedures {
            // Do some checks
            let is_pure_function = self.env.has_attribute_name(proc_id, "pure");

            let support_status = if is_pure_function {
                validator.pure_function_item_support_status(proc_id)
            } else {
                validator.procedure_item_support_status(proc_id)
            };

            if support_status.is_partially_supported() {
                let reasons = support_status.get_partially_supported_reasons().join(", ");
                let proc_name = self.env.get_item_name(proc_id);
                let message = if is_pure_function {
                    format!("verification of pure function '{}' is partially supported. Reasons: {}.", proc_name, reasons)
                } else {
                    format!("verification of procedure '{}' is partially supported. Reasons: {}.", proc_name, reasons)
                };
                self.env.warn(&message);
            } else if support_status.is_unsupported() {
                let reasons = support_status.get_unsupported_reasons().join(", ");
                let proc_name = self.env.get_item_name(proc_id);
                let message = if is_pure_function {
                    format!("verification of pure function '{}' is not supported. Reasons: {}.", proc_name, reasons)
                } else {
                    format!("verification of procedure '{}' is not supported. Reasons: {}.", proc_name, reasons)
                };
                self.env.err(&message);
            }
        }

        info!("Basic support checks complete"); // TODO: remove this error message?

        for &proc_id in &task.procedures {
            // We could skip the verification if `support_status.is_unsupported()`
            self.encoder.queue_encoding(proc_id)
        }
        self.encoder.process_encoding_queue();

        let ast = &self.ast_factory;

        let program = ast.program(
            &self.encoder.get_used_viper_domains(),
            &self.encoder.get_used_viper_fields().to_viper(ast),
            &self.encoder.get_used_viper_functions().into_iter().map(|m| m.to_viper(ast)).collect::<Vec<_>>(),
            &self.encoder.get_used_viper_predicates().to_viper(ast),
            &self.encoder.get_used_viper_methods().into_iter().map(|m| m.to_viper(ast)).collect::<Vec<_>>()
        );

        // Dump Viper program
        let source_path = self.env.source_path();
        let source_filename = source_path.file_name().unwrap().to_str().unwrap();
        Log::report("viper_program", format!("{}.vpr", source_filename), self.ast_utils.pretty_print(program));

        info!("Translation successful");

        let verification_result: viper::VerificationResult = self.verifier.verify(program);

        info!("Verification complete");

        let verification_errors = match verification_result {
            viper::VerificationResult::Failure(errors) => errors,
            _ => vec![]
        };

        if verification_errors.is_empty() {
            VerificationResult::Success
        } else {
            let error_manager = self.encoder.error_manager();

            for verification_error in verification_errors {
                debug!("Verification error: {:?}", verification_error);
                let compilation_error = error_manager.translate(&verification_error);
                debug!("Compilation error: {:?}", compilation_error);
                self.env.span_err_with_code(
                    compilation_error.span,
                    &compilation_error.message,
                    compilation_error.id
                )
            }
            VerificationResult::Failure
        }
    }

    fn invalidate_all(&mut self) {
        unimplemented!()
    }
}
