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
        self.encoder.initialize();

        for proc_id in &task.procedures {
            self.encoder.queue_encoding(*proc_id)
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

        let verification_result: viper::VerificationResult = self.verifier.verify(program);

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
