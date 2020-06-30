// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

// use encoder::vir::{self, optimisations, ToViper, ToViperDecl};
use crate::encoder::Encoder;
// use prusti_filter::validators::Validator;
use prusti_interface::config;
use prusti_interface::data::VerificationResult;
use prusti_interface::data::VerificationTask;
use prusti_interface::environment::Environment;
use prusti_interface::report::log;
// use prusti_interface::specifications::TypedSpecificationMap;
use std::time::Instant;
use viper::{self, VerificationBackend, Viper};
use std::path::PathBuf;
use std::fs::{create_dir_all, canonicalize};
// use std::ffi::OsString;
use prusti_interface::specs::typed;
use ::log::info;

/// A verifier builder is an object that lives entire program's
/// lifetime, has no mutable state, and is responsible for constructing
/// verification context instances. The user of this interface is supposed
/// to create a new verifier for each crate he or she wants to verify.
/// The main motivation for having a builder is to be able to cache the JVM
/// initialization.
pub struct VerifierBuilder {
    viper: Viper,
}

impl VerifierBuilder {
    pub fn new() -> Self {
        VerifierBuilder {
            viper: Viper::new_with_args(
                config::extra_jvm_args(),
                VerificationBackend::from_str(&config::viper_backend())
            ),
        }
    }

    pub fn new_verification_context(&self) -> VerificationContext {
        let verification_ctx = self.viper.new_verification_context();
        VerificationContext::new(verification_ctx)
    }
}

impl Default for VerifierBuilder {
    fn default() -> Self {
        VerifierBuilder::new()
    }
}

/// A verification context is an object that lives entire verification's lifetime.
/// Its main purpose is to build verifiers.
/// The main motivation for having a verification context is to be able to detach the current
/// thread from the JVM when the verification context goes out of scope.
pub struct VerificationContext<'v> {
    verification_ctx: viper::VerificationContext<'v>,
}

impl<'v, 'r, 'a, 'tcx> VerificationContext<'v>
    where
        'r: 'v,
        'a: 'r,
        'tcx: 'a,
{
    fn new(verification_ctx: viper::VerificationContext<'v>) -> Self {
        VerificationContext { verification_ctx }
    }

    pub fn new_verifier(
        &'v self,
        env: &'v Environment<'tcx>,
        spec: &'v typed::SpecificationMap<'tcx>,
    ) -> Verifier<'v, 'tcx> {
        let backend = VerificationBackend::from_str(&config::viper_backend());

        let mut verifier_args: Vec<String> = vec![];
        let log_path: PathBuf = PathBuf::from(config::log_dir()).join("viper_tmp");
        create_dir_all(&log_path).unwrap();
        let report_path: PathBuf = log_path.join("report.csv");
        let log_dir_str = log_path.to_str().unwrap();
        if let VerificationBackend::Silicon = backend {
            if config::use_more_complete_exhale() {
                verifier_args.push("--enableMoreCompleteExhale".to_string()); // Buggy :(
            }
            verifier_args.extend(vec![
                "--assertTimeout".to_string(),
                config::assert_timeout().to_string(),
                "--tempDirectory".to_string(),
                log_dir_str.to_string(),
                //"--logLevel".to_string(), "WARN".to_string(),
            ]);
        } else {
            verifier_args.extend(vec![
                "--disableAllocEncoding".to_string(),
                "--boogieOpt".to_string(),
                format!("/logPrefix {}", log_dir_str),
            ]);
        }
        if config::dump_debug_info() {
            if let VerificationBackend::Silicon = backend {
                verifier_args.extend(vec![
                    "--printMethodCFGs".to_string(),
                    "--logLevel".to_string(),
                    "INFO".to_string(),
                    //"--printTranslatedProgram".to_string(),
                ]);
            } else {
                verifier_args.extend::<Vec<_>>(vec![
                    //"--print".to_string(), "./log/boogie_program/program.bpl".to_string(),
                ]);
            }
        }
        verifier_args.extend(config::extra_verifier_args());
        Verifier::new(
            self.verification_ctx.new_ast_utils(),
            self.verification_ctx.new_ast_factory(),
            self.verification_ctx
                .new_verifier_with_args(backend, verifier_args, Some(report_path)),
            env,
            spec,
        )
    }
}

/// A verifier is an object for verifying a single crate, potentially
/// many times.
pub struct Verifier<'v, 'tcx>
where
    'tcx: 'v,
{
    ast_utils: viper::AstUtils<'v>,
    ast_factory: viper::AstFactory<'v>,
    verifier: viper::Verifier<'v, viper::state::Started>,
    env: &'v Environment<'tcx>,
    encoder: Encoder<'v, 'tcx>,
}

impl<'v, 'tcx> Verifier<'v, 'tcx> {
    fn new(
        ast_utils: viper::AstUtils<'v>,
        ast_factory: viper::AstFactory<'v>,
        verifier: viper::Verifier<'v, viper::state::Started>,
        env: &'v Environment<'tcx>,
        spec: &'v typed::SpecificationMap<'tcx>,
    ) -> Self {
        Verifier {
            ast_utils,
            ast_factory,
            verifier,
            env,
            encoder: Encoder::new(env, spec),
        }
    }

    pub fn verify(&mut self, task: &VerificationTask) -> VerificationResult {
        let start = Instant::now();

        // Dump the configuration
        log::report("config", "prusti", config::dump());

        // let validator = Validator::new(self.env.tcx()); FIXME

        info!("Received {} items to be verified:", task.procedures.len());

        for &proc_id in &task.procedures {
            let proc_name = self.env.get_absolute_item_name(proc_id);
            let proc_def_path = self.env.get_item_def_path(proc_id);
            let proc_span = self.env.get_item_span(proc_id);
            info!(" - {} from {:?} ({})", proc_name, proc_span, proc_def_path);
        }

//         // Report support status
//         if config::report_support_status() {
//             for &proc_id in &task.procedures {
//                 // Do some checks
//                 let is_pure_function = self.env.has_attribute_name(proc_id, "pure");

//                 let support_status = if is_pure_function {
//                     validator.pure_function_support_status(proc_id)
//                 } else {
//                     validator.procedure_support_status(proc_id)
//                 };

//                 support_status.report_support_status(&self.env, is_pure_function, false);
//             }
//         }

        for &proc_id in task.procedures.iter().rev() {
            self.encoder.queue_procedure_encoding(proc_id);
        }
        self.encoder.process_encoding_queue();

//         let encoding_errors_count = self.encoder.count_encoding_errors();

//         let duration = start.elapsed();
//         info!(
//             "Encoding to Viper successful ({}.{} seconds)",
//             duration.as_secs(),
//             duration.subsec_millis() / 10
//         );
//         let start = Instant::now();

//         let program = {
//             let ast = &self.ast_factory;

//             let domains = self.encoder.get_used_viper_domains();
//             let fields = self.encoder.get_used_viper_fields().to_viper(ast);
//             let builtin_methods = self.encoder.get_used_builtin_methods();
//             let mut methods = self.encoder.get_used_viper_methods();
//             let mut functions = self.encoder.get_used_viper_functions();
//             if config::simplify_encoding() {
//                 let (new_methods, new_functions) = optimisations::functions::inline_constant_functions(
//                     methods, functions);
//                 methods = new_methods
//                     .into_iter()
//                     .map(|m| {
//                         let purified = optimisations::methods::purify_vars(m);
//                         optimisations::folding::FoldingOptimiser::optimise(purified)
//                     })
//                     .collect();
//                 functions = new_functions
//                     .into_iter()
//                     .map(|f| {
//                         optimisations::folding::FoldingOptimiser::optimise(f)
//                     })
//                     .collect();
//             }
//             let mut viper_functions: Vec<_> = functions.into_iter().map(|f| f.to_viper(ast)).collect();
//             let mut viper_methods: Vec<_> = methods.into_iter().map(|m| m.to_viper(ast)).collect();
//             viper_methods.extend(builtin_methods.into_iter().map(|m| m.to_viper(ast)));
//             let mut predicates = self.encoder.get_used_viper_predicates().to_viper(ast);
//             if config::verify_only_preamble() {
//                 viper_methods = Vec::new();
//             }

//             info!(
//                 "Viper encoding uses {} domains, {} fields, {} functions, {} predicates, {} methods",
//                 domains.len(), fields.len(), viper_functions.len(), predicates.len(),
//                 viper_methods.len()
//             );

//             // Add a function that represents the symbolic read permission amount.
//             viper_functions.push(ast.function(
//                 "read$",
//                 &[],
//                 ast.perm_type(),
//                 &[],
//                 &[
//                     ast.lt_cmp(ast.no_perm(), ast.result(ast.perm_type())),
//                     ast.lt_cmp(ast.result(ast.perm_type()), ast.full_perm()),
//                 ],
//                 ast.no_position(),
//                 None,
//             ));

//             // Add a predicate that represents the dead loan token.
//             predicates.push(
//                 ast.predicate(
//                     "DeadBorrowToken$",
//                     &[vir::LocalVar {
//                         name: "borrow".to_string(),
//                         typ: vir::Type::Int,
//                     }
//                         .to_viper_decl(ast)],
//                     None,
//                 ),
//             );

//             ast.program(&domains, &fields, &viper_functions, &predicates, &viper_methods)
//         };

//         if config::dump_viper_program() {
//             // Dump Viper program
//             let source_path = self.env.source_path();
//             let source_filename = source_path.file_name().unwrap().to_str().unwrap();
//             let mut dump_path = PathBuf::from("viper_program");
//             let num_parents = config::num_parents_for_dumps();
//             if num_parents > 0 {
//                 // Take `num_parents` parent folders and add them to `dump_path`
//                 let mut components = vec![];
//                 if let Some(abs_parent_path) = canonicalize(&source_path).ok().and_then(
//                     |full_path| full_path.parent().map(|parent| parent.to_path_buf())
//                 ) {
//                     components.extend(
//                         abs_parent_path.ancestors()
//                             .flat_map(|path| path.file_name())
//                             .take(num_parents as usize)
//                             .map(|x| x.to_os_string())
//                             .collect::<Vec<_>>()
//                             .into_iter()
//                             .rev()
//                     );
//                 } else {
//                     components.push(OsString::from("io_error"))
//                 }
//                 for component in components {
//                     dump_path.push(component);
//                 }
//             }
//             info!("Dumping Viper program to the {:?} folder", dump_path);
//             log::report(
//                 dump_path.to_str().unwrap(),
//                 format!("{}.vpr", source_filename),
//                 self.ast_utils.pretty_print(program),
//             );
//         }

//         let duration = start.elapsed();
//         info!(
//             "Construction of JVM objects successful ({}.{} seconds)",
//             duration.as_secs(),
//             duration.subsec_millis() / 10
//         );
//         let start = Instant::now();

//         let verification_result: viper::VerificationResult = self.verifier.verify(program);

//         let duration = start.elapsed();
//         info!(
//             "Verification complete ({}.{} seconds)",
//             duration.as_secs(),
//             duration.subsec_millis() / 10
//         );

//         let verification_errors = match verification_result {
//             viper::VerificationResult::Failure(errors) => errors,
//             _ => vec![],
//         };

//         if encoding_errors_count == 0 && verification_errors.is_empty() {
//             VerificationResult::Success
//         } else {
//             let error_manager = self.encoder.error_manager();

//             for verification_error in verification_errors {
//                 debug!("Verification error: {:?}", verification_error);
//                 let prusti_error = error_manager.translate_verification_error(&verification_error);
//                 debug!("Prusti error: {:?}", prusti_error);
//                 prusti_error.emit(self.env);
//             }
//             VerificationResult::Failure
//         }
        unimplemented!();
    }

    pub fn invalidate_all(&mut self) {
        unimplemented!()
    }
}
