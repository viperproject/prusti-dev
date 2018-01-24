use prusti_interface::verifier::Verifier as VerifierSpec;
use prusti_interface::data::VerificationResult;
use prusti_interface::environment::Environment;
use prusti_interface::data::VerificationTask;
use viper::Viper;
use viper::Method;
use viper::VerificationError;
use viper::VerificationContext as ViperVerificationContext;
use viper::VerificationResult as ViperVerificationResult;
use viper::Verifier as ViperVerifier;
use viper::state as verifier_state;
use viper::AstFactory as ViperAstFactory;

pub struct VerifierBuilder {
    viper: Viper,
}

impl VerifierBuilder {
    pub fn new() -> Self {
        VerifierBuilder {
            viper: Viper::new(),
        }
    }

    pub fn new_verification_context(&mut self) -> VerificationContext {
        let verification_ctx = self.viper.new_verification_context();
        VerificationContext::new(verification_ctx)
    }
}

pub struct VerificationContext<'a> {
    verification_ctx: ViperVerificationContext<'a>,
}

impl<'a> VerificationContext<'a> {
    pub fn new(verification_ctx: ViperVerificationContext<'a>) -> Self {
        VerificationContext { verification_ctx }
    }

    pub fn new_verifier(&mut self) -> Verifier {
        Verifier::new(
            self.verification_ctx.new_verifier(),
            self.verification_ctx.new_ast_factory(),
        )
    }
}

pub struct Verifier<'a> {
    verifier: ViperVerifier<'a, verifier_state::Started>,
    verifier_ast: ViperAstFactory<'a>,
    // procedure_table: ProcedureTable,
    // fields_table: FieldsTable,
    // ...
}

impl<'a> Verifier<'a> {
    pub fn new(
        verifier: ViperVerifier<'a, verifier_state::Started>,
        verifier_ast: ViperAstFactory<'a>,
    ) -> Self {
        Verifier {
            verifier,
            verifier_ast,
            // procedure_table: ProcedureTable::new(),
            // ...
        }
    }
}

impl<'a> VerifierSpec for Verifier<'a> {
    fn verify(&mut self, _env: &mut Environment, _task: &VerificationTask) -> VerificationResult {
        // let epoch = env.get_current_epoch();
        let verification_methods: Vec<Method> = vec![];
        let mut verification_errors: Vec<VerificationError> = vec![];
        /* TODO
        for proc_id in &task.procedures {
            let method_or_result = self.procedure_table.get_use(procedure, epoch);
            match method_or_result {
                Left(method) => verification_methods.push(method),
                Right(errors) => verification_errors.append(errors)
            }
        }
        let verification_fields: Vec<Field> = fields_table.get_used_definitnions(epoch);
        let program = self.verifier_ast.program(&[], &verification_fields, &[], &[], &verification_methods);
        */
        let program = self.verifier_ast.program(&[], &[], &[], &[], &verification_methods);
        let verification_result: ViperVerificationResult = self.verifier.verify(program);
        if let ViperVerificationResult::Failure(mut errors) = verification_result {
            verification_errors.append(&mut errors)
        }

        if verification_errors.is_empty() {
            VerificationResult::Success
        } else {
            for error in verification_errors {
                debug!("Verification error: {:?}", error);
                // TODO: emit errors using env?
            }
            VerificationResult::Failure
        }
    }

    fn invalidate_all(&mut self, _env: &mut Environment) {
        // self.procedure_table = ProcedureTable::new()
    }
}
