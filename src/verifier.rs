use prusti_interface::verifier::VerifierBuilder as VerifierBuilderSpec;
use prusti_interface::verifier::Verifier as VerifierSpec;
use prusti_interface::data::VerificationResult;
use prusti_interface::environment::Environment;
use prusti_interface::data::VerificationTask;
use prusti_interface::data::Procedure;
use viper::Viper;
use viper::VerificationError;
use viper::VerificationContext;
use viper::VerificationResult as ViperVerificationResult;
use viper::verifier::Verifier as ViperVerifier;
use viper::ast_factory::AstFactory as ViperAstFactory;
use procedure_table::ProcedureTable;

struct VerifierBuilder {
    viper: Viper,
}

impl VerifierBuilder {
    pub fn new() -> Self {
        VerifierBuilder {
            viper: Viper::new()
        }
    }
}

impl VerifierBuilderSpec for VerifierBuilder {
    fn new_verifier(&mut self) -> Box<VerifierSpec> {
        let verification_ctx = self.viper.new_verification_context();
        Box::new(Verifier::new(verification_ctx))
    }
}

struct Verifier<'a> {
    verification_ctx: VerificationContext<'a>,
    verifier: ViperVerifier<'a, state::Started>,
    verifier_ast: ViperAstFactory,
    procedure_table: ProcedureTable,
    // fields_table: FieldsTable,
    // ...
}

impl Verifier {
    fn new(verification_ctx: VerificationContext) -> Self {
        let verifier = verification_ctx.new_verifier();
        let verifier_ast = verification_ctx.new_ast_factory();
        Verifier {
            verification_ctx,
            verifier,
            verifier_ast,
            procedure_table: ProcedureTable::new()
        }
    }
}

impl<'a> VerifierSpec for Verifier<'a> {
    fn verify(&mut self, env: &mut Environment, task: &VerificationTask) -> VerificationResult {
        let epoch = env.get_current_epoch();
        let verification_methods: Vec<Method> = vec![];
        let mut verification_errors: Vec<VerificationError> = vec![];
        /* TODO
        for proc_id in task.procedures {
            let method_or_result = self.procedure_table.get_use(procedure, epoch);
            match method_or_result {
                Left(method) => verification_methods.push(method),
                Right(errors) => verification_errors.append(errors)
            }
        }
        let verification_fields: Vec<Field> = fields_table.get_used_definitnions(epoch);
        let program = self.verifier_ast.program(&[], &verification_fields, &[], &[], &verification_methods);
        */
        let program = self.verifier_ast.program(&[], &[], &[], &[], &[]);
        let verification_result: ViperVerificationResult = self.verifier.verify(program);
        if let Failure(errors) = verification_result {
            verification_errors.append(errors)
        }
        for error in verification_errors {
            debug!("Verification error: {}", error);
            // TODO: emit error
        }
        if verification_errors.is_empty() {
            VerificationResult::Success
        } else {
            VerificationResult::Failure
        }
    }

    fn invalidate_all(&mut self, env: &mut Environment) {
        self.procedure_table = ProcedureTable::new()
    }
}
