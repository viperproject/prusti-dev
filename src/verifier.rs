use prusti_interface::verifier::VerifierBuilder as VerifierBuilderSpec;
use prusti_interface::verifier::Verifier as VerifierSpec;
use prusti_interface::data::VerificationResult;
use prusti_interface::environment::Environment;
use prusti_interface::data::VerificationTask;
use viper::Viper;
use viper::Method;
use viper::VerificationError;
use viper::VerificationContext as VerificationContext;
use viper::VerificationResult as ViperVerificationResult;
use viper::Verifier as ViperVerifier;
use viper::state as verifier_state;
use viper::AstFactory as ViperAstFactory;
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

    fn new_verifier<'a>(&'a mut self) -> Verifier<'a> {
        let verification_ctx: VerificationContext<'a> = self.viper.new_verification_context();
        Verifier::new(verification_ctx)
    }
}

struct Verifier<'a> {
    verification_ctx: VerificationContext<'a>,
    verifier: Option<ViperVerifier<'a, verifier_state::Started>>,
    verifier_ast: Option<ViperAstFactory<'a>>,
    procedure_table: ProcedureTable,
    // fields_table: FieldsTable,
    // ...
}

impl<'a> Verifier<'a> {
    fn new(verification_ctx: VerificationContext<'a>) -> Self {
        Verifier {
            verification_ctx,
            verifier: None,
            verifier_ast: None,
            procedure_table: ProcedureTable::new()
        }
    }

    fn init(&'a mut self) {
        let verifier = self.verification_ctx.new_verifier();
        let verifier_ast = self.verification_ctx.new_ast_factory();
        self.verifier = Some(verifier);
        self.verifier_ast = Some(verifier_ast);
    }

    fn get_verifier(&'a self) -> &ViperVerifier<'a, verifier_state::Started> {
        if let Some(ref verifier) = self.verifier {
            verifier
        } else {
            panic!()
        }
    }

    fn get_verifier_ast(&'a self) -> &ViperAstFactory<'a> {
        if let Some(ref verifier_ast) = self.verifier_ast {
            verifier_ast
        } else {
            panic!()
        }
    }
}

impl<'a> VerifierSpec for Verifier<'a> {
    fn verify(&mut self, env: &mut Environment, task: &VerificationTask) -> VerificationResult {
        let verifier = self.get_verifier();
        let verifier_ast = self.get_verifier_ast();
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
        let program = verifier_ast.program(&[], &[], &[], &[], &[]);
        let verification_result: ViperVerificationResult = verifier.verify(program);
        if let ViperVerificationResult::Failure(mut errors) = verification_result {
            verification_errors.append(&mut errors)
        }

        if verification_errors.is_empty() {
            VerificationResult::Success
        } else {
            for error in verification_errors {
                debug!("Verification error: {:?}", error);
                // TODO: emit error
            }
            VerificationResult::Failure
        }
    }

    fn invalidate_all(&mut self, env: &mut Environment) {
        self.procedure_table = ProcedureTable::new()
    }
}
