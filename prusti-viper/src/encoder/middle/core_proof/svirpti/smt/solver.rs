use super::{
    super::super::transformations::{
        encoder_context::EncoderContext, symbolic_execution_new::ProgramContext,
    },
    configuration::Configuration,
    errors::SmtSolverResult,
    expressions::Expr2SmtWrap,
    parser::SmtParser,
};
use prusti_common::Stopwatch;
use rsmt2::{print::Sort2Smt, Solver};
use vir_crate::low::{self as vir_low};

#[derive(Debug, PartialEq, Eq)]
pub enum SatResult {
    Unsat,
    Unknown,
    Sat,
}

impl SatResult {
    pub fn is_sat(&self) -> bool {
        matches!(self, SatResult::Sat)
    }
    pub fn is_unsat(&self) -> bool {
        matches!(self, SatResult::Unsat)
    }
    pub fn is_sat_or_unknown(&self) -> bool {
        matches!(self, SatResult::Sat | SatResult::Unknown)
    }
}

pub struct Info<'a, 'c, EC: EncoderContext> {
    pub(in super::super) program_context: &'a ProgramContext<'c, EC>,
}

impl<'a, 'c, EC: EncoderContext> Clone for Info<'a, 'c, EC> {
    fn clone(&self) -> Self {
        Self {
            program_context: self.program_context,
        }
    }
}

impl<'a, 'c, EC: EncoderContext> Copy for Info<'a, 'c, EC> {}

pub struct SmtSolver {
    solver: Solver<SmtParser>,
}

impl SmtSolver {
    pub fn new(conf: Configuration) -> SmtSolverResult<Self> {
        let parser = SmtParser {};
        let mut solver = Solver::new(conf.smt_conf, parser)?;
        if let Some(tee_path) = conf.tee_path {
            solver.path_tee(tee_path).unwrap();
        }
        for attribute in &conf.attributes {
            solver.set_info(attribute)?;
        }
        for (option, value) in &conf.options {
            solver.set_option(option, value)?;
        }
        Ok(Self { solver })
    }
    /// We cannot use the `Default` trait because this is potentially failing
    /// operation.
    pub fn default() -> SmtSolverResult<Self> {
        Self::new(Default::default())
    }
    pub fn check_sat(&mut self) -> SmtSolverResult<SatResult> {
        let stopwatch = Stopwatch::start("svirpti", "check-sat");
        let result = match self.solver.check_sat_or_unk()? {
            Some(true) => SatResult::Sat,
            Some(false) => SatResult::Unsat,
            None => SatResult::Unknown,
        };
        let duration = stopwatch.finish();
        self.solver
            .comment(&format!("Check-sat duration: {:?}", duration))?;
        Ok(result)
    }
    pub fn push(&mut self) -> SmtSolverResult<()> {
        self.solver.push(1)?;
        Ok(())
    }
    pub fn pop(&mut self) -> SmtSolverResult<()> {
        self.solver.pop(1)?;
        Ok(())
    }
    pub fn declare_sort(&mut self, sort: &str) -> SmtSolverResult<()> {
        self.solver.declare_sort(sort, 0)?;
        Ok(())
    }
    pub fn declare_variable<Sort>(&mut self, name: &str, sort: Sort) -> SmtSolverResult<()>
    where
        Sort: Sort2Smt,
    {
        self.solver.declare_const(name, sort)?;
        Ok(())
    }
    pub fn declare_function<ParameterSorts, ResultSort>(
        &mut self,
        domain_name: &str,
        function_name: &str,
        parameter_types: ParameterSorts,
        result_type: ResultSort,
    ) -> SmtSolverResult<()>
    where
        ParameterSorts: IntoIterator,
        ParameterSorts::Item: Sort2Smt,
        ResultSort: Sort2Smt,
    {
        let full_function_name = format!("{domain_name}@{function_name}");
        self.solver
            .declare_fun(full_function_name, parameter_types, result_type)?;
        Ok(())
    }
    pub fn comment(&mut self, comment: &str) -> SmtSolverResult<()> {
        self.solver.comment(comment)?;
        Ok(())
    }
    pub fn assert<'a, 'c, EC: EncoderContext>(
        &mut self,
        assertion: &vir_low::Expression,
        info: Info<'a, 'c, EC>,
    ) -> SmtSolverResult<()> {
        self.solver.assert_with(assertion.wrap(), info)?;
        Ok(())
    }
}
