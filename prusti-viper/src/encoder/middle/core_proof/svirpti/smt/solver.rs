use super::{configuration::Configuration, errors::SmtSolverResult, parser::SmtParser};
use rsmt2::Solver;

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
}

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
        let result = match self.solver.check_sat_or_unk()? {
            Some(true) => SatResult::Sat,
            Some(false) => SatResult::Unsat,
            None => SatResult::Unknown,
        };
        Ok(result)
    }
}
