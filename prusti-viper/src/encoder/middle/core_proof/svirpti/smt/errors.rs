pub type SmtSolverResult<T = ()> = Result<T, SmtSolverError>;

#[derive(Debug)]
pub enum SmtSolverError {
    Rsmt2Error(rsmt2::errors::Error),
}

impl From<rsmt2::errors::Error> for SmtSolverError {
    fn from(e: rsmt2::errors::Error) -> Self {
        SmtSolverError::Rsmt2Error(e)
    }
}
