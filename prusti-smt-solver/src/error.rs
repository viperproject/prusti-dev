#[derive(Debug)]
pub(crate) enum ErrorKind {
    ConsumeFailed,
    ParseIdFailed,
    EofCheckFailed,
}

pub(crate) struct Error {
    pub(crate) kind: ErrorKind,
    pub(crate) line: String,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} in {:?}", self.kind, self.line)
    }
}
