// kept within prusti to be able to backtranslate errors etc
pub struct RequestWithContext {
    pub program: vir::ProgramRef,
    // TODO: flags for the verifier, backend config
    // TODO: mapping of positions to errors...?
}

// sent over the wire to a server or locally to a backend
pub struct Request {
    pub program: vir::ProgramRef,
    // TODO: other flags from RequestWithContext
}
