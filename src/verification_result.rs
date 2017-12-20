use span::MultiSpan;

#[derive(Debug)]
pub enum VerificationResult {
    Success(),
    Failure(Vec<VerificationError>),
}

#[derive(Debug)]
pub struct VerificationError {
    pos: MultiSpan,
    uuid: u64,
    message: String,
}
