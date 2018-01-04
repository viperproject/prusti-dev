#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VerificationResult {
    Success(),
    Failure(Vec<VerificationError>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerificationError {
    error_type: String,
    pos_id: String,
}

impl VerificationError {
    pub fn new(error_type: String, pos_id: String) -> Self {
        VerificationError { error_type, pos_id }
    }
}
