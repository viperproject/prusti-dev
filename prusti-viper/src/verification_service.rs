use viper;
use super::encoder::vir::Program;

pub trait VerificationService {
    fn verify(&self, program: Program, config: ViperBackendConfig) -> viper::VerificationResult;
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ViperBackendConfig {
    Silicon(Vec<String>),
    Carbon(Vec<String>),
}
