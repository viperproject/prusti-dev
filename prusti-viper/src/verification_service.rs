use super::encoder::vir::Program;
use prusti_common::config;
use viper;
use viper::VerificationBackend;

pub trait VerificationService {
    fn verify(&self, program: Program, config: ViperBackendConfig) -> viper::VerificationResult;
}

/**
The configuration for the viper backend, (i.e. verifier).
Expresses which backend (silicon or carbon) should be used, and provides command-line arguments to the viper verifier.
*/
#[derive(Debug, Clone, Serialize, Deserialize, Eq, PartialEq, Hash)]
pub struct ViperBackendConfig {
    pub backend: VerificationBackend,
    pub verifier_args: Vec<String>,
}

impl Default for ViperBackendConfig {
    fn default() -> Self {
        let backend = VerificationBackend::from_str(&config::viper_backend());
        Self {
            backend,
            verifier_args: config::extra_verifier_args(),
        }
    }
}
