use config;
use viper::{self, VerificationBackend};
use vir::Program;

pub trait VerificationService {
    fn verify(&self, request: VerificationRequest) -> viper::VerificationResult;
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerificationRequest {
    pub program: Program,
    pub program_name: String,
    pub backend_config: ViperBackendConfig,
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
        let mut verifier_args = config::extra_verifier_args();
        match backend {
            VerificationBackend::Silicon => {
                //if config::use_more_complete_exhale() {
                    //verifier_args.push("--enableMoreCompleteExhale".to_string());
                //}
                verifier_args.push("--stateConsolidationMode".to_string());
                //verifier_args.push("0".to_string()); – most tests fails with permission errors
                verifier_args.push("1".to_string());
                verifier_args.extend(vec![
                    "--assertTimeout".to_string(),
                    config::assert_timeout().to_string(),
                    "--logLevel".to_string(),
                    "ERROR".to_string(),
                ]);
            }
            VerificationBackend::Carbon => {
                verifier_args.extend(vec![
                    "--disableAllocEncoding".to_string(),
                ]);
            }
        }
        Self {
            backend,
            verifier_args,
        }
    }
}
