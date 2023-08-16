// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_common::{config, vir::program::Program};
use rustc_hash::FxHasher;
use std::hash::{Hash, Hasher};
use viper::{self, VerificationBackend};

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize, Hash)]
pub struct VerificationRequest {
    pub program: Program,
    pub backend_config: ViperBackendConfig,
}

impl VerificationRequest {
    pub(crate) fn get_hash(&self) -> u64 {
        let mut hasher = FxHasher::default();
        self.hash(&mut hasher);
        hasher.finish()
    }
}

/// The configuration for the viper backend, (i.e. verifier).
/// Expresses which backend (silicon or carbon) should be used, and provides command-line arguments
/// to the viper verifier.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize, Eq, PartialEq, Hash)]
pub struct ViperBackendConfig {
    pub backend: VerificationBackend,
    pub verifier_args: Vec<String>,
}

impl ViperBackendConfig {
    pub fn new(backend: VerificationBackend) -> Self {
        let mut verifier_args = config::extra_verifier_args();
        match backend {
            VerificationBackend::Silicon => {
                // If we want to remove dead code, numberOfErrorsToReport has to
                // be set to 0 (so all reachable errors are reported!)
                let num_errors_per_function = if config::remove_dead_code() {
                    0
                } else {
                    config::num_errors_per_function()
                };
                verifier_args.push(format!(
                    "--numberOfErrorsToReport={}",
                    num_errors_per_function
                ));
                if config::use_more_complete_exhale() {
                    verifier_args.push("--enableMoreCompleteExhale".to_string());
                }
                if config::counterexample() {
                    verifier_args.push("--counterexample".to_string());
                    verifier_args.push("mapped".to_string());
                }
                if let Some(number) = config::number_of_parallel_verifiers() {
                    verifier_args.push("--numberOfParallelVerifiers".to_string());
                    verifier_args.push(number.to_string());
                }

                verifier_args.extend(vec![
                    "--assertTimeout".to_string(),
                    config::assert_timeout().to_string(),
                    "--proverConfigArgs".to_string(),
                    // model.partial changes the default case of functions in counterexamples
                    // to #unspecified
                    format!(
                        "smt.qi.eager_threshold={} model.partial={}",
                        config::smt_qi_eager_threshold(),
                        config::counterexample()
                    ),
                    "--logLevel".to_string(),
                    "ERROR".to_string(),
                ]);

                if let Some(check_timeout) = config::check_timeout() {
                    verifier_args.push("--checkTimeout".to_string());
                    verifier_args.push(check_timeout.to_string());
                }
            }
            VerificationBackend::Carbon => {
                verifier_args.extend(vec!["--disableAllocEncoding".to_string()]);
            }
        }
        Self {
            backend,
            verifier_args,
        }
    }
}
