// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use serde::{Deserialize, Serialize};
use silicon_counterexample::SiliconCounterexample;
use std::{
    collections::HashMap,
    fs, io,
    ops::DerefMut,
    path::PathBuf,
    sync::{Arc, Mutex},
};
use JavaException;

/// The result of a verification request on a Viper program.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum VerificationResult {
    /// The program verified.
    Success,
    /// The program did not verify.
    Failure(Vec<VerificationError>),
    /// The program has consistency errors.
    ConsistencyErrors(Vec<String>),
    /// The verification raised a Java exception.
    JavaException(JavaException),
}

impl VerificationResult {
    pub fn is_success(&self) -> bool {
        matches!(self, Self::Success)
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct VerificationError {
    pub full_id: String,
    pub pos_id: Option<String>,
    pub reason_pos_id: Option<String>,
    pub message: String,
    pub counterexample: Option<SiliconCounterexample>,
}

impl VerificationError {
    pub fn new(
        full_id: String,
        pos_id: Option<String>,
        reason_pos_id: Option<String>,
        message: String,
        counterexample: Option<SiliconCounterexample>,
    ) -> Self {
        VerificationError {
            full_id,
            pos_id,
            reason_pos_id,
            message,
            counterexample,
        }
    }
}

/// The consistency error reported by the verifier.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConsistencyError {
    /// To which method corresponds the program that triggered the error.
    pub method: String,
    /// The actual error.
    pub error: String,
}

/// The Java exception reported by the verifier.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct JavaExceptionWithOrigin {
    /// To which method corresponds the program that triggered the exception.
    pub method: String,
    /// The actual exception.
    pub exception: JavaException,
}

pub trait Cache {
    fn get(&self, request: u64) -> Option<VerificationResult>;
    fn insert(self, request: u64, result: VerificationResult) -> Option<VerificationResult>;
}
#[derive(Debug, Clone)]
pub struct CacheData {
    updated: bool,
    load_loc: String,
    // `serde_json` requires that the keys are strings
    // Could switch to binary serialization if performance
    // is an issue
    data: HashMap<String, VerificationResult>,
}

#[derive(Debug, Serialize, Deserialize)]
// Could also be: #[serde(untagged)]
#[serde(tag = "cache_version")]
enum ResultCache {
    #[serde(rename = "1.0")]
    V1(HashMap<String, VerificationResult>),
    // To change the representation, use:
    // #[serde(rename = "2.0")]
    // V2(???),
}

impl CacheData {
    pub fn load_cache(cache_loc: &str) -> Self {
        let data_str = fs::read_to_string(cache_loc).unwrap_or(String::new());
        let data_res = serde_json::from_str(&data_str);
        CacheData {
            updated: false,
            load_loc: cache_loc.to_owned(),
            data: match data_res {
                Ok(ResultCache::V1(data)) => data,
                // Ok(ResultCache::V2(???)) => ???,
                Err(_) => HashMap::new(),
            },
        }
    }
    pub fn save_cache(&self, cache_loc: &str) -> io::Result<()> {
        // ResultCache::V2(...)
        match serde_json::to_string(&ResultCache::V1(self.data.clone())) {
            Ok(data) => fs::write(cache_loc, data),
            Err(e) => Err(io::Error::new(io::ErrorKind::Other, e)),
        }
    }
}
impl Drop for CacheData {
    fn drop(&mut self) {
        // Save cache to disk, if changed
        if self.updated {
            let mut save_dir = PathBuf::from(&self.load_loc);
            save_dir.pop();
            fs::create_dir_all(&save_dir).ok();
            self.save_cache(&self.load_loc).ok();
        }
    }
}

impl Cache for &mut CacheData {
    fn get(&self, request: u64) -> Option<VerificationResult> {
        self.data.get(&request.to_string()).cloned()
    }
    fn insert(self, request: u64, result: VerificationResult) -> Option<VerificationResult> {
        self.updated = true;
        self.data.insert(request.to_string(), result)
    }
}
impl Cache for &Arc<Mutex<CacheData>> {
    fn get(&self, request: u64) -> Option<VerificationResult> {
        let mut cache = self.lock().unwrap();
        cache.deref_mut().get(request)
    }
    fn insert(self, request: u64, result: VerificationResult) -> Option<VerificationResult> {
        let mut cache = self.lock().unwrap();
        cache.insert(request, result)
    }
}
