// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use serde::{Deserialize, Serialize};
use std::{
    collections::HashMap,
    fs, io,
    ops::DerefMut,
    path::{Path, PathBuf},
    sync::{Arc, Mutex},
};
use verification_result::VerificationResult;

pub trait Cache {
    fn get(&self, request: u64) -> Option<VerificationResult>;
    fn insert(self, request: u64, result: VerificationResult) -> Option<VerificationResult>;
}
#[derive(Debug, Clone)]
pub struct PersistentCache {
    updated: bool,
    load_loc: PathBuf,
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

impl PersistentCache {
    pub fn load_cache(cache_loc: PathBuf) -> Self {
        info!("Loading cache from \"{}\"", cache_loc.display());
        let data_str = fs::read_to_string(&cache_loc).unwrap_or_default();
        let data_res = serde_json::from_str(&data_str);
        PersistentCache {
            updated: false,
            load_loc: cache_loc,
            data: match data_res {
                Ok(ResultCache::V1(data)) => data,
                // Ok(ResultCache::V2(???)) => ???,
                Err(_) => HashMap::new(),
            },
        }
    }
    pub fn save_cache(&self, cache_loc: &Path) -> io::Result<()> {
        info!("Saving cache to \"{}\"", cache_loc.display());
        // ResultCache::V2(...)
        match serde_json::to_string(&ResultCache::V1(self.data.clone())) {
            Ok(data) => fs::write(cache_loc, data),
            Err(e) => Err(io::Error::new(io::ErrorKind::Other, e)),
        }
    }
}
impl Drop for PersistentCache {
    fn drop(&mut self) {
        // Save cache to disk, if changed
        if self.updated {
            let mut save_dir = self.load_loc.clone();
            save_dir.pop();
            fs::create_dir_all(&save_dir).ok();
            self.save_cache(&self.load_loc).ok();
        }
    }
}

impl Cache for &mut PersistentCache {
    fn get(&self, request: u64) -> Option<VerificationResult> {
        self.data.get(&request.to_string()).cloned()
    }
    fn insert(self, request: u64, result: VerificationResult) -> Option<VerificationResult> {
        self.updated = true;
        self.data.insert(request.to_string(), result)
    }
}
impl Cache for &Arc<Mutex<PersistentCache>> {
    fn get(&self, request: u64) -> Option<VerificationResult> {
        let mut cache = self.lock().unwrap();
        cache.deref_mut().get(request)
    }
    fn insert(self, request: u64, result: VerificationResult) -> Option<VerificationResult> {
        let mut cache = self.lock().unwrap();
        cache.insert(request, result)
    }
}
