// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use log::{error, info, warn};

use crate::verification_result::VerificationResult;
use rustc_hash::FxHashMap;
use std::{
    fs, io,
    ops::DerefMut,
    path::{Path, PathBuf},
    sync::{Arc, Mutex},
};

pub trait Cache {
    fn get(&self, request: u64) -> Option<VerificationResult>;
    fn insert(self, request: u64, result: VerificationResult) -> Option<VerificationResult>;
}
// We can change the representation here (e.g. adding fields):
#[derive(Debug, Clone)]
pub struct PersistentCache {
    updated: bool,
    load_loc: PathBuf,
    data: FxHashMap<u64, VerificationResult>,
}

const RESULT_CACHE_VERSION: u64 = 3;

#[derive(Debug, serde::Serialize, serde::Deserialize)]
struct ResultCache {
    data: FxHashMap<u64, VerificationResult>,
    version: u64,
}

impl From<(PathBuf, ResultCache)> for PersistentCache {
    /// Used when loading cache from disk
    fn from((load_loc, rc): (PathBuf, ResultCache)) -> Self {
        assert_eq!(rc.version, RESULT_CACHE_VERSION);
        let data = rc.data;
        PersistentCache {
            updated: false,
            load_loc,
            data,
        }
    }
}
impl From<&PersistentCache> for ResultCache {
    /// Used when saving cache to disk
    fn from(cache: &PersistentCache) -> Self {
        ResultCache {
            data: cache.data.clone(),
            version: RESULT_CACHE_VERSION,
        }
    }
}

impl PersistentCache {
    #[tracing::instrument(level = "debug")]
    pub fn load_cache(cache_loc: PathBuf) -> Self {
        let mut data_res: Option<ResultCache> = None;
        if !cache_loc.as_os_str().is_empty() {
            if let Ok(f) = fs::File::open(&cache_loc) {
                match bincode::deserialize_from::<_, ResultCache>(&mut io::BufReader::new(f)) {
                    Ok(data) => {
                        if data.version == RESULT_CACHE_VERSION {
                            info!("Loaded cache from \"{}\"", cache_loc.display());
                            data_res = Some(data);
                        } else {
                            error!(
                                "Cache version mismatch when reading from \"{}\": \
                                    expected={} actual={}",
                                cache_loc.display(),
                                RESULT_CACHE_VERSION,
                                data.version
                            )
                        }
                    }
                    Err(e) => error!("Failed to read cache from \"{}\": {e}", cache_loc.display()),
                }
            }
        }
        PersistentCache::from((
            cache_loc,
            data_res.unwrap_or_else(|| {
                info!("Cache file doesn't exist or is invalid. Using fresh cache.");
                ResultCache {
                    data: FxHashMap::default(),
                    version: RESULT_CACHE_VERSION,
                }
            }),
        ))
    }
    #[tracing::instrument(level = "debug")]
    pub fn save_cache(&self, cache_loc: &Path) {
        match fs::File::create(cache_loc) {
            Ok(f) => {
                info!("Saving cache to \"{}\"", cache_loc.display());
                bincode::serialize_into(&mut io::BufWriter::new(f), &ResultCache::from(self))
                    .unwrap_or_else(|e| error!("Failed to write cache: {e}"));
            }
            Err(e) => error!("Failed to create cache file: {e}"),
        }
    }
    pub fn save(&mut self) {
        // Save cache to disk, if changed and save path is valid
        if self.updated {
            if self.load_loc.as_os_str().is_empty() {
                warn!("Cannot save cache, because the cache path is empty.")
            } else {
                let mut save_dir = self.load_loc.clone();
                save_dir.pop();
                match fs::create_dir_all(&save_dir) {
                    Ok(()) => self.save_cache(&self.load_loc),
                    Err(e) => error!("Failed to create cache dir: {e}"),
                }
            }
        }
    }
}

impl Drop for PersistentCache {
    fn drop(&mut self) {
        self.save();
    }
}

impl Cache for &mut PersistentCache {
    fn get(&self, request: u64) -> Option<VerificationResult> {
        self.data.get(&request).cloned()
    }
    fn insert(self, request: u64, result: VerificationResult) -> Option<VerificationResult> {
        self.updated = true;
        self.data.insert(request, result)
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
