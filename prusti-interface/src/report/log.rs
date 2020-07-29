// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! This module defines functions for log messages, meant for developers

use prusti_common::config;
use std::fs;
use std::io::{self, Write};
use std::path::PathBuf;

fn log_dir() -> Option<PathBuf> {
    let log_dir: PathBuf = config::log_dir().into();
    fs::create_dir_all(&log_dir).ok()?;
    if log_dir.is_dir() {
        Some(log_dir)
    } else {
        None
    }
}

pub fn build_writer<S: ToString>(namespace: &str, name: S) -> io::Result<Box<dyn Write>> {
    Ok(match log_dir() {
        Some(log_dir) => {
            let mut path = log_dir.join(namespace);
            fs::create_dir_all(&path)?;
            let name_path = PathBuf::from(name.to_string());
            debug_assert!(!name_path.is_absolute(), "The name cannot be absolute");
            path.push(name_path);
            Box::new(fs::File::create(path)?)
        }
        // fallback
        None => {
            let mut stdout = io::stdout();
            write!(&mut stdout, "# {}: {}\n\n", namespace, name.to_string())?;
            Box::new(stdout)
        }
    })
}

pub fn report<S1: ToString, S2: ToString>(namespace: &str, name: S1, data: S2) {
    let mut writer = build_writer(namespace, name)
        .map_err(|e| panic!("{}", e))
        .ok()
        .unwrap();
    writer
        .write_all(data.to_string().as_bytes())
        .map_err(|e| panic!("{}", e))
        .ok()
        .unwrap();
    writer.flush().map_err(|e| panic!("{}", e)).ok().unwrap();
}

pub fn report_with_writer<S: ToString, F: FnOnce(&mut Box<Write>)>(
    namespace: &str,
    name: S,
    func: F,
) {
    let mut writer = build_writer(namespace, name)
        .map_err(|e| panic!("{}", e))
        .ok()
        .unwrap();
    func(&mut writer);
    writer.flush().map_err(|e| panic!("{}", e)).ok().unwrap();
}
