// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::fs;
use std::io::{self, Write};
use std::path::PathBuf;
use config;

pub struct Log;

impl Log {
    fn log_dir() -> Option<PathBuf> {
        let log_dir: PathBuf = config::log_dir().into();
        fs::create_dir_all(&log_dir).ok()?;
        if log_dir.is_dir() {
            Some(log_dir)
        } else {
            None
        }
    }

    pub fn writer<S: ToString>(namespace: &str, name: S) -> io::Result<Box<Write>> {
        Ok(match Self::log_dir() {
            Some(log_dir) => {
                let mut path = log_dir.join(namespace);
                fs::create_dir_all(&path)?;
                path.push(&name.to_string());
                Box::new(fs::File::create(path)?)
            },
            None => {
                let mut stdout = io::stdout();
                write!(&mut stdout, "# {}: {}\n\n", namespace, name.to_string())?;
                Box::new(stdout)
            }
        })
    }

    pub fn report<S1: ToString, S2: ToString>(namespace: &str, name: S1, data: S2) {
        let mut writer = Self::writer(namespace, name).ok().unwrap();
        writer.write_all(data.to_string().as_bytes()).ok().unwrap();
        writer.flush().ok().unwrap();
    }

    pub fn report_with_writer<S: ToString, F: FnOnce(&mut Box<Write>)>(namespace: &str, name: S, func: F) {
        let mut writer = Self::writer(namespace, name).ok().unwrap();
        func(&mut writer);
        writer.flush().ok().unwrap();
    }
}
