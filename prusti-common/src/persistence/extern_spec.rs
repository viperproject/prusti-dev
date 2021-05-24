// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/

use crate::config;
use std::{hash::Hash, io::{self, Write, Read, BufReader}};
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hasher};
use std::path::{Path, PathBuf};
use std::fs;
use serde::Serialize;
use serde_json;

fn extern_spec_dir() -> Option<PathBuf> {
    let spec_dir: PathBuf = config::extern_spec_dir().into();
    fs::create_dir_all(&spec_dir).ok()?;

    if spec_dir.is_dir() {
        Some(spec_dir)
    } else {
        None
    }
}

fn build_spec_writer(spec_name: &String) -> io::Result<Box<dyn Write>>{
    Ok(match extern_spec_dir() {
        Some(spec_dir) => {
            // hash the spec_name
            // let name_hash = calculate_hash(&spec_name);
            let path = Path::join(&spec_dir, Path::new(spec_name));
            box fs::File::create(path)?
        },

        _ => {
            panic!("cannot persist spec: {}", spec_name)
        }
    })
}

pub fn calculate_hash<T: Hash>(t: &T) -> u64 {
    let mut s = DefaultHasher::new();
    t.hash(&mut s);
    s.finish()
}

pub fn persist_spec<S: Serialize>(spec: &S, spec_name: &String) {
    let mut writer = build_spec_writer(spec_name).ok().unwrap();
    let spec_json = serde_json::to_string(&spec).unwrap();
    writer.write_all(spec_json.as_bytes())
          .map_err(|e| panic!("{}", e))
          .ok()
          .unwrap();
    writer.flush().map_err(|e| panic!("{}", e)).ok().unwrap();
}

pub fn persist_spec_tmp<S: Serialize>(spec: &S) {
    persist_spec(spec, &"tmp".to_string());
}

pub fn persist_spec_hash<S: Serialize + Hash>(spec: &S, spec_name: &String) {
    let spec_hash = calculate_hash(spec);
    persist_spec(&spec_hash, spec_name);
}

fn build_spec_reader(spec_name: &String) -> io::Result<Box<impl Read>> {
    let spec_dir = PathBuf::from(config::extern_spec_dir());
    let path = Path::join(&spec_dir, Path::new(&spec_name));
    Ok(box fs::File::open(path)?)
}

pub fn read_spec_hash(spec_name: &String) -> io::Result<String> {
    let name_hash = calculate_hash(spec_name).to_string();
    read_spec(&name_hash)
}

pub fn read_spec(spec_name: &String) -> io::Result<String> {
    let mut reader = BufReader::new(*build_spec_reader(spec_name)?);
    let mut buffer = String::new();
    reader.read_to_string(&mut buffer)?;

    let spec: String = serde_json::from_str(buffer.as_str()).unwrap();
    println!("string from json: {:?}\n\n", spec);
    Ok(spec)
}