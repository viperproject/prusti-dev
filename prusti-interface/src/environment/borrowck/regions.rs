// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

/// Code for finding `rustc::ty::sty::RegionVid` associated with local
/// reference typed variables.
use crate::environment::borrowck::facts;
use regex::Regex;
use rustc_middle::mir;
// use rustc_data_structures::indexed_vec::Idx;
use rustc_index::vec::Idx;
use std::collections::HashMap;
use std::fs::File;
use std::io::{self, BufRead};
use std::path::Path;
use log::{trace, debug};

pub fn load_variable_regions(path: &Path) -> io::Result<HashMap<mir::Local, facts::Region>> {
    trace!("[enter] load_variable_regions(path={:?})", path);
    let mut variable_regions = HashMap::new();
    let file = File::open(path)?;
    lazy_static! {
        static ref FN_SIG: Regex =
            Regex::new(r"^fn [a-zA-Z\d_]+\((?P<args>.*)\) -> (?P<result>.*)\{$").unwrap();
    }
    lazy_static! {
        static ref ARG: Regex =
            Regex::new(r"^_(?P<local>\d+): &'_#(?P<rvid>\d+)r (mut)? [a-zA-Z\d_]+\s*$").unwrap();
    }
    lazy_static! {
        static ref LOCAL: Regex =
            Regex::new(r"^\s+let( mut)? _(?P<local>\d+): &'_#(?P<rvid>\d+)r ").unwrap();
    }
    for line in io::BufReader::new(file).lines() {
        let line = line?;
        if let Some(caps) = FN_SIG.captures(&line) {
            debug!("args: {} result: {}", &caps["args"], &caps["result"]);
            for arg_str in (&caps["args"]).split(", ") {
                if let Some(arg_caps) = ARG.captures(arg_str) {
                    debug!("arg {} rvid {}", &arg_caps["local"], &arg_caps["rvid"]);
                    let local_arg: usize = (&arg_caps["local"]).parse().unwrap();
                    let rvid: usize = (&arg_caps["rvid"]).parse().unwrap();
                    variable_regions.insert(mir::Local::new(local_arg), rvid.into());
                }
            }
        }
        if let Some(local_caps) = LOCAL.captures(&line) {
            debug!(
                "local {} rvid {}",
                &local_caps["local"], &local_caps["rvid"]
            );
            let local_arg: usize = (&local_caps["local"]).parse().unwrap();
            let rvid: usize = (&local_caps["rvid"]).parse().unwrap();
            variable_regions.insert(mir::Local::new(local_arg), rvid.into());
        }
    }
    trace!("[exit] load_variable_regions");
    Ok(variable_regions)
}
