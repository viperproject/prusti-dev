// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::Environment;
use super::borrowck::facts;
use super::loops;
use super::loops_utils::*;
use super::mir_analyses::initialization::{
    compute_definitely_initialized, DefinitelyInitializedAnalysisResult,
};
use super::polonius_info::PoloniusInfo;
use super::procedure::Procedure;
use crate::data::ProcedureDefId;
use rustc_hir as hir;
use rustc_middle::mir;
use rustc_middle::ty::{self, TyCtxt};
use rustc_index::vec::Idx;
use rustc_hash::FxHashMap;
use std::cell;
use std::collections::{BTreeMap, BTreeSet, HashSet, HashMap};
use std::env;
use std::fs::File;
use std::io::{self, BufWriter, Write};
use std::path::PathBuf;
use log::{trace, debug};
use prusti_common::config;
use crate::environment::mir_utils::RealEdges;

pub fn dump_borrowck_info(env: &Environment<'_>, procedures: &[ProcedureDefId]) {
    trace!("[dump_borrowck_info] enter");

    for def_id in procedures {
        crate::environment::mir_dump::dump_mir_info(env, *def_id);
    }

    trace!("[dump_borrowck_info] exit");
}
