// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![feature(rustc_private)]
#![feature(box_syntax, box_patterns)]
#![feature(drain_filter, hash_drain_filter)]
#![feature(type_alias_impl_trait)]

#[macro_use]
extern crate tracing;

mod check;
mod defs;
mod repack;
mod free_pcs;
mod utils;

pub use defs::*;
pub use free_pcs::*;
pub use repack::*;
pub use utils::place::*;

use prusti_rustc_interface::dataflow::Analysis;
use prusti_interface::environment::Environment;

pub fn test_free_pcs(env: &Environment) {
    for proc_id in env.get_annotated_procedures_and_types().0.iter() {
        let name = env.name.get_unique_item_name(*proc_id);
        // if name != "syn::ty::parsing::ambig_ty" {
        //     continue;
        // }
        println!("id: {name}");
        let current_procedure = env.get_procedure(*proc_id);
        let mir = current_procedure.get_mir_rc();
        let fpcs = free_pcs::engine::FreePlaceCapabilitySummary::new(env.tcx(), &*mir);
        let analysis = fpcs.into_engine(env.tcx(), &*mir).pass_name("free_pcs").iterate_to_fixpoint();
        // let _ = MicroBody::new(mir, env.tcx());
    }
}
