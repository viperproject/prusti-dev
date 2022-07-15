// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_interface::environment::Environment;

pub fn dump_pcs<'tcx>(env: Environment<'tcx>) {
    for proc_id in env.get_annotated_procedures() {
        println!("id: {:#?}", env.get_unique_item_name(proc_id));
        let current_procedure = env.get_procedure(proc_id);
        let _mir = current_procedure.get_mir();

        // Q: Can we get the MIR?
        // let mir = env.local_mir(proc_id.expect_local(), env.identity_substs(proc_id));
        // println!("{:#?}", *mir);
        // Alternate:

        // Q: What about borrowck facts?
        // if let Some(facts) = env.try_get_local_mir_borrowck_facts(proc_id.expect_local()) {
        //     println!("{:#?}", (*facts).input_facts);
        // } else {
        //     println!("No borrowck facts");
        // }

        // Q: What kind of loop information can we get?
        // let loop_info = current_procedure.loop_info();
        // println!("\theads: {:#?}", loop_info.loop_heads);
        // println!("\thead depths: {:#?}", loop_info.loop_head_depths);

        // Q: MIR analyses?
    }
}
