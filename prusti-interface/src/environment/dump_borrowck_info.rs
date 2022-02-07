// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::Environment;






use crate::data::ProcedureDefId;











use log::{trace};



pub fn dump_borrowck_info(env: &Environment<'_>, procedures: &[ProcedureDefId]) {
    trace!("[dump_borrowck_info] enter");

    for def_id in procedures {
        crate::environment::mir_dump::dump_mir_info(env, *def_id);
    }

    trace!("[dump_borrowck_info] exit");
}
