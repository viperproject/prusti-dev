// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use viper::VerificationResult;

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
/// A message from a Prusti server to a Prusti client. It may contain a result
/// of a verification or anything a server might send to a client.
pub enum ServerMessage {
    /// Contains the result of a verification and signals that this verification
    /// has terminated.
    Termination(VerificationResult),

    /// A message created by the Viper backend with Z3 about
    /// the number of instantiations of the named quantifier.
    QuantifierInstantiation {
        q_name: String,
        insts: u64,
        pos_id: u64,
    },

    /// Also created by the Viper backend. The viper_quant is the expression the
    /// quantifier was translated to in silver syntax while the triggers are the
    /// triggers provided or automatically derived for this quantifier.
    QuantifierChosenTriggers {
        viper_quant: String,
        triggers: String,
        pos_id: u64,
    },
}
