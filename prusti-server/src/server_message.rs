// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use viper::{VerificationResult, VerificationResultKind};

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
/// A message from a Prusti server to a Prusti client. It may contain a result
/// of a verification or anything a server might send to a client.
pub enum ServerMessage {
    /// Contains the result of a verification and signals that this verification
    /// has terminated.
    Termination(VerificationResult),

    /// Signals the termination of the verification of a method. Contains the result.
    MethodTermination {
        viper_method_name: String,
        result: VerificationResultKind,
        verification_time: u128,
    },

    /// A message created by the Viper backend with Z3 about
    /// the number of instantiations of the named quantifier.
    QuantifierInstantiation {
        q_name: String,
        insts: u64,
        pos_id: usize,
    },

    /// Also created by the Viper backend. The viper_quant is the expression the
    /// quantifier was translated to in silver syntax while the triggers are the
    /// triggers provided or automatically derived for this quantifier.
    QuantifierChosenTriggers {
        viper_quant: String,
        triggers: String,
        pos_id: usize,
    },

    /// Contains a path id, label and viper method name corresponding to a symbolic
    /// execution path through the program being verified, the VIR label of the cfg
    /// basic block in the program and name of the method in the generated viper file
    BlockReached {
        viper_method: String,
        vir_label: String,
        path_id: i32,
    },

    /// Contains a path id, label and viper method name corresponding to a symbolic
    /// execution path through the program being verified, the VIR label of the cfg
    /// basic block in the program and name of the method in the generated viper file
    BlockFailure {
        viper_method: String,
        vir_label: String,
        path_id: i32,
    },

    /// Contains a path id, viper method name and a result corresponding to a
    /// symbolic execution path through the program being verified,
    /// and the tentative verification result of the last explored block.
    PathProcessed {
        viper_method: String,
        path_id: i32,
        result: String,
    },
}
