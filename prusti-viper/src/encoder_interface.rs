// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_interface::PrustiError;
use prusti_interface::environment::Environment;
use prusti_interface::specs::typed::DefSpecificationMap;
use prusti_common::vir::program::Program;
use viper::VerificationError;
use prusti_interface::data::VerificationTask;
use crate::encoder;

/// A generic interface common to all encoders.
pub trait EncoderInterface<'env, 'tcx> {
    fn encode_verification_task(&mut self, task: &VerificationTask<'tcx>) -> Vec<Program>;
    fn count_encoding_errors(&self) -> usize;
    fn backtranslate_verification_error(&self, verification_error: &VerificationError, name: &str) -> PrustiError;
}

/// Build the appropriate encoder, depending on the configuration flags.
pub fn build_encoder<'env, 'tcx: 'env>(
    env: &'env Environment<'tcx>, def_spec: DefSpecificationMap
) -> Box<dyn EncoderInterface<'env, 'tcx> + 'env> {
    let encoder = encoder::Encoder::new(env, def_spec);
    Box::new(encoder)
}
