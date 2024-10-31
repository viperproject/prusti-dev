// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
#![feature(rustc_private)]

mod harnesses;

fn main() {
    env_logger::init_from_env(env_logger::Env::new().filter_or("PRUSTI_LOG", "warn"));
    harnesses::compiletest::run();
    harnesses::cargotest::run();
}
