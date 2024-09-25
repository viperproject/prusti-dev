#![feature(rustc_private)]
// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use clap::Parser;
use prusti_utils::config;

/// A verification server to handle Prusti verification requests.
#[derive(Parser, Debug)]
#[clap(version, about, long_about = None)]
struct Args {
    /// Sets the port on which to listen for incoming verification requests.
    /// Pass 0 to get a free one assigned by the OS.
    #[clap(short, long, value_name = "PORT", default_value_t = 0)]
    port: u16,
}

fn main() {
    env_logger::init_from_env(
        env_logger::Env::new()
            .filter_or("PRUSTI_LOG", config::log())
            .write_style_or("PRUSTI_LOG_STYLE", config::log_style()),
    );

    let args = Args::parse();

    prusti_server::start_server_on_port(args.port);
}
