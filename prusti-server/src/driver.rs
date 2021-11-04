// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use clap::{App, Arg};

fn main() {
    env_logger::init_from_env(env_logger::Env::new().filter_or("PRUSTI_LOG", "info"));

    let matches = App::new("Prusti Server")
        .arg(
            Arg::with_name("port")
                .short("p")
                .long("port")
                .help("Sets the port on which to listen for incoming verification requests. Pass 0 to get a free one assigned by the OS.")
                .required(true)
                .takes_value(true)
                .value_name("PORT"),
        )
        .get_matches();

    let port = matches
        .value_of("port")
        .unwrap()
        .parse()
        .expect("Invalid port provided");

    prusti_server::start_server_on_port(port);
}
