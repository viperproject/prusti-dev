// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{process_verification_request, VerificationRequest};
use log::info;
use prusti_common::{config, Stopwatch};
use std::{
    net::{Ipv4Addr, SocketAddr},
    sync::{mpsc, Arc},
    thread,
};
use tokio::runtime::Builder;
use viper::Viper;
use warp::Filter;

#[derive(Debug)]
struct BincodeReject(bincode::Error);
impl warp::reject::Reject for BincodeReject {}

pub fn start_server_on_port(port: u16) {
    listen_on_port_with_address_callback(port, move |address| {
        if port == 0 {
            return;
        }
        assert_eq!(
            address.port(),
            port,
            "Server could not bind to port {}",
            port
        )
    });
}

pub fn spawn_server_thread() -> SocketAddr {
    let (sender, receiver) = mpsc::channel();
    thread::spawn(move || {
        listen_on_port_with_address_callback(
            0, // ask system for port
            move |address| sender.send(address).unwrap(),
        );
    });
    // Return the address received by the server thread.
    receiver.recv().unwrap()
}

fn listen_on_port_with_address_callback<F>(port: u16, address_callback: F) -> !
where
    F: FnOnce(SocketAddr),
{
    let stopwatch = Stopwatch::start("prusti-server", "JVM startup");
    let viper = Arc::new(Viper::new_with_args(config::extra_jvm_args()));
    stopwatch.finish();

    let build_verification_request_handler = |viper_arc: Arc<Viper>| {
        move |request: VerificationRequest| {
            // Here it would be easy to cache the result of verification requests, as soon as
            // `VerificationRequest` implements `Hash`.
            let stopwatch = Stopwatch::start("prusti-server", "attach thread to JVM");
            let viper_thread = viper_arc.attach_current_thread();
            stopwatch.finish();
            process_verification_request(&viper_thread, request)
        }
    };

    let json_verify = warp::path("json")
        .and(warp::path("verify"))
        .and(warp::path::end())
        .and(warp::body::json())
        .map(build_verification_request_handler(viper.clone()))
        .map(|response| warp::reply::json(&response));

    let bincode_verify = warp::path("bincode")
        .and(warp::path("verify"))
        .and(warp::path::end())
        .and(warp::body::bytes())
        .and_then(|buf: warp::hyper::body::Bytes| async move {
            bincode::deserialize(&buf).map_err(|err| {
                info!("request bincode body error: {}", err);
                warp::reject::custom(BincodeReject(err))
            })
        })
        .map(build_verification_request_handler(viper))
        .map(|result| {
            warp::http::Response::new(
                bincode::serialize(&result).expect("could not encode verification result"),
            )
        });

    let endpoints = json_verify.or(bincode_verify);

    // Here we use a single thread because
    // 1. Viper is not thread safe yet (Silicon issue #578), and
    // 2. By default Silicon already uses as many cores as possible.
    let mut runtime = Builder::new()
        .basic_scheduler()
        .thread_name("prusti-server")
        .enable_all()
        .build()
        .expect("failed to construct Tokio runtime");

    runtime.block_on(async {
        info!("Prusti Server binding to port {}", port);
        let (address, server_loop) =
            warp::serve(endpoints).bind_ephemeral((Ipv4Addr::LOCALHOST, port));

        println!("port: {}", address.port());
        address_callback(address);

        info!("Prusti Server listening on port {}", address.port());
        server_loop.await
    });

    unreachable!("The server unexpectedly stopped.");
}
