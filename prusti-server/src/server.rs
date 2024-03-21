// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{process_verification_request, VerificationRequest};
use log::info;
use once_cell::sync::Lazy;
use prusti_utils::{config, Stopwatch};
use std::{
    net::{Ipv4Addr, SocketAddr},
    sync::{mpsc, Arc, Mutex},
    thread,
};
use tokio::runtime::Builder;
use viper::{PersistentCache, Viper};
use warp::Filter;

#[derive(Debug)]
struct BincodeReject(bincode::Error);
impl warp::reject::Reject for BincodeReject {}

pub fn start_server_on_port(port: u16) {
    listen_on_port_with_address_callback(port, move |address| {
        if port == 0 {
            return;
        }
        assert_eq!(address.port(), port, "Server could not bind to port {port}")
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
    let viper = Arc::new(Lazy::new(|| {
        Viper::new_with_args(&config::viper_home(), config::extra_jvm_args())
    }));

    stopwatch.finish();

    let cache_data = PersistentCache::load_cache(config::cache_path());
    let cache = Arc::new(Mutex::new(cache_data));
    fn init_vcx<T>(data: T) -> T {
        // initialise a new arena every time, so the data from previous
        // verification runs is deallocated
        vir::init_vcx(vir::VirCtxt::new_without_tcx());
        data
    }
    let build_verification_request_handler = |viper_arc: Arc<Lazy<Viper, _>>, cache| {
        move |request: VerificationRequest| {
            let stopwatch = Stopwatch::start("prusti-server", "attach thread to JVM");
            let viper_thread = Lazy::new(|| viper_arc.attach_current_thread());
            stopwatch.finish();
            process_verification_request(&viper_thread, request, &cache)
        }
    };

    let json_verify = warp::path!("json" / "verify")
        .and(warp::body::json())
        .map(init_vcx)
        .map(build_verification_request_handler(
            viper.clone(),
            cache.clone(),
        ))
        .map(|response| warp::reply::json(&response));

    let bincode_verify = warp::path!("bincode" / "verify")
        .and(warp::body::bytes())
        .map(init_vcx)
        .and_then(|buf: warp::hyper::body::Bytes| async move {
            bincode::deserialize(&buf).map_err(|err| {
                info!("request bincode body error: {}", err);
                warp::reject::custom(BincodeReject(err))
            })
        })
        .map(build_verification_request_handler(viper, cache.clone()))
        .map(|result| {
            warp::http::Response::new(
                bincode::serialize(&result).expect("could not encode verification result"),
            )
        });

    let save_cache = warp::post()
        .and(warp::path("save"))
        .and(warp::path::end())
        .map(move || {
            cache.lock().unwrap().save();
            warp::reply::html("Saved")
        });

    let endpoints = json_verify.or(bincode_verify).or(save_cache);

    // Here we use a single thread because
    // 1. Viper is not thread safe yet (Silicon issue #578), and
    // 2. By default Silicon already uses as many cores as possible.
    let runtime = Builder::new_current_thread()
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
