// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::VerificationRequestProcessing;
use futures_util::{pin_mut, SinkExt, StreamExt};
use log::info;
use once_cell::sync::Lazy;
use std::{
    net::{Ipv4Addr, SocketAddr},
    sync::mpsc,
    thread,
};
use tokio::runtime::Builder;
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

// This VerificationRequestProcessing object is starting the verification thread (for more details
// see the file process_verification.rs).
// It has to have a static lifetime because warp websockets need their closures to have a static
// lifetime and we need to access this object in them.
static VERIFICATION_REQUEST_PROCESSING: Lazy<VerificationRequestProcessing> =
    Lazy::new(VerificationRequestProcessing::new);

fn listen_on_port_with_address_callback<F>(port: u16, address_callback: F) -> !
where
    F: FnOnce(SocketAddr),
{
    let json_verify = warp::path!("json" / "verify")
        .and(warp::filters::ws::ws())
        .map(|ws: warp::filters::ws::Ws| {
            ws.on_upgrade(|mut websocket| async {
                let req_msg = websocket.next().await.unwrap().unwrap();
                let verification_request = req_msg
                    .to_str()
                    .and_then(|s: &str| serde_json::from_str(s).unwrap())
                    .unwrap();
                let stream = VERIFICATION_REQUEST_PROCESSING.verify(verification_request);
                pin_mut!(stream);
                while let Some(server_msg) = stream.next().await {
                    websocket
                        .send(warp::filters::ws::Message::text(
                            serde_json::to_string(&server_msg).unwrap(),
                        ))
                        .await
                        .unwrap();
                }
                websocket.close().await.unwrap();
            })
        });

    let bincode_verify = warp::path!("bincode" / "verify")
        .and(warp::filters::ws::ws())
        .map(|ws: warp::filters::ws::Ws| {
            ws.on_upgrade(|mut websocket| async {
                let req_msg = websocket.next().await.unwrap().unwrap();
                let verification_request = bincode::deserialize(req_msg.as_bytes()).unwrap();
                let stream = VERIFICATION_REQUEST_PROCESSING.verify(verification_request);
                pin_mut!(stream);
                while let Some(server_msg) = stream.next().await {
                    websocket
                        .send(warp::filters::ws::Message::binary(
                            bincode::serialize(&server_msg).unwrap(),
                        ))
                        .await
                        .unwrap();
                }
                websocket.close().await.unwrap();
            })
        });
    let save_cache = warp::post()
        .and(warp::path("save"))
        .and(warp::path::end())
        .map(move || {
            VERIFICATION_REQUEST_PROCESSING.save_cache();
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
