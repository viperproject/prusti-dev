// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{ServerMessage, VerificationRequest, VerificationRequestProcessing};
use futures_util::{pin_mut, SinkExt, StreamExt};
use log::info;
use once_cell::sync::Lazy;
use prusti_utils::config;
use std::{
    net::{Ipv4Addr, SocketAddr},
    sync::{self, mpsc, Arc},
    thread,
};
use tokio::runtime::Builder;
use viper::{Cache, PersistentCache, VerificationResultKind};
use warp::Filter;

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
// TODO: caching currently does not work properly. The subject of caching needs to be redetermined.
// currently, it is the whole program, and the returned result is the final errors (without
// per-method ones).
static CACHE: Lazy<Arc<sync::Mutex<PersistentCache>>> = Lazy::new(|| {
    Arc::new(sync::Mutex::new(PersistentCache::load_cache(
        config::cache_path(),
    )))
});

fn listen_on_port_with_address_callback<F>(port: u16, address_callback: F) -> !
where
    F: FnOnce(SocketAddr),
{
    fn init_vcx<T>(data: T) -> T {
        // initialise a new arena every time, so the data from previous
        // verification runs is deallocated
        vir::init_vcx(vir::VirCtxt::new_without_tcx());
        data
    }

    fn handle_json_websocket_message(msg: warp::ws::Message) -> VerificationRequest {
        msg.to_str()
            .and_then(|s: &str| serde_json::from_str(s).unwrap())
            .unwrap()
    }
    fn make_json_websocket_message(msg: &ServerMessage) -> warp::ws::Message {
        warp::filters::ws::Message::text(serde_json::to_string(&msg).unwrap())
    }

    fn handle_bincode_websocket_message(msg: warp::ws::Message) -> VerificationRequest {
        bincode::deserialize(msg.as_bytes()).unwrap()
    }
    fn make_bincode_websocket_message(msg: &ServerMessage) -> warp::ws::Message {
        warp::filters::ws::Message::binary(bincode::serialize(&msg).unwrap())
    }

    let json_verify = warp::path!("json" / "verify")
        .and(warp::filters::ws::ws())
        .map(init_vcx)
        .map(move |ws: warp::filters::ws::Ws| {
            on_upgrade(
                ws,
                handle_json_websocket_message,
                make_json_websocket_message,
            )
        });

    let bincode_verify = warp::path!("bincode" / "verify")
        .and(warp::filters::ws::ws())
        .map(init_vcx)
        .map(move |ws: warp::filters::ws::Ws| {
            on_upgrade(
                ws,
                handle_bincode_websocket_message,
                make_bincode_websocket_message,
            )
        });

    let save_cache = warp::post()
        .and(warp::path("save"))
        .and(warp::path::end())
        .map(move || {
            if let Some(cache) = Lazy::get(&CACHE) {
                cache.lock().unwrap().save();
                warp::reply::html("Saved")
            } else {
                warp::reply::html("Nothing to save")
            }
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
        info!("Prusti Server binding to port {port}");
        let (address, server_loop) =
            warp::serve(endpoints).bind_ephemeral((Ipv4Addr::LOCALHOST, port));

        println!("port: {}", address.port());
        address_callback(address);

        info!("Prusti Server listening on port {}", address.port());
        server_loop.await
    });

    unreachable!("The server unexpectedly stopped.");
}

fn on_upgrade<F, G>(
    ws: warp::ws::Ws,
    handle_websocket_message: F,
    make_websocket_message: G,
) -> impl warp::Reply
where
    F: Fn(warp::ws::Message) -> VerificationRequest + Send + Sync + 'static,
    G: Fn(&ServerMessage) -> warp::ws::Message + Send + Sync + 'static,
{
    ws.on_upgrade(move |websocket| async move {
        let (mut ws_send, mut ws_recv) = websocket.split();
        let req_msg = ws_recv.next().await.unwrap().unwrap();
        let verification_request = handle_websocket_message(req_msg);
        let request_hash = verification_request.get_hash();
        let program_name = verification_request.program.get_name().to_string();
        // return early in case of a cache hit
        let stream = if config::enable_cache() {
            match Lazy::force(&CACHE).get(request_hash) {
                Some(mut result) => {
                    info!(
                        "Using cached result {:?} for program {}",
                        &result, &program_name
                    );
                    result.cached = true;
                    futures::stream::once(async move { ServerMessage::Termination(result) })
                        .left_stream()
                }
                None => VERIFICATION_REQUEST_PROCESSING
                    .verify(verification_request)
                    .right_stream(),
            }
        } else {
            VERIFICATION_REQUEST_PROCESSING
                .verify(verification_request)
                .right_stream()
        };
        pin_mut!(stream);

        while let Some(server_msg) = stream.next().await {
            if let ServerMessage::Termination(result) = &server_msg {
                if config::enable_cache()
                    && !matches!(result.kind, VerificationResultKind::JavaException(_))
                    && !result.cached
                {
                    info!(
                        "Storing new cached result {:?} for program {}",
                        &result, &program_name
                    );
                    CACHE.insert(request_hash, result.clone());
                }
            };
            let msg = make_websocket_message(&server_msg);
            ws_send.send(msg).await.unwrap();
        }
        ws_send.close().await.unwrap();
    })
}
