// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{ServerMessage, ServerRequest, VerificationRequest};
use futures::{lock, stream::Stream};
use log::{debug, info};
use std::{
    sync::{self, mpsc},
    thread,
};

struct ThreadJoin {
    handle: Option<thread::JoinHandle<()>>,
}

// we join the thread after dropping the sender for the ServerRequests, so
// that the verification thread actually terminates
impl Drop for ThreadJoin {
    fn drop(&mut self) {
        self.handle.take().unwrap().join().unwrap();
    }
}

pub struct VerificationRequestProcessing {
    mtx_rx_servermsg: lock::Mutex<mpsc::Receiver<ServerMessage>>,
    mtx_tx_verreq: sync::Mutex<mpsc::Sender<ServerRequest>>,
    // mtx_tx_verreq has to be dropped before thread_join
    #[allow(dead_code)]
    thread_join: ThreadJoin,
}

impl Default for VerificationRequestProcessing {
    fn default() -> Self {
        Self::new()
    }
}

/// A structure that lives for all the requests and has a single thread working on all the
/// requests sequentially.
/// On reception of a verification request, we send it through a channel to the already running
/// thread.
impl VerificationRequestProcessing {
    pub fn new() -> Self {
        let (tx_servermsg, rx_servermsg) = mpsc::channel();
        let (tx_verreq, rx_verreq) = mpsc::channel();
        let mtx_rx_servermsg = lock::Mutex::new(rx_servermsg);
        let mtx_tx_verreq = sync::Mutex::new(tx_verreq);

        let handle = thread::spawn(move || verification_thread(rx_verreq, tx_servermsg));
        Self {
            mtx_rx_servermsg,
            mtx_tx_verreq,
            thread_join: ThreadJoin {
                handle: Some(handle),
            },
        }
    }

    pub fn verify(&self, request: VerificationRequest) -> impl Stream<Item = ServerMessage> + '_ {
        let hash = request.get_hash();
        info!(
            "Verification request hash: {} - for program {}",
            hash,
            request.program.get_name(),
        );

        request.send(&self.mtx_tx_verreq);

        futures::stream::unfold(false, move |done: bool| async move {
            if done {
                return None;
            }
            let msg = self.mtx_rx_servermsg.lock().await.recv().unwrap();
            let mut done = false;
            if let ServerMessage::Termination(_) = msg {
                done = true;
            }
            Some((msg, done))
        })
    }
}

fn verification_thread(
    rx_verreq: mpsc::Receiver<ServerRequest>,
    tx_servermsg: mpsc::Sender<ServerMessage>,
) {
    debug!("Verification thread started.");

    while let Ok(request) = rx_verreq.recv() {
        match request {
            ServerRequest::Verification(verification_request) => {
                verification_request.process(&tx_servermsg)
            }
        }
    }
    debug!("Verification thread finished.");
}
