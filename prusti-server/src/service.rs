// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::PrustiServer;
use prusti_common::verification_service::*;

use futures::{self, Future};
use reqwest::{self, Client, Url, UrlError};
use std::{
    net::{Ipv4Addr, SocketAddr},
    sync::{mpsc, Arc},
    thread,
};
use tokio;
use viper::VerificationResult;
use warp::{self, Filter};

#[derive(Clone)]
pub struct ServerSideService {
    server: Arc<PrustiServer>,
}

impl ServerSideService {
    pub fn new(server: PrustiServer) -> Self {
        Self {
            server: Arc::new(server),
        }
    }

    pub fn spawn_off_thread() -> SocketAddr {
        let (sender, receiver) = mpsc::channel();
        thread::spawn(move || {
            ServerSideService::new(PrustiServer::new()).listen_on_ephemeral_port(
                0, // ask system for port
                |address| sender.send(address).unwrap(),
            );
        });
        receiver.recv().unwrap()
    }

    pub fn listen_on_port(self, port: u16) {
        self.listen_on_ephemeral_port(port, |address| {
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

    fn listen_on_ephemeral_port<F>(self, port: u16, address_callback: F)
    where
        F: FnOnce(SocketAddr),
    {
        let clone = self.clone();
        let json_verify = warp::path("json")
            .and(warp::path("verify"))
            .and(warp::path::end())
            .and(warp::body::json())
            .map(move |request: VerificationRequest| clone.verify(request))
            .map(|response| warp::reply::json(&response));
        // TODO: bincode endpoint

        info!("Prusti Server binding to port {}", port);
        let (address, server_handle) =
            warp::serve(json_verify).bind_ephemeral((Ipv4Addr::localhost(), port));
        address_callback(address);

        info!("Prusti Server starting on port {}", address.port());
        tokio::run(futures::lazy(move || {
            warp::spawn(server_handle);
            info!("Prusti Server launched!");
            println!("port: {}", address.port()); // stdout, for use in other applications
            Ok(())
        }));
    }

    fn verify(&self, request: VerificationRequest) -> VerificationResult {
        info!("Handling verification request for {}", request.program_name);
        self.server
            .run_verifier_async(request)
            .wait()
            .expect("verification task canceled—this should not be possible!")
    }
}

pub struct PrustiServerConnection {
    client: Client,
    server_url: Url,
}

impl PrustiServerConnection {
    pub fn new<S: ToString>(server_address: S) -> Result<Self, UrlError> {
        let mut address = server_address.to_string();
        if !address.starts_with("http") {
            address = format!("http://{}", address);
        }
        Ok(Self {
            client: Client::builder().timeout(None).build().unwrap(),
            server_url: Url::parse(address.as_str())?,
        })
    }

    pub fn verify_checked(
        &self,
        request: VerificationRequest,
    ) -> reqwest::Result<VerificationResult> {
        Ok(self
            .client
            .post(self.server_url.join("json/verify").unwrap())
            .json(&request)
            .send()?
            .error_for_status()?
            .json()?)
    }
}

impl VerificationService for PrustiServerConnection {
    /// panics if the verification request fails
    fn verify(&self, request: VerificationRequest) -> VerificationResult {
        self.verify_checked(request)
            .expect("Verification request to server failed!")
    }
}
