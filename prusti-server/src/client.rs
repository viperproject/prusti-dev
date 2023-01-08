// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::VerificationRequest;
use prusti_common::config;
use url::{ParseError, Url};
use viper::VerificationResult;
use tokio_tungstenite::{client::connect_async,
                        tungstenite::{Message,
                                      handshake::client::Response,
                                      error::Error}
};
use async_stream::stream;
use futures_core::stream::Stream;
use futures_util::{FutureExt, stream::StreamExt, sink::SinkExt, pin_mut};

pub struct PrustiClient {
    server_url: Url,
}

impl PrustiClient {
    pub fn new<S: ToString>(server_address: S) -> Result<Self, ParseError> {
        let mut address = server_address.to_string();
        if !address.starts_with("ws") {
            address = format!("ws://{}", address);
        }
        Ok(Self {
            server_url: Url::parse(address.as_str())?,
        })
    }

    pub async fn verify(
        &self,
        request: VerificationRequest,
    ) -> Result<impl Stream<ServerMessage>, Error> {
        let use_json = config::json_communication();
        let uri = self.server_url
                .join(if use_json { "json/" } else { "bincode/" })
                .unwrap()
                .join("verify/")
                .unwrap();
        let (socket, _) = connect_async(uri).await?;
        let msg = if use_json Message::text(serde_json::to_string(request).expect("error encoding verification request in json"))
                  else Message::binary(bincode::serialize(&request).expect("error encoding verification request as binary"));
        pin_mut!(socket);
        socket.send(msg).await?;
        // TODO: do we have to care about close messages?
        let json_map = |ws_msg| {
            if let Message::Text(json) = ws_msg {
                serde_json::from_string(&json).expect("error decoding verification result from json")
            } else {
                panic!("Invalid response from the server.");
            }
        });
        let bin_map = |ws_msg| {
            if let Message::Binary(bytes) = ws_msg {
                bincode::deserialize(&bytes).expect("error decoding verification result")
            } else {
                panic!("Invalid response from the server.");
            }
        });
        let s = socket.map(if use_json json_map else bin_map);
        Ok(s)
    }
}
