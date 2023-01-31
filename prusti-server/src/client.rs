// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{VerificationRequest, ServerMessage};
use prusti_common::config;
use url::Url;
use tokio_tungstenite::{connect_async,
                        tungstenite::{Message, error::Error}};
use futures_util::{stream::{Stream, StreamExt}, sink::SinkExt};

pub struct PrustiClient;

impl PrustiClient {
    pub async fn verify<S: ToString>(
        server_address: S,
        request: VerificationRequest,
    ) -> impl Stream<Item = ServerMessage> {
        // TODO: do proper error handling
        let mut address = server_address.to_string();
        if !address.starts_with("ws") {
            address = format!("ws://{}", address);
        }
        let server_url = Url::parse(address.as_str()).unwrap();

        let use_json = config::json_communication();

        let uri = server_url
                .join(if use_json { "json/" } else { "bincode/" })
                .unwrap()
                .join("verify/")
                .unwrap();
        let (mut socket, _) = connect_async(uri).await.unwrap();
        let msg = if use_json { Message::text(serde_json::to_string(&request).expect("error encoding verification request in json")) }
                  else { Message::binary(bincode::serialize(&request).expect("error encoding verification request as binary")) };
        socket.send(msg).await.unwrap();
        let json_map = |ws_msg| {
            if let Message::Text(json) = ws_msg {
                serde_json::from_str(&json).expect("error decoding verification result from json")
            } else {
                panic!("Invalid response from the server.");
            }
        };
        let bin_map = |ws_msg| {
            if let Message::Binary(bytes) = ws_msg {
                bincode::deserialize(&bytes).expect("error decoding verification result")
            } else {
                panic!("Invalid response from the server.");
            }
        };
        let filter_close = |msg_result: Result<Message, Error>| async {
            let msg = msg_result.unwrap();
            match msg {
                Message::Close(_) => None,
                _ => Some(msg),
            }
        };
        let s = socket.filter_map(filter_close).map(if use_json { json_map } else { bin_map });
        s
    }
}
