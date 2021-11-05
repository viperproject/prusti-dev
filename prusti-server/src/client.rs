// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::VerificationRequest;
use prusti_common::config;
use reqwest::Client;
use url::{ParseError, Url};
use viper::VerificationResult;

pub struct PrustiClient {
    client: Client,
    server_url: Url,
}

impl PrustiClient {
    pub fn new<S: ToString>(server_address: S) -> Result<Self, ParseError> {
        let mut address = server_address.to_string();
        if !address.starts_with("http") {
            address = format!("http://{}", address);
        }
        Ok(Self {
            client: Client::new(),
            server_url: Url::parse(address.as_str())?,
        })
    }

    pub async fn verify(
        &self,
        request: VerificationRequest,
    ) -> reqwest::Result<VerificationResult> {
        let use_json = config::json_communication();
        let base = self.client.post(
            self.server_url
                .join(if use_json { "json/" } else { "bincode/" })
                .unwrap()
                .join("verify/")
                .unwrap(),
        );
        let response = if use_json {
            base.json(&request)
                .send()
                .await?
                .error_for_status()?
                .json()
                .await?
        } else {
            let bytes = base
                .body(bincode::serialize(&request).expect("error encoding verification request"))
                .send()
                .await?
                .error_for_status()?
                .bytes()
                .await?;
            bincode::deserialize(&bytes).expect("error decoding verification result")
        };
        Ok(response)
    }
}
