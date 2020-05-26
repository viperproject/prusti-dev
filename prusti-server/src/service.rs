use super::PrustiServer;
use prusti_viper::{encoder::vir::Program, verification_service::*};

use std::net::SocketAddr;
use std::sync::{mpsc, Arc};
use std::thread;
use tarpc::sync::client::ClientExt;
use tarpc::sync::{client, server};
use tarpc::util::Never;
use viper::{VerificationBackend, VerificationResult};

service! {
    rpc verify(program: Program, config: ViperBackendConfig) -> VerificationResult;
}

#[derive(Clone)]
pub struct ServerSideService {
    server: Arc<PrustiServer>,
}

impl ServerSideService {
    fn new(server: PrustiServer) -> Self {
        Self {
            server: Arc::new(server),
        }
    }
}

impl SyncService for ServerSideService {
    fn verify(
        &self,
        program: Program,
        config: ViperBackendConfig,
    ) -> Result<VerificationResult, Never> {
        Ok(self.server.verify(program, config))
    }
}

impl VerificationService for PrustiServer {
    fn verify(&self, program: Program, config: ViperBackendConfig) -> VerificationResult {
        // TODO: handle args
        match config {
            ViperBackendConfig::Silicon(_args) => {
                self.run_verifier_sync(program, VerificationBackend::Silicon)
            }
            ViperBackendConfig::Carbon(_args) => {
                self.run_verifier_sync(program, VerificationBackend::Carbon)
            }
        }
    }
}

pub struct PrustiServerConnection {
    client: SyncClient,
}

impl PrustiServerConnection {
    pub fn new_from_string(server_address: String) -> Self {
        Self::new(server_address.parse().unwrap())
    }

    pub fn new(server_address: SocketAddr) -> Self {
        let client = SyncClient::connect(server_address, client::Options::default()).unwrap();
        Self { client }
    }

    pub fn new_fake() -> Self {
        let (sender, receiver) = mpsc::channel();
        thread::spawn(move || {
            let handle = ServerSideService::new(PrustiServer::new())
                .listen("localhost:0", server::Options::default())
                .unwrap();
            sender.send(handle.addr()).unwrap();
            handle.run();
        });
        Self::new(receiver.recv().unwrap())
    }
}

impl VerificationService for PrustiServerConnection {
    fn verify(&self, program: Program, config: ViperBackendConfig) -> VerificationResult {
        self.client.verify(program, config).unwrap()
    }
}
