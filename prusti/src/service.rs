use prusti_server::PrustiServer;
use prusti_viper::encoder::vir::Program;
use viper;

use std::sync::{mpsc, Arc};
use std::thread;
use tarpc::sync::client::ClientExt;
use tarpc::sync::{client, server};
use tarpc::util::Never;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ViperBackendConfig {
    Silicon(Vec<String>),
    Carbon(Vec<String>),
}

pub trait VerificationService {
    fn verify(&self, program: Program, config: ViperBackendConfig) -> viper::VerificationResult;
}

service! {
    rpc verify(program: Program, config: ViperBackendConfig) -> viper::VerificationResult;
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
    ) -> Result<viper::VerificationResult, Never> {
        Ok(self.server.verify(program, config))
    }
}

impl VerificationService for PrustiServer {
    fn verify(&self, program: Program, config: ViperBackendConfig) -> viper::VerificationResult {
        // TODO: handle args
        match config {
            ViperBackendConfig::Silicon(_args) => {
                self.run_verifier(program, viper::VerificationBackend::Silicon)
            }
            ViperBackendConfig::Carbon(_args) => {
                self.run_verifier(program, viper::VerificationBackend::Carbon)
            }
        }
    }
}

#[derive(Clone)]
pub struct PrustiServerConnection;

impl VerificationService for PrustiServerConnection {
    fn verify(&self, program: Program, config: ViperBackendConfig) -> viper::VerificationResult {
        // FIXME: actually implement--currently just starts a server off-thread and runs on that lol
        let (sender, receiver) = mpsc::channel();
        thread::spawn(move || {
            let handle = ServerSideService::new(PrustiServer::new())
                .listen("localhost:0", server::Options::default())
                .unwrap();
            sender.send(handle.addr()).unwrap();
            handle.run();
        });
        let client =
            SyncClient::connect(receiver.recv().unwrap(), client::Options::default()).unwrap();
        client.verify(program, config).unwrap()
    }
}
