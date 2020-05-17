use prusti_viper::encoder::vir::Program;
use viper;

use std::sync::mpsc;
use std::thread;
use tarpc::sync::{client, server};
use tarpc::sync::client::ClientExt;
use tarpc::util::Never;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ViperBackendConfig {
    Silicon(Vec<String>),
    Carbon(Vec<String>),
}

pub trait VerificationService {
    fn verify(program: Program, config: ViperBackendConfig) -> viper::VerificationResult;
}

service! {
    rpc verify(program: Program, config: ViperBackendConfig) -> viper::VerificationResult;
}

#[derive(Clone)]
struct PrustiServer;

impl SyncService for PrustiServer {
    fn verify(&self, _program: Program, _config: ViperBackendConfig) -> Result<viper::VerificationResult, Never> {
        unimplemented!()
    }
}

fn _verify_remotely(program: Program, config: ViperBackendConfig) {
    // FIXME: actually implement — currently just copy-pasted the sync, mpsc example from the tarpc readme
    let (sender, receiver) = mpsc::channel();
    thread::spawn(move || {
        let handle = PrustiServer.listen("localhost:0", server::Options::default())
            .unwrap();
        sender.send(handle.addr()).unwrap();
        handle.run();
    });
    let client = SyncClient::connect(receiver.recv().unwrap(), client::Options::default()).unwrap();
    println!("{:#?}", client.verify(program, config).unwrap());
}
