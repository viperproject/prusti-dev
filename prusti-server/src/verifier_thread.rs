use futures::Canceled;
use futures::{sync::oneshot, Future};
use prusti_viper::encoder::vir::Program;
use prusti_viper::verifier::VerifierBuilder;
use std::sync::{mpsc, Arc, Mutex};
use std::thread;
use viper::{VerificationBackend, VerificationResult};

pub type FutVerificationResult = Box<Future<Item = VerificationResult, Error = Canceled>>;

struct VerificationRequest {
    pub program: Program,
    pub sender: oneshot::Sender<VerificationResult>,
}

pub struct VerifierThread {
    request_sender: Mutex<mpsc::Sender<VerificationRequest>>,
}

impl VerifierThread {
    pub fn new(verifier_builder: Arc<VerifierBuilder>, backend: VerificationBackend) -> Self {
        let (request_sender, request_receiver) = mpsc::channel::<VerificationRequest>();

        let builder = thread::Builder::new().name(format!("Verifier thread running {}", backend));

        builder
            .spawn(move || {
                let context = verifier_builder.new_verification_context();
                let verifier = context.new_viper_verifier(backend);
                let ast_factory = context.new_ast_factory();
                while let Ok(request) = request_receiver.recv() {
                    let viper_program = request.program.to_viper(&ast_factory);
                    let result = verifier.verify(viper_program);
                    request.sender.send(result).unwrap_or_else(|err| {
                        panic!(
                            "verifier thread attempting to send result to dropped receiver: {:?}",
                            err
                        );
                    });
                }
            })
            .unwrap();

        Self {
            request_sender: Mutex::new(request_sender),
        }
    }

    pub fn verify(&self, program: Program) -> FutVerificationResult {
        let (tx, rx) = oneshot::channel();
        self.request_sender
            .lock()
            .unwrap()
            .send(VerificationRequest {
                program,
                sender: tx,
            })
            .unwrap();
        Box::new(rx)
    }
}
