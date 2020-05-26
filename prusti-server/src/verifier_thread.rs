use prusti_viper::encoder::vir::Program;
use prusti_viper::verifier::VerifierBuilder;
use std::sync::{mpsc, Arc, Mutex};
use std::thread;
use viper::{VerificationBackend, VerificationResult};

pub trait VerifierCallback: Fn(VerificationResult) -> () + Send + 'static {}
impl<F> VerifierCallback for F where F: Fn(VerificationResult) -> () + Send + 'static {}

struct VerificationRequest {
    pub program: Program,
    pub callback: Box<Fn(VerificationResult) -> () + Send>,
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
                    let callback: Box<_> = request.callback;
                    callback(result);
                }
            })
            .unwrap();

        Self {
            request_sender: Mutex::new(request_sender),
        }
    }

    pub fn verify<F>(&self, program: Program, callback: F)
    where
        F: VerifierCallback,
    {
        self.request_sender
            .lock()
            .unwrap()
            .send(VerificationRequest {
                program,
                callback: Box::new(callback),
            })
            .unwrap();
    }
}
