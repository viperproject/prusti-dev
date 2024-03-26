use serde_json::json;
use std::time::SystemTime;

const API_HOST: &str = "http://localhost:8080";

pub struct ProgramSubmitter {
    allow_submission: bool,
    program: String,
    original_frontend: String,
    original_verifier: String,
    args: Vec<String>,
    start_time: SystemTime,
    succeeded: bool,
}

impl ProgramSubmitter {
    pub fn new(
        allow_submission: bool,
        program: String,
        original_frontend: String,
        original_verifier: String,
        args: Vec<String>,
    ) -> Self {
        Self {
            allow_submission,
            program,
            original_frontend,
            original_verifier,
            args,
            start_time: SystemTime::now(),
            succeeded: false,
        }
    }

    pub fn set_success(&mut self, success: bool) {
        self.succeeded = success;
    }

    fn runtime(&self) -> u64 {
        self.start_time.elapsed().unwrap().as_millis() as u64
    }

    pub fn submit(&self) {
        if !API_HOST.is_empty() && self.allow_submission {
            let submission = json!({
                "program": &self.program,
                "frontend": &self.original_frontend,
                "args": self.args,
                "originalVerifier": &self.original_verifier,
                "success": self.succeeded,
                "runtime": self.runtime(),
            });

            let client = reqwest::blocking::Client::new();
            let response = client
                .post(&format!("{}/submit-program", API_HOST))
                .json(&submission)
                .send();
            match response {
                Ok(_) => {}
                Err(_) => eprintln!("Program couldn't be submitted"),
            }
        }
    }
}
