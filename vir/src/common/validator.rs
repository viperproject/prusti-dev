#[derive(Debug, Clone)]
pub struct ValidationError {
    message: String,
    context: Vec<String>,
}

impl std::fmt::Display for ValidationError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        writeln!(f, "Error: {}", self.message)?;
        for context in &self.context {
            writeln!(f, "  at {}", context)?;
        }
        Ok(())
    }
}

impl ValidationError {
    pub fn new(message: String) -> Self {
        Self {
            message,
            context: Vec::new(),
        }
    }

    pub fn add_context(&mut self, context: String) {
        self.context.push(context);
    }
}

pub trait Validator: std::fmt::Display {
    fn assert_valid_debug(&self) {
        if cfg!(debug_assertions) {
            self.assert_valid();
        }
    }
    fn assert_valid(&self) {
        match self.validate() {
            Ok(_) => {}
            Err(e) => panic!("Validation failed with: {}", e),
        }
    }
    fn validate(&self) -> Result<(), ValidationError>;
}
