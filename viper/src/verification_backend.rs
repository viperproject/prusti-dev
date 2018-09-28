use std::fmt;

#[derive(Clone,Copy,Debug,Eq,PartialEq,Hash)]
pub enum VerificationBackend {
    Silicon,
    Carbon,
}

impl VerificationBackend {
    pub fn from_str(backend: &str) -> Self {
        match backend {
            "silicon" => VerificationBackend::Silicon,
            "carbon" => VerificationBackend::Carbon,
            _ => panic!(
                "Invalid verification backend: '{}'. Allowed values are 'Silicon' and 'Carbon'",
                backend
            )
        }
    }
}

impl fmt::Display for VerificationBackend {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &VerificationBackend::Silicon => write!(f, "Silicon"),
            &VerificationBackend::Carbon => write!(f, "Carbon"),
        }
    }
}
