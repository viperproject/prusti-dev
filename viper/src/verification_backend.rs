use std::fmt;

#[derive(Clone,Copy,Debug,Eq,PartialEq,Hash)]
pub enum VerificationBackend {
    Silicon,
    Carbon,
}

impl fmt::Display for VerificationBackend {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &VerificationBackend::Silicon => write!(f, "Silicon"),
            &VerificationBackend::Carbon => write!(f, "Carbon"),
        }
    }
}
