use std::result;
use prusti_contracts::*;

pub enum ErrorTypes {
    Err1(std::io::Error), // std::io::Error contains a trait object
    Err2,
}

pub struct Request {
    sector: u64,
}

impl Request {
    #[requires(sector == 123)]
    #[ensures(matches!(result, Ok(req) if req.sector == 123))] // Ok
    pub fn good_parse(sector: u64) -> result::Result<Request, ErrorTypes> {
        let req = Request { sector };
        Ok(req)
    }

    #[ensures(matches!(result, Ok(_)))] //~ ERROR postcondition might not hold
    pub fn bad_parse() -> result::Result<Request, ErrorTypes> {
        Err(ErrorTypes::Err2)
    }
}

fn main(){}
