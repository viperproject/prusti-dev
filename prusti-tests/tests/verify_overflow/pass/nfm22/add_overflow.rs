use prusti_contracts::*;

struct Height {
    pub revision_number: u64,
    pub revision_height: u64
}

impl Height {

#[requires(u64::MAX - self.revision_height >= delta)]
pub fn add(&self, delta: u64) -> Height {
    Height {
        revision_number: self.revision_number,
        revision_height: self.revision_height + delta,
    }
}

}

fn main(){}
