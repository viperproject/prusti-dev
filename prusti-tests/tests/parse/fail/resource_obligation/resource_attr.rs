use prusti_contracts::*;

resource! {
    /// documentation should be allowed
    #[pure] //~ ERROR the function in `resource!` shall have only doc attributes
    fn reso(amount: usize);
}

fn main() {}
