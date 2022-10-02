extern crate prusti_contracts;
use prusti_contracts::*;

struct Link {next: Box<List>}
type List = Option<Link>;

#[pure]
fn main() {
    let LL0: List = None;
    let LL1: List = Some(Link{next: Box::new(LL0)});
    let LL2: List = Some(Link{next: Box::new(LL1)});
    let LL3: List = Some(Link{next: Box::new(LL2)});
}

