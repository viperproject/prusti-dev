extern crate prusti_contracts;
use prusti_contracts::*;

struct Link {next: Box<List>}
type List = Option<Link>;

#[pure]
fn main() {
    let mut ll0: List = None;
    let mut ll1: List = Some(Link{next: Box::new(ll0)});
    let mut ll2: List = Some(Link{next: Box::new(ll1)});
    let mut ll3: List = Some(Link{next: Box::new(ll2)});
    
    let mut bl: &mut List = &mut ll3;
    loop {
        match bl {
            Some(next_link) => {
                bl = &mut next_link.next;
            },
            None => { break; },
        }
    }
}
