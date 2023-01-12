extern crate prusti_contracts;
use prusti_contracts::*;

struct Link {next: Box<List>}
type List = Option<Link>;

#[pure]
fn test(mut l: List)
{
    let mut list = &mut l;
    while let Some(next_link) = list {
        list = &mut next_link.next;
    }
    let list_live = &mut (*list);
}


fn main() { }
