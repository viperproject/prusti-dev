extern crate prusti_contracts;
use prusti_contracts::*;

struct Link {data: u32, next: Box<List>}
type List = Option<Link>;

#[pure]
fn main() {
    // Setup 
    let mut ll0: List = None;
    let mut ll1: List = Some(Link{next: Box::new(ll0), data: 5});
    let mut ll2: List = Some(Link{next: Box::new(ll1), data: 4});
    let mut ll3: List = Some(Link{next: Box::new(ll2), data: 3});
    let mut ll4: List = Some(Link{next: Box::new(ll3), data: 6});
    let mut l = &mut ll4;


    let mut x: &mut Link = match l {
        None => return,
        Some(lnk) => lnk,
    };
    
    while let Some(v) = &mut(*(*x).next) {
        if x.data > v.data {
            let tmp = x.data;
            x.data = v.data;
            v.data = tmp;
        }
        
        x = v;
    }
}
