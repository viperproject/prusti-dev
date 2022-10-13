extern crate prusti_contracts;
use prusti_contracts::*;

// Non-copy type
struct T {}

#[pure]
fn main() {
    let mut x: T = T {}; // _1
    let mut y: T = T {}; // _2
    let mut bt1 = &mut x; // _3
    let mut bt2 = &mut y; // _4
    let mut n: usize = 10;
    
    // snapshot @39, before loop entry
    // live loans _0, _1 
    // _3 --(bw0)--> _1
    // _4 --(bw1)--> _2

    // @40, before loop break check
    // live loans: 0, 1, 6, 9, 10
    //
    // _3 changed rhs and both are live at loopo head
    // Is collapse implemented for tagged places?
    // Work backwards: 
    
    while n < 20 {
        // @54
        n = n + 1;

        // @68
        let tmp = bt1;
        // _12 = move _3
        //      _12 --(bw9)--> _1
        //      _4  --(bw1)--> _2

        // @74
        bt1 = bt2;
        // _13 = move &mut(*_4)
        //      _12 --(bw9)--> _1
        //      _13 --(bw2)--> *_4 --(pack)--> _4 --(bw1)--> _2
       
        // _3 = move _13
        //      _12 --(bw9)--> _1
        //      _3 --(bw6)--> *_4 --(pack)--> _4 --(bw1)--> _2
        //      zombie loan ??
        
        // @82
        bt2 = tmp;
        // _14 = &mut(*_12)
        //      _14 --(bw3)--> *_12 --(pack)--> _12 --(bw9)--> _1
        //      _3 --(bw6)--> *_4 --(pack)--> _4 --(bw1)--> _2
        //      zombie loan ?? 
        
        // _4 = move _4
        //      _4 --(bw10)--> *_12 --(pack)--> _12 --(bw9)--> _1
        //      _3 --(bw6)--> *_4 --(pack)--> _4 --(bw1)--> _2
        //      zombie loan ?? 
    }

    // Force the loans to live longer than the loop (ie do the join)
    let bbx = bt1;
    let bby = bt2;

    // (all loans still alive + one new one)
    
    // (all loans expire)

    // Force a "gradual" expiry
    let xx = x;
    let yy = y;
}

