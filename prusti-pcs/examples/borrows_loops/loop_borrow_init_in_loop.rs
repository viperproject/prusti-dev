extern crate prusti_contracts;
use prusti_contracts::*;

// Non-copy type
struct T {}

#[pure]
fn main() {
    let mut x: T = T {};    // _1
    let mut bx = &mut x;    // _2
    // _2 --(bw0)--> _1
    // bw0 expires immediately
    
    let mut n = 0;

    // @23, before loop entry
    // no live loans

    loop {
        // @30
        bx = &mut x;
        // _7 = &mut _1
        //      _7 --(bw1)--> _1

        // _6 = &mut(*_7)
        //      _6 --(bw2)--> *_7 --(pack)--> _7 --(bw1)--> _1
        
        // _2 = move _6
        //      _2 --(bw5)--> *_7 --(pack)--> _7 --(bw1)--> _1
        //      zombie loan bw2
        
        // ...

        // bw2 expires, bw1 bw5 live

        if n == 1 {
            break;
        }
        n = n + 1;
    }

    // live: bw1, bw5
    //      _2 --(bw5)--> *_7 --(pack)--> _7 --(bw1)--> _1
    //          (join somehow with)
    //      empty DAG
    
    // Force a gradual expiry
    let bxx = bx;
    // @64
    // _14 = move _2 
    //      _14 --(bw6)--> *_7 --(pack)--> _7 --(bw1)--> _1
    // zombie loan bw5
    
    // ...

    // all loans expire

    let xx = x;
}

