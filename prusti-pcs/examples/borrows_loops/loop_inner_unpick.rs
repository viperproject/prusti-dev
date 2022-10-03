extern crate prusti_contracts;
use prusti_contracts::*;

struct T {}

#[pure]
fn main() {
    let mut x: T = T {};                // _1
    let mut y: T = T {};                // _2

    let mut bx = &mut x;                // bx=_3    bw0
    let mut bbx = &mut bx;              // bbx=_4   bw1
    let mut n: usize = 0;
    // snapshot @39 (before while condition evaluated)
    //      { e _2, e _4 } 
    //      e _4 --(bw1)--> e _3 --(bw0)--> e _1
    
    // @ 40, before break check
    //  live: bw 0, 1, 2, 4, 8, 11
    while n < 10 {
        // @ 54, after break check
        //      { e _1, e _2 }
        //      no loans live
        n  = n + 1;
        /* @ 66 */ 
        bx = &mut y;
        //  _13 = &mut _2
        //      e _13 --(bw2)--> e _2
        
        //  _12 = &mut (*_13)
        //      e _12 --(bw3)--> e *_13 --(pack)--> e _13 --(bw2)--> e_2
        
        //  _3 = move _12
        //      e _3 --(bw11)--> e *_13 --(pack)--> e _13 --(bw2)--> e_2
        //      zombie loan 3 expires shortly thereafter


        /* @ 82 */ 
        bbx = &mut bx;
        // _15 = &mut _3
        //      e _15 --(bw4)--> e _3 --(bw11)--> e *_13 ...
        //          ... --(pack)--> e _13 --(bw2)--> e_2
        
        // _14 = &mut(*_15)
        //      e _14 --(bw5)--> e *_15 --(pack)--> e_15 ...
        //          ... --(bw4)--> e _3 --(bw11)--> e *_13 ...
        //          ... --(pack)--> e _13 --(bw2)--> e_2
        
        // _4 = move _14
        //      e _4 --(bw8)--> e *_15 --(pack)--> e_15 ...
        //          ... --(bw4)--> e _3 --(bw11)--> e *_13 ...
        //          ... --(pack)--> e _13 --(bw2)--> e_2
        //      zombie loan 5 expires shortly thereafter
    }
    
    // Final graph: (_15, _13 are out of scope)
    //      e _4 --(bw8)--> e *_15 --(pack)--> e_15 ...
    //          ... --(bw4)--> e _3 --(bw11)--> e *_13 ...
    //          ... --(pack)--> e _13 --(bw2)--> e_2
    //        (somehow joined with)
    //      e _4 --(bw1)--> e _3 --(bw0)--> e _1
    
    //  Hypothesis: I do not think it is possible for loan bw1 and bw8 to expire
    //      at different locations any longer. Expiry is done eagerly
    //      with variable liveness, so the two loans are coupled:
    //          if of the two expires
    //          and there's no borrow check errors
    //          then the other loan's LHS is not a live variable
    //          so the other loan is not live
    //          so the other loan eagerly expires
    
    /* @112 */  
    let tbbx = bbx;
    // _19 = move _4
    
    //      live loans 0, 1, 2, 4, 8, 9, 11
    //      zombie loans 1, and 8 
    //      e _19 --(bw9)--> e *_15 --(pack)--> e_15 ...
    //          ... --(bw4)--> e _3 --(bw11)--> e *_13 ...
    //          ... --(pack)--> e _13 --(bw2)--> e_2
    //        (somehow joined with) 
    //      e _19 --(bw9)--> e _3 --(bw0)--> e _1

    // ... 

    //      live loans 0, 2, 11
    //      e _3 --(bw11)--> e *_13 --(pack)--> e _13 --(bw2)--> e_2
    //        (somehow joined with) 
    //      e _3 --(bw0)--> e _1

    let tbx = bx;

    // No live loans
    // permission for _1 and _2 regained
    
    let tx = x;
}
