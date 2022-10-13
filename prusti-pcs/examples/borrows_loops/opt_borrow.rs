struct K { }


fn main()
{
    let mut k1 = K {} ;
    let mut k2 = K {} ;
    let mut bk1 = &mut k1;
    let mut bbk1 = &mut bk1;
    
    while true {
        if true {
            bbk1 = &mut &mut k1; // Statement 1
        } 
        else if true {
            // bbk1 = &mut bk1;     // Statement 2
        } else {
            bbk1 = &mut &mut k2; // Statement 3
        }
    }
    
    // (1)
    // (2)
    // (3)
    // (1, 2)     NO 
    // (1, 3)
    // (2, 3)     NO 
    // (1, 2, 3)  NO 
    
    // (1,2):
    //  error[E0499]: cannot borrow `k1` as mutable more than once at a time
    //    --> src/lib.rs:13:25
    //     |
    //  8  |     let mut bk1 = &mut k1;
    //     |                   ------- first mutable borrow occurs here
    //  ...
    //  13 |             bbk1 = &mut &mut k1; // Statement 1
    //     |                         ^^^^^^^ second mutable borrow occurs here
    //  ...
    //  16 |             bbk1 = &mut bk1;     // Statement 2
    //     |                    -------- first borrow later used here
    
}
