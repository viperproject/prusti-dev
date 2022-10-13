struct K { }


fn main()
{
    let mut k1 = K {} ;
    let mut bk1 = &mut k1;
    let mut bbk1 = &mut bk1;
    
    while true {
        if true {
            bbk1 = &mut &mut k1; 
        } 
        else {
            bk1 = &mut k1;
        } 
    }

    // Accessing bbk1 here ruins it!
}
