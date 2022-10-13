struct K { }


fn main()
{
    let mut k1 = K {} ;
    let mut bk1 = &mut k1;
    let mut bbk1 = &mut bk1;
    
    while true {
        //let mut tmp = &mut k1;
        //bbk1 = &mut tmp;
        
        bk1 = &mut k1;
        bbk1 = &mut bk1;
        
        // bbk1 = &mut &mut k1; 

    }
    
    let bk = bbk1;
    
}
