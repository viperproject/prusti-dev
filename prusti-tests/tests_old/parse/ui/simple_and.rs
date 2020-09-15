/// Tests that parser handles spans correctly.

use prusti_contracts::*;

#[requires(12345)]
pub fn test1a(x: i32) {}

#[requires=     "12345)]
pub fn test1b(x: i32) {}

#[

    requires
    
        =     

    "12345" ]
pub fn test1c(x: i32) {}

#[requires(

    12345
    
    )]
pub fn test1d(x: i32) {}

#[requires=r###"

    12345
    
    "###]
pub fn test1e(x: i32) {}

#[requires(true && 12345)]
pub fn test2a(x: i32) {}

#[requires(true &&

    12345  
    
        &&  true && 
            false &&
        
            456)]
pub fn test2b(x: i32) {}

fn main() {}
