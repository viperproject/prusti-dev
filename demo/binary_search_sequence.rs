#![allow(dead_code)]
#![allow(unused_imports)]







use prusti_contracts::*;


/// Interface to any indexable way of fetching i32s with indices [0, length-1]
trait Sequence {
  
  #[pure]
  fn length(&self) -> usize; // typical integer type for indices  
  
  #[pure]
  #[requires(index < self.length())]
  fn get(&self, index: usize) -> i32; // unsigned 32-bit integers
}












//#[requires(forall(|i:usize, j:usize| i < j && j < seq.length() 
//                                           ==> seq.get(i) <= seq.get(j)))]
#[ensures(match result {
    Some(v) => target == seq.get(v),
    None => true//forall(|i:usize| i < seq.length() ==> seq.get(i) != target)
})]
fn binary_search<T: Sequence>(seq: &T, target: i32) -> Option<usize> {
    let mut low = 0;
    let mut high = seq.length();
   
    while low < high {

        body_invariant!(high <= seq.length());
//        body_invariant!(forall(|i:usize| i < low || i >= high && i < seq.length() ==> seq.get(i) != target));
let mid = low + (high - low) / 2;
let mid_val = seq.get(mid);
        if mid_val < target {
            low = mid + 1;
        } else if mid_val > target {
            high = mid;
        } else { // found it!
            return Some(mid);
        }
    }
    return None;
}