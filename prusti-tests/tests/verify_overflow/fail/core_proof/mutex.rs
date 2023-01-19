// compile-flags: -Punsafe_core_proof=true

use prusti_contracts::*;

use std::sync::Mutex;

fn test1_fail<T>(m: &Mutex<T>) {
    if let Ok(g1) = m.lock() {
        assert!(false); //~ ERROR: the asserted expression might not hold
    }
}

fn test2<T>(m: &Mutex<T>) {
    if let Ok(g1) = m.lock() {
    }
}

fn test3<T>(m: &Mutex<T>) {
    if let Ok(g1) = m.lock() {
        if let Ok(g2) = m.lock() {
        }
    }
}

fn test4<T>(m: &Mutex<T>) {
    if let Ok(g1) = m.lock() {
        if let Ok(g2) = m.lock() {
            if let Ok(g3) = m.lock() {
            }
        }
    }
}

fn test5<T>(m: &Mutex<T>) {
    if let Ok(g1) = m.lock() {
        if let Ok(g2) = m.lock() {
            if let Ok(g3) = m.lock() {
                if let Ok(g4) = m.lock() {
                }
            }
        }
    }
}

fn main() {}
