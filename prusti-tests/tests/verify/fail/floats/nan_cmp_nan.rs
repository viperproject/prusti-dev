// ignore-test: link to the issue
fn eq32() { 
    assert!(f32::NAN == f32::NAN); //~ ERROR: the asserted expression might not hold
} 
fn ne32() { 
    assert!(f32::NAN != f32::NAN);
}
fn leq32() { 
    assert!(f32::NAN <= f32::NAN); //~ ERROR: the asserted expression might not hold
} 
fn lt32() { 
    assert!(f32::NAN < f32::NAN); //~ ERROR: the asserted expression might not hold
}
fn geq32() { 
    assert!(f32::NAN >= f32::NAN); //~ ERROR: the asserted expression might not hold
} 
fn gt32() { 
    assert!(f32::NAN > f32::NAN); //~ ERROR: the asserted expression might not hold
}

fn eq64() { 
    assert!(f64::NAN == f64::NAN); //~ ERROR: the asserted expression might not hold
}
fn ne64() { 
    assert!(f64::NAN != f64::NAN); 
} 
fn leq64() { 
    assert!(f64::NAN <= f64::NAN); //~ ERROR: the asserted expression might not hold
} 
fn lt64() { 
    assert!(f64::NAN < f64::NAN); //~ ERROR: the asserted expression might not hold
}
fn geq64() { 
    assert!(f64::NAN >= f64::NAN); //~ ERROR: the asserted expression might not hold
} 
fn gt64() { 
    assert!(f64::NAN > f64::NAN); //~ ERROR: the asserted expression might not hold
}

fn main() {}