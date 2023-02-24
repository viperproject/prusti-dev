// compile-flags: -Psif=true -Pserver_address=MOCK

// Example from "Secure Information Flow and Pointer Confinement in a Java-like Language"
// A. Banerjee and D. A. Naumann
// CSFW 2002

use prusti_contracts::*;

// ignore-test: rust's borrow checker makes this example hard to translate without too much modification

// HIV is high, name is low
struct Patient {
    name: String,
    hiv: String,
}

impl Patient {
    fn get_name(&self) -> &str {
        &self.name
    }

    #[requires(low(name))]
    #[ensures(low(&self.name))]
    fn set_name(&mut self, name: String) {
        self.name = name;
    }

    fn get_hiv(&self) -> &str {
        &self.hiv
    }

    fn set_hiv(&mut self, hiv: String) {
        self.hiv = hiv;
    }
}

#[trusted]
#[ensures(low(result))]
#[ensures(low(&result.name))]
fn read_file() -> Patient {
    Patient {
        name: String::new(),
        hiv: String::new(),
    }
}

// the result is high
#[trusted]
fn read_from_trusted_channel() -> String {
    String::new()
}

fn main() {
    let lbuf: &str;
    let mut hbuf: &str;
    let mut lp = read_file();
    let mut xp = Patient {
        name: String::new(),
        hiv: String::new(),
    };
    lbuf = lp.get_name();
    hbuf = lp.get_name();
    xp.set_name(lbuf);
    hbuf = read_from_trusted_channel();
    xp.set_hiv(hbuf);
}
