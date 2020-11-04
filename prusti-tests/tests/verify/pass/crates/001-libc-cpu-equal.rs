// From the libc crate

pub struct cpu_set_t {
    #[cfg(target_pointer_width = "32")]
    bits: [u32; 32],
    #[cfg(target_pointer_width = "64")]
    bits: [u64; 16],
}

pub fn CPU_EQUAL(set1: &cpu_set_t, set2: &cpu_set_t) -> bool {
    set1.bits == set2.bits
}

fn main(){}
