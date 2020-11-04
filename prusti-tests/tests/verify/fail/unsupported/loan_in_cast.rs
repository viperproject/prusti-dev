// From the libc crate

pub struct cpu_set_t {
    #[cfg(target_pointer_width = "32")]
    bits: [u32; 32],
    #[cfg(target_pointer_width = "64")]
    bits: [u64; 16],
}

pub fn CPU_ZERO(cpuset: &mut cpu_set_t) -> () {
    for slot in cpuset.bits.iter_mut() { //~ ERROR cast statements that create loans are not supported
        *slot = 0;
    }
}

fn main(){}
