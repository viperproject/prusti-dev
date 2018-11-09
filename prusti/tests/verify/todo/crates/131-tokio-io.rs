/// Source: https://docs.rs/tokio-io/0.1.6/src/tokio_io/length_delimited.rs.html
extern crate prusti_contracts;

pub struct Builder {
    // Maximum frame length
    max_frame_len: usize,

    // Number of bytes representing the field length
    length_field_len: usize,

    // Number of bytes in the header before the length field
    length_field_offset: usize,

    // Adjust the length specified in the header field by this amount
    length_adjustment: isize,

    // Total number of bytes to skip before reading the payload, if not set,
    // `length_field_len + length_field_offset`
    num_skip: Option<usize>,

    // Length field byte order (little or big endian)
    length_field_is_big_endian: bool,
}

impl Builder {
    pub fn big_endian(&mut self) -> &mut Self {
        self.length_field_is_big_endian = true;
        self
    }

    pub fn little_endian(&mut self) -> &mut Self {
        self.length_field_is_big_endian = false;
        self
    }

    pub fn native_endian(&mut self) -> &mut Self {
        if cfg!(target_endian = "big") {
            self.big_endian()
        } else {
            self.little_endian()
        }
    }
}

fn main() {}
