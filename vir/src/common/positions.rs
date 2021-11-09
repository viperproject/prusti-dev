// FIXME: For some reason if we use macro, the compiler cannot find
// `is_default`.
//
// pub(crate) macro derive_position_impl($ty: ty) {
//     impl $ty {
//         pub fn line(&self) -> i32 {
//             self.line
//         }
//         pub fn column(&self) -> i32 {
//             self.column
//         }
//         pub fn id(&self) -> u64 {
//             self.id
//         }
//         pub fn is_default(&self) -> bool {
//             self.line == 0 && self.column == 0 && self.id == 0
//         }
//     }
// }
// derive_position_impl!(crate::high::Position);
// derive_position_impl!(crate::snapshot::Position);
// derive_position_impl!(crate::polymorphic::Position);
// derive_position_impl!(crate::legacy::Position);

impl crate::high::Position {
    pub fn line(&self) -> i32 {
        self.line
    }
    pub fn column(&self) -> i32 {
        self.column
    }
    pub fn id(&self) -> u64 {
        self.id
    }
    pub fn is_default(&self) -> bool {
        self.line == 0 && self.column == 0 && self.id == 0
    }
}

impl crate::snapshot::Position {
    pub fn line(&self) -> i32 {
        self.line
    }
    pub fn column(&self) -> i32 {
        self.column
    }
    pub fn id(&self) -> u64 {
        self.id
    }
    pub fn is_default(&self) -> bool {
        self.line == 0 && self.column == 0 && self.id == 0
    }
}

impl crate::polymorphic::Position {
    pub fn line(&self) -> i32 {
        self.line
    }
    pub fn column(&self) -> i32 {
        self.column
    }
    pub fn id(&self) -> u64 {
        self.id
    }
    pub fn is_default(&self) -> bool {
        self.line == 0 && self.column == 0 && self.id == 0
    }
}

impl crate::legacy::Position {
    pub fn line(&self) -> i32 {
        self.line
    }
    pub fn column(&self) -> i32 {
        self.column
    }
    pub fn id(&self) -> u64 {
        self.id
    }
    pub fn is_default(&self) -> bool {
        self.line == 0 && self.column == 0 && self.id == 0
    }
}
