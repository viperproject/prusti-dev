vir_raw_block! { Assert =>
    impl std::fmt::Display for Assert {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "assert ")?;
            if let Some(label) = &self.label {
                write!(f, "{} ", label)?;
            }
            write!(f, "{}", self.assertion)
        }
    }
}

vir_raw_block! { Assume =>
    impl std::fmt::Display for Assume {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "assume ")?;
            if let Some(label) = &self.label {
                write!(f, "{} ", label)?;
            }
            write!(f, "{}", self.assertion)
        }
    }
}

vir_raw_block! { Havoc =>
    impl std::fmt::Display for Havoc {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Self::Variable(variable) => {
                    write!(f, "havoc {}", variable)
                }
            }
        }
    }
}

vir_raw_block! { Assign =>
    impl std::fmt::Display for Assign {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "assign {} = {};", self.variable, self.expression)
        }
    }
}