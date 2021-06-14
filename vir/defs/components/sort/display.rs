vir_raw_block! { Sort =>
    impl std::fmt::Display for Sort {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Sort::Bool => write!(f, "Bool"),
                Sort::Int => write!(f, "Int"),
                Sort::Real => write!(f, "Real"),
                Sort::Uninterpreted { name } => write!(f, "{}", name),
            }
        }
    }
}
