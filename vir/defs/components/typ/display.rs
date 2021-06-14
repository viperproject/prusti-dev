vir_raw_block! { Type =>
    impl std::fmt::Display for Type {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Type::Bool => write!(f, "Bool"),
                Type::Int => write!(f, "Int"),
                Type::Real => write!(f, "Real"),
                Type::Domain(domain) => write!(f, "{}", domain),
            }
        }
    }
}
vir_raw_block! { DomainType =>
    impl std::fmt::Display for DomainType {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "Domain<{}>", self.name)
        }
    }
}
