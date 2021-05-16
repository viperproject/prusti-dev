vir_raw_block! { UninterpretedSortDeclaration =>
    impl std::fmt::Display for UninterpretedSortDeclaration {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            self.name.fmt(f)
        }
    }
}
vir_raw_block! { VariableDeclaration =>
    impl std::fmt::Display for VariableDeclaration {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{}: {}", self.name, self.sort)
        }
    }
}
vir_raw_block! { FunctionDeclaration =>
    impl std::fmt::Display for FunctionDeclaration {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{}(", self.name)?;
            for parameter in &self.parameters {
                write!(f, "{},", parameter)?;
            }
            write!(f, ") -> {}", self.return_sort)
        }
    }
}
vir_raw_block! { LabelDeclaration =>
    impl std::fmt::Display for LabelDeclaration {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            self.name.fmt(f)
        }
    }
}
vir_raw_block! { AxiomDeclaration =>
    impl std::fmt::Display for AxiomDeclaration {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "axiom ")?;
            if let Some(name) = &self.name {
                write!(f, "{}", name)?;
            }
            write!(f, "{{ {} }}", self.body)
        }
    }
}