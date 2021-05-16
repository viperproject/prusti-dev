trait Interface {
    type UninterpretedSortSymbol;
    type Context;
}

vir_raw_block! { Sort =>
    impl<'a, C: Context> ::rsmt2::print::Sort2Smt<&'a C> for Sort {
        fn sort_to_smt2<Writer: std::io::Write>(
            &self,
            writer: &mut Writer,
            context: &'a C
        ) -> ::rsmt2::SmtRes<()> {
            match self {
                Sort::Bool => write!(writer, "Bool")?,
                Sort::Int => write!(writer, "Int")?,
                Sort::Real => write!(writer, "Real")?,
                Sort::Uninterpreted {
                    name
                } => context.write_uninterpreted_sort_name(writer, name)?,
            }
            Ok(())
        }
    }
}
