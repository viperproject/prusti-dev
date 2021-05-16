trait Interface {
    type Context;
    type UninterpretedSortSymbol;
}

vir_raw_block! { UninterpretedSortDeclaration =>
    impl<'a, C: Context> ::rsmt2::print::Sort2Smt<&'a C> for UninterpretedSortDeclaration {
        fn sort_to_smt2<Writer: std::io::Write>(
            &self,
            writer: &mut Writer,
            context: &'a C
        ) -> ::rsmt2::SmtRes<()> {
           context.write_uninterpreted_sort_name(writer, &self.name)?;
            Ok(())
        }
    }
}
