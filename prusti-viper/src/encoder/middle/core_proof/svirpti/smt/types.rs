use rsmt2::{print::Sort2Smt, SmtRes};
use std::io::Write;
use vir_crate::low::{self as vir_low};

pub(super) trait Type2Smt<'a> {
    fn type_to_smt2<Writer>(&'a self, writer: &mut Writer) -> SmtRes<()>
    where
        Writer: Write;
}

impl<'a, T> Type2Smt<'a> for T
where
    Sort2SmtWrapper<'a, T>: Sort2Smt + 'a,
{
    fn type_to_smt2<Writer>(&'a self, writer: &mut Writer) -> SmtRes<()>
    where
        Writer: Write,
    {
        Sort2SmtWrapper::new(self).sort_to_smt2(writer)
    }
}

pub struct Sort2SmtWrapper<'a, T> {
    ty: &'a T,
}

impl<'a, T> Sort2SmtWrapper<'a, T> {
    pub(super) fn new(ty: &'a T) -> Self {
        Self { ty }
    }
}

pub trait Sort2SmtWrap<T> {
    fn wrap(&self) -> Sort2SmtWrapper<T>;
}

impl<'a> Sort2SmtWrap<vir_low::Type> for vir_low::Type {
    fn wrap(&self) -> Sort2SmtWrapper<vir_low::Type> {
        Sort2SmtWrapper::new(self)
    }
}

impl<'a> Sort2Smt for Sort2SmtWrapper<'a, vir_low::Type> {
    fn sort_to_smt2<Writer>(&self, writer: &mut Writer) -> SmtRes<()>
    where
        Writer: Write,
    {
        match self.ty {
            vir_low::Type::Int => write!(writer, "Int")?,
            vir_low::Type::Bool => write!(writer, "Bool")?,
            vir_low::Type::Perm => write!(writer, "Real")?,
            vir_low::Type::Float(_) => todo!(),
            vir_low::Type::BitVector(_) => todo!(),
            vir_low::Type::Seq(_) => todo!(),
            vir_low::Type::Set(ty) => {
                write!(writer, "Set<")?;
                ty.element_type.type_to_smt2(writer)?;
                write!(writer, ">")?;
            }
            vir_low::Type::MultiSet(_) => todo!(),
            vir_low::Type::Map(_) => todo!(),
            vir_low::Type::Ref => todo!(),
            vir_low::Type::Domain(ty) => write!(writer, "{}", ty.name)?,
        }
        Ok(())
    }
}
