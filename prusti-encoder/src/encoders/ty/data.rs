use std::{fmt::Debug, hash::Hash, ops::{Deref, Index}};

use prusti_rustc_interface::abi;

pub trait TyDatas<'vir>: Debug + Clone + Copy {
    type TyData: Debug + Clone + 'vir = ();

    type ParamData: Debug + Clone + 'vir = ();
    type OpaqueData: Debug + Clone + 'vir = ();

    type PrimitiveData: Debug + Clone + 'vir = ();

    type ImmRefData: Debug + Clone + 'vir = ();
    type MutRefData: Debug + Clone + 'vir = ();

    type StructData: Debug + Clone + 'vir = ();
    type FieldData: Debug + Clone + 'vir = ();

    type EnumData: Debug + Clone + 'vir = ();
    type VariantData: Debug + Clone + 'vir = ();
}

pub type Ty<'vir, D> = &'vir TyData<'vir, D>;

pub struct TyData<'vir, D: TyDatas<'vir>> {
    pub data: D::TyData,
    pub specifics: TySpecifics<'vir, D>,
}

pub enum TySpecifics<'vir, D: TyDatas<'vir>> {
    Param(D::ParamData),
    Opaque(D::OpaqueData),
    Primitive(D::PrimitiveData),
    ImmRef(D::ImmRefData),
    MutRef(D::MutRefData),
    StructLike(StructData<'vir, D>),
    EnumLike(EnumData<'vir, D>),
}

pub struct StructData<'vir, D: TyDatas<'vir>> {
    pub data: D::StructData,
    pub fields: Vec<D::FieldData>,
}

pub struct EnumData<'vir, D: TyDatas<'vir>> {
    pub data: D::EnumData,
    pub variants: Vec<VariantData<'vir, D>>,
}

pub struct VariantData<'vir, D: TyDatas<'vir>> {
    pub data: D::VariantData,
    pub inner: StructData<'vir, D>,
}

// Utility functions

impl<'vir, D: TyDatas<'vir>> Index<abi::FieldIdx> for StructData<'vir, D> {
    type Output = D::FieldData;

    fn index(&self, index: abi::FieldIdx) -> &Self::Output {
        &self.fields[index.as_usize()]
    }
}

impl<'vir, D: TyDatas<'vir>> Index<abi::VariantIdx> for EnumData<'vir, D> {
    type Output = VariantData<'vir, D>;

    fn index(&self, index: abi::VariantIdx) -> &Self::Output {
        &self.variants[index.as_usize()]
    }
}

impl<'vir, D: TyDatas<'vir>> TySpecifics<'vir, D> {
    pub fn mk_param(data: D::ParamData) -> Self {
        Self::Param(data)
    }

    pub fn mk_opaque(data: D::OpaqueData) -> Self {
        Self::Opaque(data)
    }

    pub fn mk_primitive(data: D::PrimitiveData) -> Self {
        Self::Primitive(data)
    }

    pub fn mk_immref(data: D::ImmRefData) -> Self {
        Self::ImmRef(data)
    }

    pub fn mk_mutref(data: D::MutRefData) -> Self {
        Self::MutRef(data)
    }

    pub fn mk_structlike(data: D::StructData, fields: Vec<D::FieldData>) -> Self {
        Self::StructLike(StructData::new(data, fields))
    }

    pub fn mk_enumlike(data: D::EnumData, variants: Vec<VariantData<'vir, D>>) -> Self {
        Self::EnumLike(EnumData::new(data, variants))
    }

    pub fn is_param(&self) -> bool {
        matches!(self, Self::Param(_))
    }
}

impl<'vir, D: TyDatas<'vir>> TyData<'vir, D> {
    pub(super) fn alloc(self) -> Ty<'vir, D> {
        vir::with_vcx(|vcx| vcx.alloc(self))
    }

    #[track_caller]
    pub fn expect_opaque(&self) -> &D::OpaqueData where Self: Debug {
        match &self.specifics {
            TySpecifics::Opaque(data) => data,
            _ => panic!("expected opaque (was {self:?})"),
        }
    }

    #[track_caller]
    pub fn expect_primitive(&self) -> &D::PrimitiveData where Self: Debug {
        match &self.specifics {
            TySpecifics::Primitive(data) => data,
            _ => panic!("expected primitive (was {self:?})"),
        }
    }

    #[track_caller]
    pub fn expect_immref(&self) -> &D::ImmRefData where Self: Debug {
        match &self.specifics {
            TySpecifics::ImmRef(data) => data,
            _ => panic!("expected immref (was {self:?})"),
        }
    }

    #[track_caller]
    pub fn expect_mutref(&self) -> &D::MutRefData where Self: Debug {
        match &self.specifics {
            TySpecifics::MutRef(data) => data,
            _ => panic!("expected mutref (was {self:?})"),
        }
    }

    pub fn get_structlike(&self) -> Option<&StructData<'vir, D>> {
        match &self.specifics {
            TySpecifics::StructLike(data) => Some(data),
            _ => None,
        }
    }

    #[track_caller]
    pub fn expect_structlike(&self) -> &StructData<'vir, D> where Self: Debug {
        match &self.specifics {
            TySpecifics::StructLike(data) => data,
            _ => panic!("expected struct-like (was {self:?})"),
        }
    }

    pub fn get_enumlike(&self) -> Option<&EnumData<'vir, D>> {
        match &self.specifics {
            TySpecifics::EnumLike(data) => Some(data),
            _ => None,
        }
    }

    #[track_caller]
    pub fn expect_enumlike(&self) -> &EnumData<'vir, D> where Self: Debug {
        match &self.specifics {
            TySpecifics::EnumLike(data) => data,
            _ => panic!("expected enum-like (was {self:?})"),
        }
    }

    pub fn get_variant_any(&self, vid: abi::VariantIdx) -> &StructData<'vir, D> where Self: Debug {
        match &self.specifics {
            TySpecifics::StructLike(s) => {
                assert_eq!(vid, abi::FIRST_VARIANT);
                s
            }
            TySpecifics::EnumLike(e) => &e[vid].inner,
            _ => panic!("expected structlike or enumlike type"),
        }
    }

    #[track_caller]
    pub fn expect_variant(&self, vid: abi::VariantIdx) -> &VariantData<'vir, D> where Self: Debug {
        &self.expect_enumlike()[vid]
    }

    #[track_caller]
    pub fn get_variant_opt(&self, vid: Option<abi::VariantIdx>) -> Option<&StructData<'vir, D>> where Self: Debug {
        match vid {
            None => self.get_structlike(),
            Some(vid) => Some(&self.expect_variant(vid).inner),
        }
    }

    /// Get the struct specifics (or enum variant if specified), panics if not a struct.
    pub fn expect_variant_opt(&self, vid: Option<abi::VariantIdx>) -> &StructData<'vir, D> {
        self.get_variant_opt(vid).unwrap_or_else(|| panic!("expected structlike or enumlike type (was {self:?})"))
    }
}

impl<'vir, D: TyDatas<'vir>> StructData<'vir, D> {
    pub fn zip<D2: TyDatas<'vir>>(&'vir self, other: &'vir StructData<'vir, D2>) -> StructData<'vir, (D, D2)> {
        assert_eq!(self.fields.len(), other.fields.len());
        let fields = self.fields.iter().zip(other.fields.iter());
        StructData {
            data: (&self.data, &other.data),
            fields: fields.map(|(f1, f2)| (f1, f2)).collect(),
        }
    }
}

impl<'vir, D: TyDatas<'vir>> EnumData<'vir, D> {
    pub fn zip<D2: TyDatas<'vir>>(&'vir self, other: &'vir EnumData<'vir, D2>) -> EnumData<'vir, (D, D2)> {
        assert_eq!(self.variants.len(), other.variants.len());
        let variants = self.variants.iter().zip(other.variants.iter());
        EnumData {
            data: (&self.data, &other.data),
            variants: variants.map(|(v1, v2)| v1.zip(v2)).collect(),
        }
    }
}

// Pair implementation for zipping

impl<'vir, D1: TyDatas<'vir>, D2: TyDatas<'vir>> TyDatas<'vir> for (D1, D2) {
    type TyData = (&'vir D1::TyData, &'vir D2::TyData);
    type ParamData = (&'vir D1::ParamData, &'vir D2::ParamData);
    type OpaqueData = (&'vir D1::OpaqueData, &'vir D2::OpaqueData);
    type PrimitiveData = (&'vir D1::PrimitiveData, &'vir D2::PrimitiveData);
    type ImmRefData = (&'vir D1::ImmRefData, &'vir D2::ImmRefData);
    type MutRefData = (&'vir D1::MutRefData, &'vir D2::MutRefData);
    type FieldData = (&'vir D1::FieldData, &'vir D2::FieldData);
    type StructData = (&'vir D1::StructData, &'vir D2::StructData);
    type VariantData = (&'vir D1::VariantData, &'vir D2::VariantData);
    type EnumData = (&'vir D1::EnumData, &'vir D2::EnumData);
}

// Deref implementations

macro_rules! impls {
    ($container:ident$( { $field:ident: $ty:ty })?) => {
impl<'vir, D: TyDatas<'vir>> $container<'vir, D> {
    pub fn new(data: D::$container $(, $field: $ty)?) -> Self {
        Self { data, $($field,)? }
    }
}

impl<'vir, D: TyDatas<'vir>> Debug for $container<'vir, D> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct(stringify!($container)).field("data", &self.data)$(.field(stringify!($field), &self.$field))?.finish()
    }
}

impl<'vir, D: TyDatas<'vir>> Clone for $container<'vir, D> {
    fn clone(&self) -> Self {
        Self { data: self.data.clone(), $($field: self.$field.clone())? }
    }
}

impl<'vir, D: TyDatas<'vir>> PartialEq for $container<'vir, D>
where
    D::TyData: PartialEq, D::ParamData: PartialEq, D::OpaqueData: PartialEq,
    D::PrimitiveData: PartialEq, D::ImmRefData: PartialEq, D::MutRefData: PartialEq,
    D::StructData: PartialEq, D::FieldData: PartialEq, D::EnumData: PartialEq,
    D::VariantData: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.data == other.data $(&& self.$field == other.$field)?
    }
}

impl<'vir, D: TyDatas<'vir>> Eq for $container<'vir, D>
where
    D::TyData: Eq, D::ParamData: Eq, D::OpaqueData: Eq, D::PrimitiveData: Eq,
    D::ImmRefData: Eq, D::MutRefData: Eq, D::StructData: Eq,
    D::FieldData: Eq, D::EnumData: Eq, D::VariantData: Eq,
{}

impl<'vir, D: TyDatas<'vir>> Hash for $container<'vir, D>
where
    D::TyData: Hash, D::ParamData: Hash, D::OpaqueData: Hash, D::PrimitiveData: Hash,
    D::ImmRefData: Hash, D::MutRefData: Hash, D::StructData: Hash,
    D::FieldData: Hash, D::EnumData: Hash, D::VariantData: Hash,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.data.hash(state);
        $(self.$field.hash(state);)?
    }
}

impl<'vir, D: TyDatas<'vir>> Deref for $container<'vir, D> {
    type Target = D::$container;

    fn deref(&self) -> &Self::Target {
        &self.data
    }
}
    };
}

macro_rules! impl_zip {
    ($container:ident$(.$field:ident)?) => {
impl<'vir, D: TyDatas<'vir>> $container<'vir, D> {
    pub fn zip<D2: TyDatas<'vir>>(&'vir self, other: &'vir $container<'vir, D2>) -> $container<'vir, (D, D2)> {
        $container {
            data: (&self.data, &other.data),
            $($field: self.$field.zip(&other.$field),)?
        }
    }
}
    };
}

impls!(TyData { specifics: TySpecifics<'vir, D> });
impl_zip!(TyData.specifics);
impls!(StructData { fields: Vec<D::FieldData> });
impls!(EnumData { variants: Vec<VariantData<'vir, D>> });
impls!(VariantData { inner: StructData<'vir, D> });
impl_zip!(VariantData.inner);

impl<'vir, D: TyDatas<'vir>> Debug for TySpecifics<'vir, D> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Param(arg0) => f.debug_tuple("Param").field(arg0).finish(),
            Self::Opaque(arg0) => f.debug_tuple("Opaque").field(arg0).finish(),
            Self::Primitive(arg0) => f.debug_tuple("Primitive").field(arg0).finish(),
            Self::ImmRef(arg0) => f.debug_tuple("ImmRef").field(arg0).finish(),
            Self::MutRef(arg0) => f.debug_tuple("MutRef").field(arg0).finish(),
            Self::StructLike(arg0) => f.debug_tuple("StructLike").field(arg0).finish(),
            Self::EnumLike(arg0) => f.debug_tuple("EnumLike").field(arg0).finish(),
        }
    }
}

impl<'vir, D: TyDatas<'vir>> Clone for TySpecifics<'vir, D> {
    fn clone(&self) -> Self {
        match self {
            Self::Param(arg0) => Self::Param(arg0.clone()),
            Self::Opaque(arg0) => Self::Opaque(arg0.clone()),
            Self::Primitive(arg0) => Self::Primitive(arg0.clone()),
            Self::ImmRef(arg0) => Self::ImmRef(arg0.clone()),
            Self::MutRef(arg0) => Self::MutRef(arg0.clone()),
            Self::StructLike(arg0) => Self::StructLike(arg0.clone()),
            Self::EnumLike(arg0) => Self::EnumLike(arg0.clone()),
        }
    }
}

impl<'vir, D: TyDatas<'vir>> PartialEq for TySpecifics<'vir, D>
where
    D::TyData: PartialEq, D::ParamData: PartialEq, D::OpaqueData: PartialEq,
    D::PrimitiveData: PartialEq, D::ImmRefData: PartialEq, D::MutRefData: PartialEq,
    D::StructData: PartialEq, D::FieldData: PartialEq, D::EnumData: PartialEq,
    D::VariantData: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Param(l0), Self::Param(r0)) => l0 == r0,
            (Self::Opaque(l0), Self::Opaque(r0)) => l0 == r0,
            (Self::Primitive(l0), Self::Primitive(r0)) => l0 == r0,
            (Self::ImmRef(l0), Self::ImmRef(r0)) => l0 == r0,
            (Self::MutRef(l0), Self::MutRef(r0)) => l0 == r0,
            (Self::StructLike(l0), Self::StructLike(r0)) => l0 == r0,
            (Self::EnumLike(l0), Self::EnumLike(r0)) => l0 == r0,
            _ => false,
        }
    }
}

impl<'vir, D: TyDatas<'vir>> Eq for TySpecifics<'vir, D>
where
    D::TyData: Eq, D::ParamData: Eq, D::OpaqueData: Eq, D::PrimitiveData: Eq,
    D::ImmRefData: Eq, D::MutRefData: Eq, D::StructData: Eq,
    D::FieldData: Eq, D::EnumData: Eq, D::VariantData: Eq,
{}

impl<'vir, D: TyDatas<'vir>> Hash for TySpecifics<'vir, D>
where
    D::TyData: Hash, D::ParamData: Hash, D::OpaqueData: Hash, D::PrimitiveData: Hash,
    D::ImmRefData: Hash, D::MutRefData: Hash, D::StructData: Hash,
    D::FieldData: Hash, D::EnumData: Hash, D::VariantData: Hash,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        core::mem::discriminant(self).hash(state);
    }
}

impl<'vir, D: TyDatas<'vir>> TySpecifics<'vir, D> {
    pub fn zip<D2: TyDatas<'vir>>(&'vir self, other: &'vir TySpecifics<'vir, D2>) -> TySpecifics<'vir, (D, D2)> {
        use TySpecifics::*;
        match (self, other) {
            (Param(d1), Param(d2)) => Param((d1, d2)),
            (Opaque(d1), Opaque(d2)) => Opaque((d1, d2)),
            (Primitive(d1), Primitive(d2)) => Primitive((d1, d2)),
            (ImmRef(d1), ImmRef(d2)) => ImmRef((d1, d2)),
            (MutRef(d1), MutRef(d2)) => MutRef((d1, d2)),
            (StructLike(d1), StructLike(d2)) => StructLike(d1.zip(d2)),
            (EnumLike(d1), EnumLike(d2)) => EnumLike(d1.zip(d2)),
            _ => panic!("Mismatched TySpecifics variants"),
        }
    }
}
