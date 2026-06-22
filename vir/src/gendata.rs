use std::fmt::Debug;

use crate::{
    data::*,
    debug_info::{DebugInfo, DEBUGINFO_NONE},
    genrefs::*,
    refs::*,
    spans::VirSpan,
    typecheck_error, with_vcx, CastType, CompType, Dyn,
};

use vir_proc_macro::*;

#[derive(VirHash, VirReify, VirSerde)]
pub struct UnOpGenData<'vir, Curr, Next> {
    #[vir(reify_pass)]
    pub kind: UnOpKind,
    pub expr: ExprGenPrim<'vir, Curr, Next>,
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct BinOpGenData<'vir, Curr, Next> {
    #[vir(reify_pass)]
    pub kind: BinOpKind,
    pub lhs: ExprGenDyn<'vir, Curr, Next>,
    pub rhs: ExprGenDyn<'vir, Curr, Next>,
}

impl<'vir, Curr, Next> BinOpGenData<'vir, Curr, Next> {
    pub fn ty(&self) -> TypeDyn<'vir> {
        let ty: TypePrim<'vir> = match self.kind {
            BinOpKind::CmpEq
            | BinOpKind::CmpNe
            | BinOpKind::CmpGt
            | BinOpKind::CmpLt
            | BinOpKind::CmpGe
            | BinOpKind::CmpLe => crate::TYPE_BOOL.upcast_ty(),
            BinOpKind::And | BinOpKind::Or | BinOpKind::Implies => crate::TYPE_BOOL.upcast_ty(),
            BinOpKind::Add | BinOpKind::Sub | BinOpKind::Mul | BinOpKind::Div | BinOpKind::Mod => {
                crate::TYPE_INT.upcast_ty()
            }
            BinOpKind::PermAdd
            | BinOpKind::PermSub
            | BinOpKind::PermMul
            | BinOpKind::PermPermDiv
            | BinOpKind::FracPerm => crate::TYPE_PERM.upcast_ty(),
        };
        ty.as_dyn()
    }
}

/// A binary operation on a native Viper collection (see
/// [`CollectionBinOpKind`]). The collection operand determines the exact
/// operation and the result type.
#[derive(VirHash, VirReify, VirSerde)]
pub struct CollectionBinOpGenData<'vir, Curr, Next> {
    #[vir(reify_pass)]
    pub kind: CollectionBinOpKind,
    pub lhs: ExprGenDyn<'vir, Curr, Next>,
    pub rhs: ExprGenDyn<'vir, Curr, Next>,
}

impl<'vir, Curr, Next> CollectionBinOpGenData<'vir, Curr, Next> {
    pub fn ty(&self) -> TypeDyn<'vir> {
        match self.kind {
            CollectionBinOpKind::Contains => match self.rhs.ty().kind() {
                TypeKind::Multiset(_) => crate::TYPE_INT.as_dyn(),
                TypeKind::Set(_) | TypeKind::Seq(_) | TypeKind::Map(..) => {
                    crate::TYPE_BOOL.as_dyn()
                }
                kind => {
                    typecheck_error!("`Contains` on non-collection type {kind:?}");
                    crate::TYPE_ERR.as_dyn()
                }
            },
            CollectionBinOpKind::Subset => {
                if !matches!(
                    self.lhs.ty().kind(),
                    TypeKind::Set(_) | TypeKind::Multiset(_)
                ) {
                    typecheck_error!("`Subset` on non-set type {:?}", self.lhs.ty().kind());
                }
                crate::TYPE_BOOL.as_dyn()
            }
            CollectionBinOpKind::Union
            | CollectionBinOpKind::Intersection
            | CollectionBinOpKind::Difference => {
                if !matches!(
                    self.lhs.ty().kind(),
                    TypeKind::Set(_) | TypeKind::Multiset(_)
                ) {
                    typecheck_error!(
                        "`{:?}` on non-set type {:?}",
                        self.kind,
                        self.lhs.ty().kind()
                    );
                }
                self.lhs.ty()
            }
            CollectionBinOpKind::Concat | CollectionBinOpKind::Take | CollectionBinOpKind::Drop => {
                if !matches!(self.lhs.ty().kind(), TypeKind::Seq(_)) {
                    typecheck_error!(
                        "`{:?}` on non-`Seq` type {:?}",
                        self.kind,
                        self.lhs.ty().kind()
                    );
                }
                self.lhs.ty()
            }
            CollectionBinOpKind::Index => match self.lhs.ty().kind() {
                TypeKind::Seq(elem) => elem,
                TypeKind::Map(_, val) => val,
                kind => {
                    typecheck_error!("`Index` on non-`Seq`/`Map` type {kind:?}");
                    crate::TYPE_ERR.as_dyn()
                }
            },
        }
    }
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct TernaryGenData<'vir, Curr, Next> {
    pub cond: ExprGenBool<'vir, Curr, Next>,
    pub then: ExprGenDyn<'vir, Curr, Next>,
    pub else_: ExprGenDyn<'vir, Curr, Next>,
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct ForallGenData<'vir, Curr, Next> {
    #[vir(reify_pass)]
    pub qvars: &'vir [LocalDeclDyn<'vir>],
    pub triggers: &'vir [TriggerGen<'vir, Curr, Next>],
    pub body: ExprGenBool<'vir, Curr, Next>,
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct ExistsGenData<'vir, Curr, Next> {
    #[vir(reify_pass)]
    pub qvars: &'vir [LocalDeclDyn<'vir>],
    pub triggers: &'vir [TriggerGen<'vir, Curr, Next>],
    pub body: ExprGenBool<'vir, Curr, Next>,
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct TriggerGenData<'vir, Curr, Next> {
    pub exprs: &'vir [ExprGenDyn<'vir, Curr, Next>],
}

/// A literal of a native Viper collection (`Set`/`Multiset`/`Seq`/`Map`);
/// which one is determined by `ty`. `Map` literals must be empty (maps are
/// built up with [`CollectionUpdateGenData`]).
#[derive(VirHash, VirReify, VirSerde)]
pub struct CollectionLiteralGenData<'vir, Curr, Next> {
    pub values: &'vir [ExprGenDyn<'vir, Curr, Next>],
    #[vir(reify_pass, is_ref)]
    pub ty: TypeDyn<'vir>,
}

/// The native Viper map or sequence update `target[key := val]`.
#[derive(VirHash, VirReify, VirSerde)]
pub struct CollectionUpdateGenData<'vir, Curr, Next> {
    pub target: ExprGenDyn<'vir, Curr, Next>,
    pub key: ExprGenDyn<'vir, Curr, Next>,
    pub val: ExprGenDyn<'vir, Curr, Next>,
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct FuncAppGenData<'vir, Curr, Next> {
    pub target: &'vir str, // TODO: identifiers
    pub args: &'vir [ExprGenDyn<'vir, Curr, Next>],
    // TODO: does this need to be here? (we already track the type in the
    // containing `ExprGenData`)
    #[vir(reify_pass, is_ref)]
    pub result_ty: TypeDyn<'vir>,
    #[vir(reify_pass)]
    pub typ_var_map: &'vir [TypeDyn<'vir>],
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct OldGenData<'vir, Curr, Next> {
    pub expr: ExprGenDyn<'vir, Curr, Next>,
    #[vir(reify_pass)]
    pub label: OldLabel<'vir>,
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct PredicateAppGenData<'vir, Curr, Next> {
    pub target: &'vir str, // TODO: identifiers
    pub args: &'vir [ExprGenDyn<'vir, Curr, Next>],
    pub perm: Option<ExprGenPerm<'vir, Curr, Next>>,
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct UnfoldingGenData<'vir, Curr, Next> {
    pub target: PredicateAppGen<'vir, Curr, Next>,
    pub expr: ExprGenDyn<'vir, Curr, Next>,
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct AccFieldGenData<'vir, Curr, Next> {
    pub recv: ExprGenRef<'vir, Curr, Next>,
    #[vir(reify_pass, is_ref)]
    pub field: FieldDyn<'vir>, // TODO: identifiers
    pub perm: Option<ExprGenPerm<'vir, Curr, Next>>,
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct LetGenData<'vir, Curr, Next> {
    pub name: &'vir str,
    pub val: ExprGenDyn<'vir, Curr, Next>,
    pub expr: ExprGenDyn<'vir, Curr, Next>,
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct WandGenData<'vir, Curr, Next> {
    pub lhs: ExprGenBool<'vir, Curr, Next>,
    pub rhs: ExprGenBool<'vir, Curr, Next>,
}

/*
// TODO: something like this would be a cleaner solution for ExprGenData's
//   generic; when tested, this runs into an infinite loop in rustc ...?
pub trait GenRow {
    type Curr;
    type Next: GenRow;
}
impl GenRow for () {
    type Curr = !;
    type Next = ();
}
impl<A, B: GenRow> GenRow for fn(A) -> B {
    type Curr = A;
    type Next = B;
}*/

// TODO add position and other metadata
#[derive(VirHash, VirSerde)]
pub struct ExprGenData<'vir, Curr: 'vir, Next: 'vir, T: CompType> {
    pub kind: ExprKindGen<'vir, Curr, Next>,
    #[vir(reify_pass)]
    pub debug_info: DebugInfo<'vir>,
    #[vir(reify_pass)]
    pub span: Option<&'vir VirSpan<'vir>>,
    // #[vir(reify_pass)]
    ty: Type<'vir, T>,
}

macro_rules! const_expr {
    ($expr_kind:expr, $ty:ident => $ety:ident) => {{
        const TY: $crate::$ety = unsafe { &$crate::TypeData::new_unchecked($crate::TypeKind::$ty) };
        &ExprGenData {
            kind: $expr_kind,
            debug_info: DEBUGINFO_NONE,
            span: None,
            ty: TY,
        }
    }};
}

impl<'vir, Curr: 'vir, Next: 'vir, T: CompType> ExprGenData<'vir, Curr, Next, T> {
    pub(crate) fn new(kind: ExprKindGen<'vir, Curr, Next>) -> Self {
        Self::new_with_ty(kind, kind.ty().inner_cast_ty())
    }

    pub(crate) fn new_with_ty(kind: ExprKindGen<'vir, Curr, Next>, ty: Type<'vir, T>) -> Self {
        with_vcx(|vcx| Self::new_inner(kind, DebugInfo::new(vcx), vcx.top_span(), ty))
    }

    pub(crate) fn new_inner(
        kind: ExprKindGen<'vir, Curr, Next>,
        debug_info: DebugInfo<'vir>,
        span: Option<&'vir VirSpan<'vir>>,
        ty: Type<'vir, T>,
    ) -> Self {
        if kind.ty() != ty.as_dyn() && !matches!(kind.ty().kind(), crate::TypeKind::Err) {
            typecheck_error!(
                "ExprGenData new_inner: kind {:?} has type {:?}, but trying to create with type {:?}",
                kind,
                kind.ty(),
                ty
            );
        }
        Self {
            kind,
            debug_info,
            span,
            ty,
        }
    }
}

impl<'tcx> crate::VirCtxt<'tcx> {
    pub const fn mk_bool<'vir, const VALUE: bool>(&'vir self) -> ExprBool<'vir> {
        const_expr!(&ExprKindGenData::Const(&ConstData::Bool(VALUE)), Bool => TypeBool)
    }

    pub const fn mk_int<'vir, const VALUE: i128>(&'vir self) -> ExprInt<'vir> {
        if VALUE < 0 {
            // Hack to get a const-promoted absolute value, otherwise rustc
            // would complain that `VALUE.unsigned_abs()` does not have a static
            // lifetime.
            struct Math<const V: i128>;
            impl<const V: i128> Math<V> {
                const ABS: u128 = V.unsigned_abs();
            }
            const_expr!(&ExprKindGenData::UnOp(&UnOpData {
                kind: UnOpKind::Neg,
                expr: const_expr!(&ExprKindGenData::Const(&ConstData::Int(Math::<VALUE>::ABS)), Int => TypePrim),
            }), Int => TypeInt)
        } else {
            const_expr!(&ExprKindGenData::<(), !>::Const(&ConstData::Int(VALUE as u128)), Int => TypeInt)
        }
    }

    pub const fn mk_uint<'vir, const VALUE: u128>(&'vir self) -> ExprInt<'vir> {
        const_expr!(&ExprKindGenData::<(), !>::Const(&ConstData::Int(VALUE)), Int => TypeInt)
    }

    pub const fn mk_wildcard<'vir>(&'vir self) -> ExprPerm<'vir> {
        const_expr!(&ExprKindGenData::Const(&ConstData::Wildcard), Perm => TypePerm)
    }

    pub const fn mk_null<'vir>(&'vir self) -> ExprRef<'vir> {
        const_expr!(&ExprKindGenData::Const(&ConstData::Null), Ref => TypeRef)
    }
}

#[derive(VirHash, VirSerde)]
pub enum ExprKindGenData<'vir, Curr: 'vir, Next: 'vir> {
    Local(LocalDyn<'vir>),
    Field(ExprGenRef<'vir, Curr, Next>, FieldDyn<'vir>), // TODO: FieldApp?
    Old(OldGen<'vir, Curr, Next>),
    Const(Const<'vir>),
    /// Result of a pure function
    Result(TypeDyn<'vir>), // TODO: do we need to store the type here when it's already stored in the containing ExprGen?
    AccField(AccFieldGen<'vir, Curr, Next>),
    Unfolding(UnfoldingGen<'vir, Curr, Next>),
    UnOp(UnOpGen<'vir, Curr, Next>),
    BinOp(BinOpGen<'vir, Curr, Next>),
    CollectionBinOp(CollectionBinOpGen<'vir, Curr, Next>),
    // perm ops?
    // container ops?
    // map ops?
    // sequence, map, set, multiset literals
    CollectionLiteral(CollectionLiteralGen<'vir, Curr, Next>),
    CollectionUpdate(CollectionUpdateGen<'vir, Curr, Next>),
    /// The length/cardinality of a native Viper collection.
    CollectionLen(ExprGenDyn<'vir, Curr, Next>),
    /// The domain (key set) of a native Viper `Map`.
    MapDomain(ExprGenDyn<'vir, Curr, Next>),
    /// The range (value set) of a native Viper `Map`.
    MapRange(ExprGenDyn<'vir, Curr, Next>),
    Ternary(TernaryGen<'vir, Curr, Next>),
    Exists(ExistsGen<'vir, Curr, Next>),
    Forall(ForallGen<'vir, Curr, Next>),
    Let(LetGen<'vir, Curr, Next>),
    FuncApp(FuncAppGen<'vir, Curr, Next>),
    PredicateApp(PredicateAppGen<'vir, Curr, Next>), // TODO: this should not be used instead of acc?
    Wand(WandGen<'vir, Curr, Next>),
    // domain func app
    InhaleExhale(InhaleExhaleGen<'vir, Curr, Next>),
    Lazy(LazyGen<'vir, Curr, Next>),

    // Adt ops
    AdtDestructor(ExprGenDyn<'vir, Curr, Next>, AdtDestructor<'vir, Dyn, Dyn>),
    // For `AdtConstructor` use `FuncApp` instead.
    // TODO: make this not a &str
    AdtDiscriminator(ExprGenDyn<'vir, Curr, Next>, &'vir str),

    Todo(&'vir str),
}

unsafe impl<'vir> Send for ExprKindGenData<'vir, (), !> {}
unsafe impl<'vir> Sync for ExprKindGenData<'vir, (), !> {}

impl<'vir, Curr, Next> ExprKindGenData<'vir, Curr, Next> {
    pub fn ty(&self) -> TypeDyn<'vir> {
        match self {
            ExprKindGenData::Local(l) => l.ty,
            ExprKindGenData::Field(_, f) => f.ty,
            ExprKindGenData::Old(e) => e.expr.ty(),
            ExprKindGenData::Const(c) => c.ty().as_dyn(),
            ExprKindGenData::Result(ty) => ty,
            ExprKindGenData::AccField(_) => crate::TYPE_BOOL.as_dyn(),
            ExprKindGenData::Unfolding(f) => f.expr.ty(),
            ExprKindGenData::UnOp(u) => u.expr.ty().as_dyn(),
            ExprKindGenData::BinOp(b) => b.ty().as_dyn(),
            ExprKindGenData::CollectionBinOp(b) => b.ty(),
            ExprKindGenData::CollectionLiteral(s) => s.ty.as_dyn(),
            ExprKindGenData::CollectionUpdate(u) => u.target.ty(),
            ExprKindGenData::CollectionLen(_) => crate::TYPE_INT.as_dyn(),
            ExprKindGenData::MapDomain(m) => match m.ty().kind() {
                TypeKind::Map(key, _) => with_vcx(|vcx| vcx.mk_ty_set(*key).as_dyn()),
                kind => {
                    typecheck_error!("`MapDomain` of non-`Map` type {kind:?}");
                    crate::TYPE_ERR.as_dyn()
                }
            },
            ExprKindGenData::MapRange(m) => match m.ty().kind() {
                TypeKind::Map(_, val) => with_vcx(|vcx| vcx.mk_ty_set(*val).as_dyn()),
                kind => {
                    typecheck_error!("`MapRange` of non-`Map` type {kind:?}");
                    crate::TYPE_ERR.as_dyn()
                }
            },
            ExprKindGenData::Ternary(t) => t.then.ty(),
            ExprKindGenData::Forall(_) => crate::TYPE_BOOL.as_dyn(),
            ExprKindGenData::Exists(_) => crate::TYPE_BOOL.as_dyn(),
            ExprKindGenData::Let(l) => l.expr.ty(),
            ExprKindGenData::FuncApp(a) => a.result_ty,
            ExprKindGenData::PredicateApp(_) => crate::TYPE_BOOL.as_dyn(),
            ExprKindGenData::Wand(..) => crate::TYPE_BOOL.as_dyn(),
            ExprKindGenData::InhaleExhale(..) => crate::TYPE_BOOL.as_dyn(),
            ExprKindGenData::Lazy(l) => l.ty,
            ExprKindGenData::AdtDestructor(_, destr) => destr.ty,
            ExprKindGenData::AdtDiscriminator(_, _) => crate::TYPE_BOOL.as_dyn(),
            ExprKindGenData::Todo(_msg) => crate::TYPE_ERR.as_dyn(), // panic!("{msg}"),
        }
    }
}

impl<'vir, Curr, Next, T: CompType> ExprGenData<'vir, Curr, Next, T> {
    pub fn ty(&self) -> Type<'vir, T> {
        self.ty
    }

    pub fn lift<Prev>(&'vir self) -> ExprGen<'vir, Prev, ExprKindGen<'vir, Curr, Next>, T> {
        match self.kind {
            ExprKindGenData::Lazy(_) => panic!("cannot lift lazy expression"),
            _ => unsafe {
                std::mem::transmute::<
                    &ExprGenData<'vir, Curr, Next, T>,
                    &ExprGenData<'vir, Prev, ExprKindGen<'vir, Curr, Next>, T>,
                >(self)
            },
        }
    }
}

impl<'vir, T: CompType> ExprGenData<'vir, (), !, T> {
    pub fn lazy<Curr, Next>(&'vir self) -> ExprGen<'vir, Curr, Next, T> {
        unsafe {
            std::mem::transmute::<&ExprGenData<'vir, (), !, T>, &ExprGenData<'vir, Curr, Next, T>>(
                self,
            )
        }
    }
}

pub struct LazyGenData<'vir, Curr: 'vir, Next: 'vir> {
    pub name: &'vir str,
    #[allow(clippy::type_complexity)]
    pub func: Box<dyn for<'a> Fn(&'vir crate::VirCtxt<'a>, Curr) -> Next + 'vir>,
    pub ty: TypeDyn<'vir>,
}

impl<'vir, Curr: 'vir, Next: 'vir> std::hash::Hash for LazyGenData<'vir, Curr, Next> {
    fn hash<H>(&self, _state: &mut H)
    where
        H: std::hash::Hasher,
    {
        panic!("cannot hash lazy expression {}", self.name)
    }
}
impl<'vir, Curr: 'vir, Next: 'vir> serde::Serialize for LazyGenData<'vir, Curr, Next> {
    fn serialize<S>(&self, _serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::ser::Serializer,
    {
        panic!("cannot serialize lazy expression {}", self.name)
    }
}
impl<'vir, Curr: 'vir, Next: 'vir> serde::Deserialize<'vir> for LazyGenData<'vir, Curr, Next> {
    fn deserialize<D>(_deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::de::Deserializer<'vir>,
    {
        panic!("cannot deserialize lazy expression")
    }
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct InhaleExhaleGenData<'vir, Curr: 'vir, Next: 'vir> {
    pub inhale: ExprGenBool<'vir, Curr, Next>,
    pub exhale: ExprGenBool<'vir, Curr, Next>,
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct DomainAxiomGenData<'vir, Curr, Next> {
    pub name: &'vir str, // ? or comment, then auto-gen the names?
    pub expr: ExprGenBool<'vir, Curr, Next>,
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct DomainGenData<'vir, Curr, Next> {
    pub name: &'vir str, // TODO: identifiers
    #[vir(reify_pass)]
    pub typarams: &'vir [DomainParam<'vir>],
    pub axioms: &'vir [DomainAxiomGen<'vir, Curr, Next>],
    #[vir(reify_pass)]
    pub functions: &'vir [DomainFunction<'vir>],
    #[vir(reify_pass)]
    pub interpretation: Option<BackendInterpretation<'vir>>,
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct AdtGenData<'vir, Curr, Next> {
    pub name: &'vir str,
    #[vir(reify_pass)]
    pub typarams: &'vir [DomainParam<'vir>],
    pub constructors: &'vir [AdtConstructorGen<'vir, Curr, Next>],
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct AdtConstructorGenData<'vir, Curr, Next> {
    pub name: &'vir str,
    #[vir(reify_pass)]
    pub args: &'vir [LocalDeclDyn<'vir>],
    pub axiom: Option<ExprGenBool<'vir, Curr, Next>>,
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct PredicateGenData<'vir, Curr, Next> {
    pub name: &'vir str, // TODO: identifiers
    #[vir(reify_pass)]
    pub args: &'vir [LocalDeclDyn<'vir>],
    pub expr: Option<ExprGenBool<'vir, Curr, Next>>,
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct FunctionGenData<'vir, Curr, Next> {
    pub name: &'vir str, // TODO: identifiers
    #[vir(reify_pass)]
    pub args: &'vir [LocalDeclDyn<'vir>],
    #[vir(reify_pass, is_ref)]
    pub ret: TypeDyn<'vir>,
    pub pres: &'vir [ExprGenBool<'vir, Curr, Next>],
    pub posts: &'vir [ExprGenBool<'vir, Curr, Next>],
    pub decreases: DecreasesGen<'vir, Curr, Next>,
    pub expr: Option<ExprGenDyn<'vir, Curr, Next>>,
}

#[derive(VirHash, VirReify, VirSerde)]
pub enum DecreasesGenData<'vir, Curr, Next> {
    None,
    Tuple(
        &'vir [ExprGenDyn<'vir, Curr, Next>],
        Option<ExprGenBool<'vir, Curr, Next>>,
    ),
    Wildcard(Option<ExprGenBool<'vir, Curr, Next>>),
    Star,
}

// TODO: why is this called "pure"?
#[derive(VirHash, VirReify, VirSerde)]
pub struct PureAssignGenData<'vir, Curr, Next> {
    pub lhs: ExprGenDyn<'vir, Curr, Next>,
    //pub dest: Local<'vir>,
    //pub projs: &'vir [&'vir str],
    pub rhs: ExprGenDyn<'vir, Curr, Next>,
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct MethodCallGenData<'vir, Curr, Next> {
    #[vir(reify_pass)]
    pub targets: &'vir [LocalDyn<'vir>],
    pub method: &'vir str,
    pub args: &'vir [ExprGenDyn<'vir, Curr, Next>],
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct StmtGenData<'vir, Curr, Next> {
    pub kind: StmtKindGen<'vir, Curr, Next>,
    // #[vir(reify_pass)] pub debug_info: DebugInfo<'vir>,
    #[vir(reify_pass)]
    pub span: Option<&'vir VirSpan<'vir>>,
}

impl<'vir, Curr: 'vir, Next: 'vir> StmtGenData<'vir, Curr, Next> {
    pub fn new(kind: StmtKindGen<'vir, Curr, Next>) -> Self {
        with_vcx(|vcx| Self {
            kind,
            // debug_info: DebugInfo::new(vcx),
            span: vcx.top_span(),
        })
    }
}

#[derive(VirHash, VirReify, VirSerde)]
pub enum StmtKindGenData<'vir, Curr, Next> {
    LocalDecl(
        #[vir(reify_pass, is_ref)] LocalDeclDyn<'vir>,
        Option<ExprGenDyn<'vir, Curr, Next>>,
    ),
    PureAssign(PureAssignGen<'vir, Curr, Next>),
    Inhale(ExprGenBool<'vir, Curr, Next>),
    Exhale(ExprGenBool<'vir, Curr, Next>),
    Refute(ExprGenBool<'vir, Curr, Next>),
    Unfold(PredicateAppGen<'vir, Curr, Next>),
    Fold(PredicateAppGen<'vir, Curr, Next>),
    Package(WandGen<'vir, Curr, Next>, &'vir [StmtGen<'vir, Curr, Next>]),
    Apply(WandGen<'vir, Curr, Next>),
    MethodCall(MethodCallGen<'vir, Curr, Next>),
    If(
        ExprGenBool<'vir, Curr, Next>,
        &'vir [StmtGen<'vir, Curr, Next>],
        &'vir [StmtGen<'vir, Curr, Next>],
    ),
    Label(&'vir str),
    Comment(&'vir str),
    Dummy(&'vir str),
}

impl<'vir, Curr, Next> StmtKindGenData<'vir, Curr, Next> {
    pub fn alloc(self) -> StmtGen<'vir, Curr, Next> {
        with_vcx(|vcx| self.alloc_vcx(vcx))
    }

    pub(super) fn alloc_vcx<'tcx>(
        self,
        vcx: &'vir crate::VirCtxt<'tcx>,
    ) -> StmtGen<'vir, Curr, Next> {
        vcx.alloc(StmtGenData::new(vcx.alloc(self)))
    }
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct GotoIfGenData<'vir, Curr, Next> {
    pub value: ExprGenDyn<'vir, Curr, Next>,
    pub targets: &'vir [GotoIfTargetGen<'vir, Curr, Next>],
    #[vir(reify_pass, is_ref)]
    pub otherwise: CfgBlockLabel<'vir>,
    pub otherwise_statements: &'vir [StmtGen<'vir, Curr, Next>],
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct GotoIfTargetGenData<'vir, Curr, Next> {
    pub value: ExprGenDyn<'vir, Curr, Next>,
    #[vir(reify_pass, is_ref)]
    pub label: CfgBlockLabel<'vir>,
    pub statements: &'vir [StmtGen<'vir, Curr, Next>],
}

#[derive(VirHash, VirReify, VirSerde)]
pub enum TerminatorStmtGenData<'vir, Curr, Next> {
    AssumeFalse,
    Goto(#[vir(reify_pass, is_ref)] CfgBlockLabel<'vir>),
    GotoIf(GotoIfGen<'vir, Curr, Next>),
    Exit,
    Dummy(&'vir str),
}

#[derive(Debug, VirHash, VirReify, VirSerde)]
pub struct CfgBlockGenData<'vir, Curr, Next> {
    pub label: CfgLabelGen<'vir, Curr, Next>,
    pub stmts: &'vir [StmtGen<'vir, Curr, Next>],
    pub terminator: TerminatorStmtGen<'vir, Curr, Next>,
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct CfgLabelGenData<'vir, Curr, Next> {
    #[vir(reify_pass, is_ref)]
    pub label: CfgBlockLabel<'vir>,
    pub invariants: &'vir [ExprGenBool<'vir, Curr, Next>],
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct MethodGenData<'vir, Curr, Next> {
    pub name: &'vir str, // TODO: identifiers
    #[vir(reify_pass)]
    pub args: &'vir [LocalDeclDyn<'vir>],
    #[vir(reify_pass)]
    pub rets: &'vir [LocalDeclDyn<'vir>],
    // TODO: pre/post - add a comment variant
    pub pres: &'vir [ExprGenBool<'vir, Curr, Next>],
    pub posts: &'vir [ExprGenBool<'vir, Curr, Next>],
    pub body: Option<MethodBodyGen<'vir, Curr, Next>>,
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct MethodBodyGenData<'vir, Curr, Next> {
    pub blocks: &'vir [CfgBlockGen<'vir, Curr, Next>], // first one is the entrypoint
}

#[derive(Debug, VirHash, VirReify, VirSerde)]
pub struct ProgramGenData<'vir, Curr, Next> {
    #[vir(reify_pass)]
    pub fields: &'vir [FieldDyn<'vir>],
    pub adts: &'vir [AdtGen<'vir, Curr, Next>],
    pub domains: &'vir [DomainGen<'vir, Curr, Next>],
    pub predicates: &'vir [PredicateGen<'vir, Curr, Next>],
    pub functions: &'vir [FunctionGen<'vir, Curr, Next>],
    pub methods: &'vir [MethodGen<'vir, Curr, Next>],
    // verification flags?
}

impl<'vir> ProgramGenData<'vir, (), !> {
    pub fn to_ref(&self) -> crate::ProgramRef {
        use std::hash::{Hash, Hasher};
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        self.hash(&mut hasher);
        crate::ProgramRef {
            hash: hasher.finish(),
            // SAFETY: this transmutes a `'vir` (or shorter) reference to a
            //   `'static` reference. The reference is not used except in
            //   `VirCtxt::get_program`. See comment there.
            program: unsafe {
                std::mem::transmute::<&ProgramGenData<'vir, (), !>, &ProgramGenData<'static, (), !>>(
                    self,
                )
            },
        }
    }
}

// TODO: remove this, it is here only to fit the old API
impl<'vir, Curr, Next> ProgramGenData<'vir, Curr, Next> {
    pub fn get_name(&self) -> &str {
        "program"
    }
    pub fn get_check_mode(&self) -> &str {
        "check"
    }
    pub fn get_name_with_check_mode(&self) -> &str {
        "program-check"
    }
    pub fn set_name(&mut self, _name: &str) {}
}

#[cfg(test)]
mod tests {
    use crate::CastType;
    macro_rules! roundtrip_test_eq {
        ($name:ident, $vcx:ident, $val:expr) => {
            #[test]
            fn $name() {
                crate::init_vcx(crate::VirCtxt::new_without_tcx());
                let a = crate::with_vcx(|$vcx| $val);
                let b = bincode::serialize(&a).unwrap();
                let old_vcx = crate::replace_vcx(crate::VirCtxt::new_without_tcx()).unwrap();
                let c = bincode::deserialize(&b[..]).unwrap();
                assert_eq!(a, c);
                drop(old_vcx);
            }
        };
    }
    macro_rules! roundtrip_test_match {
        ($name:ident, $vcx:ident, $val:expr, $exp:pat) => {
            #[test]
            fn $name() {
                crate::init_vcx(crate::VirCtxt::new_without_tcx());
                let a = crate::with_vcx(|$vcx| $val);
                let b = bincode::serialize(&a).unwrap();
                let old_vcx = crate::replace_vcx(crate::VirCtxt::new_without_tcx()).unwrap();
                let c = bincode::deserialize(&b[..]).unwrap();
                assert!(matches!(c, $exp));
                drop(old_vcx);
            }
        };
    }

    // roundtrip_test_match!(
    //     rt_binop,
    //     vcx,
    //     crate::BinOpGenData {
    //         kind: crate::BinOpKind::Sub,
    //         lhs: &crate::ExprGenData {
    //             kind: &crate::ExprKindGenData::<(), !>::Todo("todo"),
    //             debug_info: DebugInfo::new(&vcx)
    //         },
    //         rhs: &crate::ExprGenData {
    //             kind: &crate::ExprKindGenData::<(), !>::Todo("todo"),
    //             debug_info: DebugInfo::new(&vcx)
    //         },
    //     },
    //     crate::BinOpGenData {
    //         kind: crate::BinOpKind::Sub,
    //         lhs: &crate::ExprGenData {
    //             kind: &crate::ExprKindGenData::Todo("todo"),
    //             debug_info: _
    //         },
    //         rhs: &crate::ExprGenData {
    //             kind: &crate::ExprKindGenData::Todo("todo"),
    //             debug_info: _
    //         },
    //     }
    // );
    roundtrip_test_eq!(rt_binopkind, _vcx, crate::BinOpKind::Add);
    roundtrip_test_eq!(
        rt_cfgblocklabel,
        _vcx,
        crate::CfgBlockLabelData::BasicBlock(42)
    );
    roundtrip_test_eq!(rt_const, _vcx, crate::ConstData::Int(0x1122334455667788));
    // roundtrip_test_eq!(
    //     rt_domainfunction,
    //     vcx,
    //     crate::DomainFunctionData {
    //         unique: true,
    //         name: vcx.alloc_str("hello"),
    //         args: &[&crate::TypeData::Bool],
    //         ret: &crate::TypeData::Int,
    //     }
    // );
    roundtrip_test_eq!(
        rt_domainparam,
        vcx,
        crate::DomainParamData {
            name: vcx.alloc_str("hello"),
            index: 0,
        }
    );
    roundtrip_test_eq!(
        rt_field,
        vcx,
        crate::FieldData {
            name: vcx.alloc_str("hello"),
            ty: crate::TYPE_BOOL,
        }
    );
    roundtrip_test_match!(
        rt_stmt,
        _vcx,
        crate::StmtKindGenData::<(), !>::Dummy("hello",),
        crate::StmtKindGenData::Dummy("hello",)
    );
    roundtrip_test_match!(
        rt_terminatorstmt,
        _vcx,
        crate::TerminatorStmtGenData::<(), !>::Exit,
        crate::TerminatorStmtGenData::Exit
    );
    roundtrip_test_eq!(
        rt_type,
        vcx,
        crate::TypeKind::Domain(
            vcx.alloc_str("hello"),
            vcx.alloc_slice(&[crate::TYPE_BOOL.as_dyn()]),
        )
    );
    roundtrip_test_eq!(rt_unopkind, _vcx, crate::UnOpKind::Neg);
    roundtrip_test_eq!(
        rt_unsupportedtype,
        vcx,
        crate::UnsupportedType {
            name: vcx.alloc_str("hello"),
        }
    );

    // TODO: one test for every type in VIR ...
}
