use prusti_interface::environment::EnvBody;
use prusti_rustc_interface::middle::ty;
use std::cell::RefCell;

use crate::{data::*, gendata::*, refs::*};

/// The VIR context is a data structure used throughout the encoding process.
pub struct VirCtxt<'tcx> {
    /// The arena used for bump allocating all VIR AST data. Anything allocated
    /// in the arena (using [VirCtxt::alloc] or similar) is returned as a
    /// shared reference (with the `'tcx` lifetime). This means that different
    /// parts of the AST can refer to the same node, without the need for
    /// unnecessary cloning.
    pub arena: bumpalo::Bump,

    /// The stack of spans during the encoding process. (TODO)
    pub span_stack: Vec<i32>,
    // TODO: span stack
    // TODO: error positions?

    /// The compiler's typing context. This allows convenient access to most
    /// of the compiler's APIs. Is only present when running through `rustc`,
    /// but not when running on the server or in tests.
    pub tcx: Option<ty::TyCtxt<'tcx>>,

    pub body: Option<RefCell<EnvBody<'tcx>>>,
}

impl<'tcx> VirCtxt<'tcx> {
    pub fn new(tcx: ty::TyCtxt<'tcx>, body: EnvBody<'tcx>) -> Self {
        Self {
            arena: bumpalo::Bump::new(),
            span_stack: vec![],
            tcx: Some(tcx),
            body: Some(RefCell::new(body)),
        }
    }

    pub fn new_without_tcx() -> Self {
        Self {
            arena: bumpalo::Bump::new(),
            span_stack: vec![],
            tcx: None,
            body: None,
        }
    }

    pub fn tcx(&self) -> ty::TyCtxt<'tcx> {
        self.tcx.unwrap()
    }

    pub fn body_mut(&self) -> std::cell::RefMut<'_, EnvBody<'tcx>> {
        self.body.as_ref().unwrap().borrow_mut()
    }

    /// Moves `val` into the arena and returns a shared reference to the data.
    pub fn alloc<T>(&self, val: T) -> &T {
        &*self.arena.alloc(val)
    }

    pub fn alloc_str(&self, val: &str) -> &str {
        &*self.arena.alloc_str(val)
    }

    pub fn alloc_slice<T: Copy>(&self, val: &[T]) -> &[T] {
        &*self.arena.alloc_slice_copy(val)
    }

    pub fn alloc_array<T: Copy, const N: usize>(&self, val: &[T; N]) -> &[T; N] {
        &*self.arena.alloc(*val)
    }

    pub fn reset(&mut self) {
        self.arena.reset();
    }

    pub fn apply_ty_substs<'vir>(&'vir self, ty: Type<'vir>, substs: &TySubsts<'vir>) -> Type<'vir> {
        match ty {
            TypeData::DomainTypeParam(p) => substs.get(p.name).unwrap_or(&ty),
            TypeData::Domain(name, args) => {
                let args = args.iter().map(|t| self.apply_ty_substs(t, substs)).collect::<Vec<_>>();
                self.alloc(TypeData::Domain(name, &self.alloc(args)))
            }
            other => other
        }
    }

    pub fn get_program(&'tcx self, program_ref: ProgramRef) -> Program<'tcx> {
        // SAFETY: this transmutes a `'static` reference to a `'tcx` reference.
        //   This is safe as long as the program was allocated in this arena
        //   and the arena was not emptied in the meantime. For the time being,
        //   there is only ever a single `VirCtxt` and no arena emptying.
        unsafe { std::mem::transmute(program_ref.program) }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct ProgramRef {
    pub(crate) hash: u64,
    pub(crate) program: Program<'static>,
}

impl ProgramRef {
    pub fn get_hash(&self) -> u64 {
        self.hash
    }

    pub fn get_name(&self) -> &str { "program" }
    pub fn get_rust_name(&self) -> &str { "rustprogram" }
    pub fn get_check_mode(&self) -> &str { "check" }
    pub fn get_name_with_check_mode(&self) -> &str { "program-check" }
    pub fn set_name(&mut self, _name: &str) {}
}

impl serde::Serialize for ProgramRef {
    fn serialize<S>(&self, s: S) -> Result<S::Ok, S::Error>
    where S: serde::Serializer
    {
        with_vcx(|vcx| {
            let program = vcx.get_program(*self);
            program.serialize(s)
        })
    }
}
impl<'de> serde::Deserialize<'de> for ProgramRef {
    fn deserialize<D>(d: D) -> Result<Self, D::Error>
    where D: serde::Deserializer<'de>
    {
        let program = Program::deserialize(d)?;
        Ok(program.to_ref())
    }
}

thread_local! {
    static VCTX: RefCell<Option<VirCtxt<'static>>> = RefCell::new(None);
}

/// Initialises the VIR context. Should only be called once, when the type
/// context is available.
pub fn init_vcx<'tcx>(vcx: VirCtxt<'tcx>) {
    VCTX.replace(Some(unsafe { std::mem::transmute(vcx) }));
}

pub(crate) fn replace_vcx<'tcx>(vcx: VirCtxt<'tcx>) -> Option<VirCtxt<'tcx>> {
    unsafe { std::mem::transmute(VCTX.replace(Some(std::mem::transmute(vcx)))) }
}

/// Perform an action with the VIR context.
pub fn with_vcx<'vir, 'tcx: 'vir, F, R>(f: F) -> R
where
    F: FnOnce(&'vir VirCtxt<'tcx>) -> R,
{
    VCTX.with_borrow(|vcx: &Option<VirCtxt<'static>>| {
        // SAFETY: the 'vir and 'tcx given to this function will always be
        //   the same (or shorter) than the lifetimes of the VIR arena and
        //   the rustc type context, respectively
        let vcx = vcx.as_ref().expect("VIR context was not initialised");
        let vcx = unsafe { std::mem::transmute(vcx) };
        f(vcx)
    })
}

pub fn with_vcx_mut<'vir, 'tcx: 'vir, F, R>(f: F) -> R
where
    F: FnOnce(&'vir mut VirCtxt<'tcx>) -> R,
{
    VCTX.with_borrow_mut(|vcx: &mut Option<VirCtxt<'static>>| {
        // SAFETY: the 'vir and 'tcx given to this function will always be
        //   the same (or shorter) than the lifetimes of the VIR arena and
        //   the rustc type context, respectively
        let vcx = vcx.as_mut().expect("VIR context was not initialised");
        let vcx = unsafe { std::mem::transmute(vcx) };
        f(vcx)
    })
}
