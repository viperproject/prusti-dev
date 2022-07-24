use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxIndexSet},
    hir::def_id::{CrateNum, DefId, DefIndex},
    middle::{
        mir::interpret::AllocId,
        ty::{self, codec::TyEncoder, PredicateKind, Ty, TyCtxt},
    },
    serialize::{opaque, Encodable, Encoder},
};

pub struct DefSpecsEncoder<'tcx> {
    tcx: TyCtxt<'tcx>,
    opaque: opaque::MemEncoder,
    type_shorthands: FxHashMap<Ty<'tcx>, usize>,
    predicate_shorthands: FxHashMap<PredicateKind<'tcx>, usize>,
    interpret_allocs: FxIndexSet<AllocId>,
}

impl<'tcx> DefSpecsEncoder<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        DefSpecsEncoder {
            tcx,
            opaque: opaque::MemEncoder::new(),
            type_shorthands: Default::default(),
            predicate_shorthands: Default::default(),
            interpret_allocs: Default::default(),
        }
    }

    pub fn into_inner(self) -> Vec<u8> {
        self.opaque.finish()
    }
}

macro_rules! encoder_methods {
    ($($name:ident($ty:ty);)*) => {
        $(fn $name(&mut self, value: $ty) -> () {
            self.opaque.$name(value)
        })*
    }
}
impl<'tcx> Encoder for DefSpecsEncoder<'tcx> {
    encoder_methods! {
        emit_usize(usize);
        emit_u128(u128);
        emit_u64(u64);
        emit_u32(u32);
        emit_u16(u16);
        emit_u8(u8);

        emit_isize(isize);
        emit_i128(i128);
        emit_i64(i64);
        emit_i32(i32);
        emit_i16(i16);
        emit_i8(i8);

        emit_bool(bool);
        emit_f64(f64);
        emit_f32(f32);
        emit_char(char);
        emit_str(&str);
        emit_raw_bytes(&[u8]);
    }
}

impl<'tcx> Encodable<DefSpecsEncoder<'tcx>> for DefId {
    fn encode(&self, s: &mut DefSpecsEncoder<'tcx>) {
        s.tcx.def_path_hash(*self).encode(s)
    }
}

impl<'tcx> Encodable<DefSpecsEncoder<'tcx>> for DefIndex {
    fn encode(&self, _: &mut DefSpecsEncoder<'tcx>) {
        panic!("encoding `DefIndex` without context");
    }
}

impl<'tcx> Encodable<DefSpecsEncoder<'tcx>> for CrateNum {
    fn encode(&self, s: &mut DefSpecsEncoder<'tcx>) {
        s.tcx.stable_crate_id(*self).encode(s)
    }
}

impl<'tcx> TyEncoder for DefSpecsEncoder<'tcx> {
    type I = TyCtxt<'tcx>;
    // What the fuck does this mean?
    const CLEAR_CROSS_CRATE: bool = true;

    fn position(&self) -> usize {
        self.opaque.position()
    }

    fn type_shorthands(&mut self) -> &mut FxHashMap<Ty<'tcx>, usize> {
        &mut self.type_shorthands
    }

    fn predicate_shorthands(&mut self) -> &mut FxHashMap<ty::PredicateKind<'tcx>, usize> {
        &mut self.predicate_shorthands
    }

    fn encode_alloc_id(&mut self, alloc_id: &rustc_middle::mir::interpret::AllocId) {
        let (index, _) = self.interpret_allocs.insert_full(*alloc_id);

        index.encode(self)
    }
}
