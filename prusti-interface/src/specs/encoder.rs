use std::{
    collections::hash_map::Entry,
    fs::File,
    io::{self, Error, Seek, Write},
    path::{Path, PathBuf},
};

use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxIndexSet},
    hir::def_id::{CrateNum, DefId, DefIndex, LOCAL_CRATE},
    middle::{
        mir::interpret::{self, AllocId},
        ty::{self, codec::TyEncoder, PredicateKind, Ty, TyCtxt},
    },
    serialize::{opaque, Encodable, Encoder},
    span::{
        hygiene::{raw_encode_syntax_context, HygieneEncodeContext},
        ByteSymbol, ExpnId, Span, SpanEncoder, StableSourceFileId, Symbol, SyntaxContext,
    },
};
use prusti_utils::launch::{SPECS_FORMAT_VERSION, SPECS_MAGIC};

// Tags for encoding Symbol's
pub(super) const SYMBOL_STR: u8 = 0;
pub(super) const SYMBOL_OFFSET: u8 = 1;
pub(super) const SYMBOL_PREINTERNED: u8 = 2;

pub(super) const BYTE_SYMBOL_STR: u8 = 3;
pub(super) const BYTE_SYMBOL_OFFSET: u8 = 1;
pub(super) const BYTE_SYMBOL_PREINTERNED: u8 = 2;

pub struct DefSpecsEncoder<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    opaque: opaque::FileEncoder<'a>,
    type_shorthands: FxHashMap<Ty<'tcx>, usize>,
    predicate_shorthands: FxHashMap<PredicateKind<'tcx>, usize>,
    interpret_allocs: FxIndexSet<AllocId>,
    hygiene_context: &'a HygieneEncodeContext,
    symbol_table: FxHashMap<Symbol, usize>,
    byte_symbol_table: FxHashMap<ByteSymbol, usize>,
}

impl<'a, 'tcx> DefSpecsEncoder<'a, 'tcx> {
    pub fn serialize<T: for<'b> Encodable<DefSpecsEncoder<'b, 'tcx>>>(
        tcx: TyCtxt<'tcx>,
        path: &Path,
        meta: T,
    ) -> Result<(), io::Error> {
        let _ = std::fs::File::create(path)?;
        std::fs::create_dir_all(path.parent().unwrap())?;

        let hygiene_context = HygieneEncodeContext::default();

        let mut opaque = opaque::FileEncoder::new(path)?;
        opaque.emit_raw_bytes(SPECS_MAGIC);
        opaque.emit_raw_bytes(&SPECS_FORMAT_VERSION.to_le_bytes());
        // Will be filled with the position of the allocation index after
        // encoding everything (same as the crate root position in rustc's
        // metadata encoder).
        opaque.emit_raw_bytes(&0u64.to_le_bytes());

        let mut encoder = DefSpecsEncoder {
            tcx,
            opaque,
            type_shorthands: Default::default(),
            predicate_shorthands: Default::default(),
            interpret_allocs: Default::default(),
            hygiene_context: &hygiene_context,
            symbol_table: Default::default(),
            byte_symbol_table: Default::default(),
        };

        meta.encode(&mut encoder);
        let alloc_index_pos = encoder.encode_interpret_alloc_index();
        encoder.finish(alloc_index_pos).map_err(|e| e.1)
    }

    /// Encodes the allocations referenced by the already encoded data,
    /// followed by an index with the position of each one (indexed like
    /// `interpret_allocs`). Returns the position of that index.
    /// Encoding an allocation can reference further allocations, so we loop
    /// until no new ones show up (same as rustc's metadata encoder).
    fn encode_interpret_alloc_index(&mut self) -> usize {
        let tcx = self.tcx;
        let mut alloc_index = Vec::new();
        let mut n = 0;
        while n < self.interpret_allocs.len() {
            let new_n = self.interpret_allocs.len();
            for idx in n..new_n {
                let id = self.interpret_allocs[idx];
                alloc_index.push(self.position() as u64);
                interpret::specialized_encode_alloc_id(self, tcx, id);
            }
            n = new_n;
        }
        let alloc_index_pos = self.position();
        alloc_index.encode(self);
        alloc_index_pos
    }

    pub fn finish(mut self, alloc_index_pos: usize) -> Result<(), (PathBuf, Error)> {
        self.opaque.finish()?;
        encode_alloc_index_position(self.opaque.file(), alloc_index_pos)
            .map_err(|err| (self.opaque.path().to_path_buf(), err))
    }
}

// Same as `encode_root_position` in rustc's metadata encoder
fn encode_alloc_index_position(mut file: &File, pos: usize) -> Result<(), Error> {
    // We will return to this position after writing the index position.
    let pos_before_seek = file.stream_position()?;

    let header = SPECS_MAGIC.len() + size_of_val(&SPECS_FORMAT_VERSION);
    file.seek(io::SeekFrom::Start(header as u64))?;
    file.write_all(&(pos as u64).to_le_bytes())?;

    // Return to the position where we were before writing the index position.
    file.seek(io::SeekFrom::Start(pos_before_seek))?;
    Ok(())
}

// Taken from rustc:
// https://doc.rust-lang.org/nightly/nightly-rustc/rustc_metadata/rmeta/encoder/macro.encoder_methods.html
macro_rules! encoder_methods {
    ($($name:ident($ty:ty);)*) => {
        $(fn $name(&mut self, value: $ty) -> () {
            self.opaque.$name(value)
        })*
    }
}
impl<'a, 'tcx> Encoder for DefSpecsEncoder<'a, 'tcx> {
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
        emit_char(char);
        emit_str(&str);
        emit_raw_bytes(&[u8]);
    }
}

impl<'a, 'tcx> SpanEncoder for DefSpecsEncoder<'a, 'tcx> {
    fn encode_span(&mut self, span: Span) {
        let sm = self.tcx.sess.source_map();
        let local_crate_stable_id = self.tcx.stable_crate_id(LOCAL_CRATE);
        for bp in [span.lo(), span.hi()] {
            let sf = sm.lookup_source_file(bp);

            let ssfi =
                StableSourceFileId::from_filename_for_export(&sf.name, local_crate_stable_id);
            ssfi.encode(self);
            // Not sure if this is the most stable way to encode a BytePos. If it fails
            // try finding a function in `SourceMap` or `SourceFile` instead. E.g. the
            // `bytepos_to_file_charpos` fn which returns `CharPos` (though there is
            // currently no fn mapping back to `BytePos` for decode)
            (bp - sf.start_pos).encode(self);
        }
    }
    fn encode_symbol(&mut self, sym: Symbol) {
        // if symbol preinterned, emit tag and symbol index
        if Symbol::is_predefined(sym.as_u32()) {
            self.opaque.emit_u8(SYMBOL_PREINTERNED);
            self.opaque.emit_u32(sym.as_u32());
        } else {
            // otherwise write it as string or as offset to it
            match self.symbol_table.entry(sym) {
                Entry::Vacant(o) => {
                    self.opaque.emit_u8(SYMBOL_STR);
                    let pos = self.opaque.position();
                    o.insert(pos);
                    self.emit_str(sym.as_str());
                }
                Entry::Occupied(o) => {
                    let x = *o.get();
                    self.emit_u8(SYMBOL_OFFSET);
                    self.emit_usize(x);
                }
            }
        }
    }

    fn encode_expn_id(&mut self, eid: ExpnId) {
        self.hygiene_context.schedule_expn_data_for_encoding(eid);
        eid.krate.encode(self);
        eid.local_id.as_u32().encode(self);
    }
    fn encode_syntax_context(&mut self, ctx: SyntaxContext) {
        raw_encode_syntax_context(ctx, self.hygiene_context, self);
    }
    fn encode_crate_num(&mut self, cnum: CrateNum) {
        self.tcx.stable_crate_id(cnum).encode(self)
    }
    fn encode_def_index(&mut self, _: DefIndex) {
        panic!("encoding `DefIndex` without context");
    }
    fn encode_def_id(&mut self, id: DefId) {
        self.tcx.def_path_hash(id).encode(self)
    }

    fn encode_byte_symbol(&mut self, byte_sym: ByteSymbol) {
        // if symbol preinterned, emit tag and symbol index
        if Symbol::is_predefined(byte_sym.as_u32()) {
            self.opaque.emit_u8(BYTE_SYMBOL_PREINTERNED);
            self.opaque.emit_u32(byte_sym.as_u32());
        } else {
            // otherwise write it as string or as offset to it
            match self.byte_symbol_table.entry(byte_sym) {
                Entry::Vacant(o) => {
                    self.opaque.emit_u8(BYTE_SYMBOL_STR);
                    let pos = self.opaque.position();
                    o.insert(pos);
                    self.emit_byte_str(byte_sym.as_byte_str());
                }
                Entry::Occupied(o) => {
                    let x = *o.get();
                    self.emit_u8(BYTE_SYMBOL_OFFSET);
                    self.emit_usize(x);
                }
            }
        }
    }
}

impl<'a, 'tcx> TyEncoder<'tcx> for DefSpecsEncoder<'a, 'tcx> {
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
