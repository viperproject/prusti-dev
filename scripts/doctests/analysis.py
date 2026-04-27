import re
import sqlite3
from pathlib import Path

import polars as pl

# ── regex constants ────────────────────────────────────────────────────────────
const_overflow_re = r"range end index \d+ out of range for slice of length \d+"
unsupported_mut_ptr_re = r"error: \[Prusti: verification error\] unsupported rvalue &raw (mut|const) [^ ]+ might be reached"
unsupported_closure_re = r"error: \[Prusti: verification error\] unsupported rvalue {closure@[^}]+} \{[^\}]+\} might be reached"
c_str_re = r"not yet implemented: ConstValue::Slice: &'\?\d+ std::ffi::CStr"
index_out_of_bounds_re = r"index out of bounds: the len is \d+ but the index is \d+"


def _categorize(
    success: str,
    output: str,
    panic_message: str | None,
    first_prusti_frame: str | None,
    panic_location: str | None,
) -> str | None:
    if success != "fail":
        return ""
    
    # can occur in panic message and outside
    if '("wand encoder", "Unsupported(\\"function shape: ContainsAliasType\\")"' in output:
        return "unsupported: function shapes containing alias types (pcg)"

    if panic_message is None:
        if re.search(unsupported_mut_ptr_re, output):
            return "unsupported: &raw mut/const rvalue might be reached (no crash)"
        elif re.search(unsupported_closure_re, output):
            return "unsupported: closure rvalue might be reached (no crash)"
        elif 'consistency error: ConsistencyError { message: "Consistency error: Duplicate identifier' in output:
            return "bug: duplicate identifier in consistency check"
        elif 'consistency error: ConsistencyError { message: "Consistency error: Local variable' in output:
            return "bug: local variable not found in consistency check"
        return "other"

    # all cases with panic messages
    if "not implemented: ty_name for dyn" in panic_message:
        return "unsupported: trait objects"
    # elif "PcgError { kind: Unsupported(DerefUnsafePtr), context: [] }" in output:
    #     return "unsupported (pcg): dereferencing unsafe pointers"
    # elif "PcgError { kind: Unsupported(CallWithUnsafePtrWithNestedLifetime), context: [] }" in output:
    #     return "unsupported (pcg): call with unsafe ptr with nested lifetimes"
    elif panic_message == "called `Result::unwrap()` on an `Err` value: PcgError { kind: Unsupported(DerefUnsafePtr), context: [] }":
        return "unsupported (pcg): dereferencing unsafe pointers"
    elif "<prusti_encoder::encoders::ty::generics::args_ty::GArgsTyEnc as task_encoder::TaskEncoder>::do_encode_full" in output and "compiler/rustc_middle/src/ty/generic_args.rs" in panic_location:
        return "bug: indexing during parametric const encoding"
    elif panic_location == "prusti-encoder/src/encoders/mir_builtin.rs" and panic_message.startswith("expected array") and "prusti_encoder::encoders::mir_builtin::MirBuiltinEnc::handle_unsize" in output:
        return "unsupported: unsizing of other types than refs to arrays"
    elif panic_location == "prusti-encoder/src/encoders/ty/indirect.rs" and first_prusti_frame == "prusti_encoder::encoders::impure::fn_wand::WandEncOutput::encode_predicates_for_function_shape_node" and panic_message == "called `Option::unwrap()` on a `None` value":
        return "bug: lifetime-annotated structs"
    elif '("wand encoder", "Unsupported(\\"function shape: CheckOutlivesError(CannotCompareRegions' in panic_message:
        return "unsupported: function shapes with incomparable regions (pcg)"
    elif panic_message.startswith("not implemented: ty_name for Coroutine"):
        return "unsupported: coroutine types"
    elif re.match(const_overflow_re, panic_message):
        return "bug: const ptr offset overflow"
    elif re.match(index_out_of_bounds_re, panic_message) and first_prusti_frame == "prusti_encoder::encoders::ty::generics::params::GParams::try_normalize::{{closure}}":
        return "bug: ReVar from outer InferCtxt in try_normalize"
    elif panic_message.startswith("not implemented: ty_name for FnDef"):
        return "unsupported: passing functions into other functions"
    elif panic_message == "not yet implemented: bitwise operations":
        return "unsupported: bitwise operations"
    elif panic_message == "not yet implemented: cast kind PointerCoercion(MutToConstPointer, Implicit)":
        return "unsupported: implicit mut-to-const pointer coercions"
    elif panic_message.startswith("called `Result::unwrap()` on an `Err` value: PcgError { kind: Unsupported(CallWithUnsafePtrWithNestedLifetime("):
        return "unsupported (pcg): call with unsafe ptr with nested lifetime"
    elif panic_message.startswith("called `Result::unwrap()` on an `Err` value: PcgError { kind: Unsupported(MoveUnsafePtrWithNestedLifetime("):
        return "unsupported (pcg): move unsafe ptr with nested lifetime"
    elif panic_message == "internal error: entered unreachable code":
        if panic_location == "prusti-encoder/src/encoders/ty/generics/params.rs" and first_prusti_frame == "prusti_encoder::encoders::ty::generics::params::GParams::ty_params::{{closure}}":
            return "bug: g_params uses concrete substs instead of identity args"
        elif panic_location.endswith("pcg/src/borrow_pcg/region_projection.rs") and first_prusti_frame == "prusti_encoder::encoders::impure::fn_wand::WandEncOutput::encode_predicates_for_function_shape_node":
            return "bug: region index out-of-bounds"
    elif panic_message == "assertion failed: ty.is_primitive()" and panic_location == "prusti-encoder/src/encoders/ty/rust_ty.rs" and first_prusti_frame == "prusti_encoder::encoders::ty::rust_ty::RustTyDecomposition::from_prim_ty":
        return "unsupported: binary operation with one operand of pointer type"
    elif re.match(c_str_re, panic_message):
        return "unsupported: CStr constants"
    elif panic_message == "called `Result::unwrap()` on an `Err` value: AlreadyEncoded":
        return "unsupported: recursive struct types"
    elif panic_message == "Box<dyn Any>":
        if "Got a scalar pair where a scalar was expected" in output and panic_location.endswith("rustc_const_eval/src/interpret/operand.rs"):
            return "unsupported: c string literals"
        elif "primitive read not possible for type: ()" in output and panic_location.endswith("rustc_const_eval/src/interpret/operand.rs"):
            return "unsupported: nested references in promoted constants"
        elif "`project_index` called on non-array type" in output and panic_location.endswith("rustc_const_eval/src/interpret/projection.rs"):
            return "unsupported: nested references in promoted constants"
    elif panic_message == "not yet implemented" and panic_location == "prusti-encoder/src/encoders/ty/indirect.rs":
        return "unsupported: enum types in indirect predicate encoder"
    elif panic_message == "not yet implemented: unsizing with unsupported types":
        return "unsupported: unsizing of other types than refs to arrays"

    # class of errors: constant encoding
    elif first_prusti_frame == "prusti_encoder::encoders::ty::data::TyData<D>::expect_primitive" and panic_message.startswith("expected primitive") and "prusti_encoder::encoders::const::ConstEnc::encode_scalar" in output:
        return "unsupported: constant scalars that are not primitives"
    elif first_prusti_frame == "prusti_encoder::encoders::const::ConstEnc::encode_scalar::{{closure}}" and panic_message == "called `Result::unwrap()` on an `Err` value: ReadPointerAsInt(None)":
        return "unsupported: constant pointer-to-pointers"
    elif panic_message == "not yet implemented: ConstValue::Indirect":
        return "unsupported: indirect constant values"
    elif panic_message.startswith("called `Result::unwrap()` on an `Err` value: InvalidUninitBytes(Some(BadBytesAccess {") and first_prusti_frame == "prusti_encoder::encoders::const::ConstEnc::encode_scalar::{{closure}}":
        return "unsupported: invalid uninitialized bytes in constants"

    return panic_message


def load_dbs(paths: list) -> pl.DataFrame:
    """Load results from one or more .db files into a single DataFrame.

    A 'db' column (the filename stem) identifies the source of each row.
    """
    frames = []
    for path in paths:
        p = Path(path)
        conn = sqlite3.connect(p)
        df = pl.from_records(
            conn.execute("SELECT id, file_name, success, output, timestamp FROM results").fetchall(),
            schema=["id", "file_name", "success", "output", "timestamp"],
            orient="row",
        )
        conn.close()
        df = df.with_columns(pl.lit(p.stem).alias("db"))
        frames.append(df)
    return pl.concat(frames)


def transform(df: pl.DataFrame) -> pl.DataFrame:
    """Add derived columns: cleaned output, panic_message, first_prusti_frame,
    panic_location, test_file, and category."""
    df = df.with_columns(
        pl.when(pl.col("success") == "success")
          .then(pl.lit(""))
          .otherwise(
              pl.col("output").str.replace(
                  r"(thread '[^']+') \(\d+\) (panicked)",
                  "${1} ${2}",
              )
          )
          .alias("output"),
        pl.col("output")
            .str.extract(r"panicked at [^\n]+:\n([^\n]+)")
            .alias("panic_message"),
        pl.col("output")
          .str.extract(r"\d+:\s+0x[0-9a-f]+ - (prusti_encoder::[^\n]+)")
          .str.replace(r"::(h[0-9a-f]{16}|\{\{closure\}\})+$", "")
          .alias("first_prusti_frame"),
        pl.col("output")
          .str.extract(r"panicked at ([^:\n]+):\d+:\d+")
          .alias("panic_location"),
        pl.col("file_name")
          .str.extract(r"(\w+)_doctest_\d+\.rs")
          .alias("test_file"),
    )
    df = df.with_columns(
        pl.struct(["success", "output", "panic_message", "first_prusti_frame", "panic_location"])
        .map_elements(
            lambda s: _categorize(
                s["success"], s["output"], s["panic_message"],
                s["first_prusti_frame"], s["panic_location"],
            ),
            return_dtype=pl.String,
        )
        .alias("category")
    )
    return df
