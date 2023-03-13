# Tracing

Utilities for tracing within Prusti. For now the main point of this crate
is to wrap the `instrument` macro of the `tracing` crate to make it work nicely
with return types and rust-analyzer (see comments in `proc-macro-tracing` crate).
