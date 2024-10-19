#![deny(unsafe_op_in_unsafe_fn)]
#![allow(
    clippy::option_map_unit_fn,
    clippy::new_without_default,
    clippy::try_err
)]

mod ast;
pub mod clox;
pub mod jlox;
mod scanner;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ErrorKind {
    CompilationError,
    RuntimeError,
}
