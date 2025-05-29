//! This crate contains various implementations of radix trees (also called tries),
//! which provide efficient storage and lookup of data that shares long common prefixes.

#![no_std]
mod key_trait;
pub mod ptree;

extern crate alloc;
#[cfg(feature = "std")]
extern crate std;

pub use crate::key_trait::*;
