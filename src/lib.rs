// Copyright 2022 Tim Hammerquist
//
// Licensed under the [MIT license](https://opensource.org/licenses/MIT).
// This file may not be copied, modified, or distributed
// except according to those terms.

//! HP Voyager-inspired text-based RPN calculator implementation
//!
//! TODO: go into some more detail
//!
//! # Quick Start
//!
//! TODO: write quick start

#![warn(clippy::all, clippy::pedantic)]
#![deny(missing_docs)]

pub mod atom;
pub mod hpn;

mod util;

pub use crate::hpn::HPN;
pub use crate::atom::Atom;
