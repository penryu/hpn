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
//! Evaluate a sequence of operations and retrieve the result:
//!
//! ```
//! # use hpn::HPN;
//! # use bigdecimal::ToPrimitive;
//! let hp17 = HPN::from("4 5 + 6 *");
//! assert_eq!(Some(54), hp17.x().to_i32());
//! ```

#![warn(clippy::all, clippy::pedantic)]
#![deny(missing_docs)]

mod atom;
mod hpn;

mod util;

pub use crate::hpn::HPN;
// pub use crate::atom::Atom;
