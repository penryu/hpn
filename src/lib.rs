// Copyright 2023 Tim Hammerquist
//
// Licensed under the [MIT license](https://opensource.org/licenses/MIT).
// This file may not be copied, modified, or distributed except according to those terms.

//! [HP Voyager][hp_voyager]-inspired text-based RPN calculator
//!
//! Originating from a deep desire to have an RPN calculator from inside an IRC session, the `HPN`
//! struct evaluates stack-based calculator instructions in a HP Voyager-inspired "virtual
//! calculator".
//!
//! HPN uses a 4-register stack-based RPN implementation based on and inspired by the [HP
//! Voyager][hp_voyager] series of calculators.
//!
//! Calculator state and history are preserved inside the `HPN` object.
//!
//! The current state of registers are available as instance methods; eg, `hpn.x()`, `hpn.y()`,
//! etc.
//!
//! ```
//! use hpn::prelude::*;
//!
//! // convert 21ºC to ºF
//! let mut hp = HPN::from("21 9 * 5 / 32 +");
//! assert_eq!(Some(69.8), hp.x().to_f64());
//! // or just
//! hp.evaluate("21 ctof");
//! assert_eq!(Some(69.8), hp.x().to_f64());
//! ```
//!
//! Snapshots of each operation performed are available via the `HPN::tape()` instance method.
//!
//! ```
//! # use hpn::prelude::*;
//! # let mut hp = HPN::from("21 9 * 5 / 32 +");
//! # hp.evaluate("21 ctof");
//! let tape = hp.tape().collect::<Vec<_>>().join("\n");
//! println!("{tape}");
//! // Output:
//! // 0: [ T:    0.000 | Z:    0.000 | Y:    0.000 | X:    0.000 ]  <- 21
//! // 1: [ T:    0.000 | Z:    0.000 | Y:    0.000 | X:   21.000 ]  <- 9
//! // 2: [ T:    0.000 | Z:    0.000 | Y:   21.000 | X:    9.000 ]  <- *
//! // 3: [ T:    0.000 | Z:    0.000 | Y:    0.000 | X:  189.000 ]  <- 5
//! // 4: [ T:    0.000 | Z:    0.000 | Y:  189.000 | X:    5.000 ]  <- /
//! // 5: [ T:    0.000 | Z:    0.000 | Y:    0.000 | X:   37.800 ]  <- 32
//! // 6: [ T:    0.000 | Z:    0.000 | Y:   37.800 | X:   32.000 ]  <- +
//! // 7: [ T:    0.000 | Z:    0.000 | Y:    0.000 | X:   69.800 ]  <- 21
//! // 8: [ T:    0.000 | Z:    0.000 | Y:   69.800 | X:   21.000 ]  <- ctof
//! // 9: [ T:    0.000 | Z:    0.000 | Y:   69.800 | X:   69.800 ]
//! ```
//!
//! ## Command-line Client
//!
//! The easiest way to use this calculator is via the CLI client `hpnc`:
//!
//! ```text
//! $ cargo install hpn
//! $ hpnc
//! hpnc x.x.x
//! > 77 ftoc
//!  0: [ T:    0.000 | Z:    0.000 | Y:    0.000 | X:    0.000 ]  <- 77
//!  1: [ T:    0.000 | Z:    0.000 | Y:    0.000 | X:   77.000 ]  <- ftoc
//!  2: [ T:    0.000 | Z:    0.000 | Y:    0.000 | X:   25.000 ]
//! => 25
//! >
//! ```
//!
//! [hp_voyager]: https://en.wikipedia.org/wiki/Hewlett-Packard_Voyager_series

#![warn(clippy::pedantic)]
#![deny(clippy::all)]
#![deny(missing_docs)]

pub mod prelude;

mod atom;
mod hpn;
mod util;

pub use crate::hpn::HPN;
