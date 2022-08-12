// Copyright 2022 Tim Hammerquist
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
//! let hp = HPN::from("21 9 * 5 / 32 +");
//! assert_eq!(Some(69.8), hp.x().to_f64());
//! ```
//!
//! Snapshots of each operation performed are available via the `HPN::tape()` instance method.
//!
//! ```
//! # use hpn::prelude::*;
//! # let hp = HPN::from("21 9 * 5 / 32 +");
//! let tape = hp.tape().collect::<Vec<_>>();
//! println!("{}", tape.join("\n"));
//! // Output:
//! // 0: [ t = 0      | z = 0      | y = 0      | x = 0      ]  <- 21
//! // 1: [ t = 0      | z = 0      | y = 0      | x = 21     ]  <- 9
//! // 2: [ t = 0      | z = 0      | y = 21     | x = 9      ]  <- *
//! // 3: [ t = 0      | z = 0      | y = 0      | x = 189    ]  <- 5
//! // 4: [ t = 0      | z = 0      | y = 189    | x = 5      ]  <- /
//! // 5: [ t = 0      | z = 0      | y = 0      | x = 37.8   ]  <- 32
//! // 6: [ t = 0      | z = 0      | y = 37.8   | x = 32     ]  <- +
//! // 7: [ t = 0      | z = 0      | y = 0      | x = 69.8   ]
//! ```
//!
//! For a simple implementation of an interactive calculator, see the `hpnc` workspace.
//!
//! [hp_voyager]: https://en.wikipedia.org/wiki/Hewlett-Packard_Voyager_series

#![warn(clippy::all, clippy::pedantic)]
#![deny(missing_docs)]

pub mod prelude;

mod atom;
mod hpn;
mod util;

pub use crate::hpn::HPN;
