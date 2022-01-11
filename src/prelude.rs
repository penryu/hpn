// Copyright 2022 Tim Hammerquist
//
// Licensed under the [MIT license](https://opensource.org/licenses/MIT).
// This file may not be copied, modified, or distributed
// except according to those terms.

//! Types and traits used by and with the HPN struct and associated types.

pub use bigdecimal::{
    FromPrimitive,
    Num,
    One,
    Signed,
    ToPrimitive,
    Zero,
};
pub use crate::hpn::HPN;
pub use rand::Rng;
pub use std::str::FromStr;

/// Type alias for internal numeric type
pub type Number = bigdecimal::BigDecimal;
