// Copyright 2022 Tim Hammerquist
//
// Licensed under the [MIT license](https://opensource.org/licenses/MIT).
// This file may not be copied, modified, or distributed
// except according to those terms.

//! Atom

use bigdecimal::BigDecimal;
use std::fmt;

/// The `Atom` enum represents any whitespace-separated token in an
/// HPN-evaluated expression. Each instance represents either a value (`Value`),
/// or an operation to perform on one or more of those values (`Add`, `Abs`,
/// `Exchange`).
#[derive(Debug, PartialEq)]
pub enum Atom {
    /// Arithmetic addition
    Add,
    /// Arithmetic subtraction
    Sub,
    /// Arithmetic multiplication
    Mul,
    /// Arithmetic real division
    Div,
    /// Arithmetic integer division
    IDiv,
    /// Integer Remainder
    Remainder,
    /// Absolute value
    Abs,
    /// Euler's constant (e)
    Euler,
    /// Factorial; eg: 5! => (5*4*3*2*1) => 120
    Factorial,
    /// Invert x - 1/x
    InvX,
    /// pi
    PI,
    /// Generate random number in range [0, 1)
    Random,
    /// Change size of value in x
    ChangeSign,
    /// Exchange contents of x and y registers
    Exchange,
    /// Push copy of x; similar to ENTER key with no input
    Push,
    /// Pushes value
    Value(BigDecimal),
    /// Represents (and logs) an unrecognized token
    BadToken(String),
}

impl Atom {
    #[must_use]

    /// Parses an expression and returns a vector of `Atom`s.
    ///
    /// This operation does not fail. Any unrecognized token is returned as a
    /// `BadToken` for the underlying engine to deal with appropriately.
    pub fn tokenize(line: &str) -> Vec<Atom> {
        line
            .split_ascii_whitespace()
            .filter_map(|token| Atom::try_from(token).ok())
            .into_iter()
            .collect()
    }

    /// Indicates whether the given `Atom` is recognized.
    ///
    /// Only `BadToken` yields a `false` value.
    #[must_use]
    pub fn is_valid(&self) -> bool {
        !matches!(self, Atom::BadToken(_))
    }

    /// Predicate indicates if `Atom` is a `Value`.
    #[must_use]
    pub fn is_value(&self) -> bool {
        matches!(self, Atom::Value(_))
    }

    /// If the `Atom` is a `Value`, returns `Some(value)`. If `Atom` is any
    /// other type, returns `None`.
    #[must_use]
    pub fn value(&self) -> Option<BigDecimal> {
        match self {
            Atom::Value(ref n) => Some(n.clone()),
            _ => None,
        }
    }
}

/// Implements the `Display` trait to pretty-print an `Atom` for use in the
/// ticker tape (calculation log).
impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let repr = match &self {
            Atom::Value(n) => n.to_string(),
            Atom::BadToken(raw) => format!("Bad token {:?}", raw.clone()),
            _ => format!("{:?}", self),
        };

        write!(f, "{}", repr)
    }
}

/// Constructs an `Atom` instance associated with the token given.
///
/// Unrecognized tokens returned as `BadToken`s and not treated as failures.
impl From<&str> for Atom {
    fn from(token: &str) -> Self {
        match token {
            "abs" => Atom::Abs,
            "+" => Atom::Add,
            "chs" => Atom::ChangeSign,
            "/" => Atom::Div,
            "e" => Atom::Euler,
            "exch" => Atom::Exchange,
            "!" | "n!" => Atom::Factorial,
            "//" => Atom::IDiv,
            "1/x" => Atom::InvX,
            "*" => Atom::Mul,
            "pi" => Atom::PI,
            "push" => Atom::Push,
            "rand" => Atom::Random,
            "rmd" | "%" => Atom::Remainder,
            "-" => Atom::Sub,
            _ => match token.parse::<BigDecimal>() {
                Ok(n) => Atom::Value(n),
                Err(_) => Atom::BadToken(token.to_string()),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bigdecimal::{Num, Zero};

    #[test]
    fn test_bad_token() {
        assert!(!Atom::from("nonsense").is_valid());
    }

    #[test]
    fn test_abs() {
        assert_eq!(Atom::Abs, Atom::from("abs"));
    }

    #[test]
    fn test_add() {
        assert_eq!(Atom::Add, Atom::from("+"));
    }

    #[test]
    fn test_change_sign() {
        assert_eq!(Atom::ChangeSign, Atom::from("chs"));
    }

    #[test]
    fn test_div() {
        assert_eq!(Atom::Div, Atom::from("/"));
    }

    #[test]
    fn test_euler() {
        assert_eq!(Atom::Euler, Atom::from("e"));
    }

    #[test]
    fn test_exchange() {
        assert_eq!(Atom::Exchange, Atom::from("exch"));
    }

    #[test]
    fn test_factorial_excl() {
        assert_eq!(Atom::Factorial, Atom::from("!"));
    }

    #[test]
    fn test_factorial_n_excl() {
        assert_eq!(Atom::Factorial, Atom::from("n!"));
    }

    #[test]
    fn test_idiv() {
        assert_eq!(Atom::IDiv, Atom::from("//"));
    }

    #[test]
    fn test_inv_x() {
        assert_eq!(Atom::InvX, Atom::from("1/x"));
    }

    #[test]
    fn test_mul() {
        assert_eq!(Atom::Mul, Atom::from("*"));
    }

    #[test]
    fn test_pi() {
        assert_eq!(Atom::PI, Atom::from("pi"));
    }

    #[test]
    fn test_push() {
        assert_eq!(Atom::Push, Atom::from("push"));
    }

    #[test]
    fn test_random() {
        assert_eq!(Atom::Random, Atom::from("rand"));
    }

    #[test]
    fn test_remainder() {
        assert_eq!(Atom::Remainder, Atom::from("rmd"));
        assert_eq!(Atom::Remainder, Atom::from("%"));
    }

    #[test]
    fn test_sub() {
        assert_eq!(Atom::Sub, Atom::from("-"));
    }

    #[test]
    fn test_value_zero() {
        assert_eq!(
            Some(BigDecimal::zero()),
            Atom::from("0").value(),
        );
    }

    #[test]
    fn test_value_pi() {
        assert_eq!(
            BigDecimal::from_str_radix("3.14159265", 10).unwrap(),
            Atom::from("3.14159265").value().unwrap(),
        );
    }
}
