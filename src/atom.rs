// Copyright 2022 Tim Hammerquist
//
// Licensed under the [MIT license](https://opensource.org/licenses/MIT).
// This file may not be copied, modified, or distributed
// except according to those terms.

//! Atom

use std::fmt;

use crate::prelude::Number;

/// The `Atom` enum represents any whitespace-separated token in an
/// HPN-evaluated expression. Each instance represents either a value (`Value`),
/// or an operation to perform on one or more of those values (`Add`, `Abs`,
/// `Exchange`).
#[derive(Debug, PartialEq)]
pub(crate) enum Atom {
    Abs,
    Add,
    /// Convert ºC to ºF
    CToF,
    /// Change sign of value in `x`
    ChangeSign,
    /// Clear the contents of `x`
    ClearX,
    Cube,
    CubeRoot,
    Div,
    /// Exchange contents of `x` and `y` registers
    Exchange,
    /// _e_
    Euler,
    /// Convert ºF to ºC
    FToC,
    /// n!
    Factorial,
    Help,
    IDiv,
    LastX,
    Mul,
    PI,
    /// Push copy of x; similar to ENTER key with no input
    Push,
    /// Generate random number in range [0, 1)
    Random,
    /// 1/x
    Reciprocal,
    Remainder,
    /// Rolls the stack "down"; eg, `T -> Z, Z -> Y, Y -> X, X -> T`
    Roll,
    Square,
    SquareRoot,
    Sub,
    /// Raise Y to the power of X
    YToX,
    /// Pushes value
    Value(Number),
    /// Represents (and logs) an unrecognized token
    BadToken(String),
}

impl Atom {
    /// Parses an expression and returns a vector of `Atom`s.
    ///
    /// This operation does not fail. Any unrecognized token is returned as a
    /// `BadToken` for the underlying engine to deal with appropriately.
    #[must_use]
    pub fn tokenize(line: &str) -> Vec<Atom> {
        line.split_ascii_whitespace().map(Atom::from).collect()
    }

    pub fn saves_last_x(&self) -> bool {
        match self {
            Atom::Abs
            | Atom::Add
            | Atom::CToF
            | Atom::ChangeSign
            | Atom::Cube
            | Atom::CubeRoot
            | Atom::Div
            | Atom::Euler
            | Atom::FToC
            | Atom::Factorial
            | Atom::IDiv
            | Atom::Mul
            | Atom::PI
            | Atom::Random
            | Atom::Reciprocal
            | Atom::Remainder
            | Atom::Square
            | Atom::SquareRoot
            | Atom::Sub
            | Atom::YToX => true,

            Atom::BadToken(_)
            | Atom::ClearX
            | Atom::Exchange
            | Atom::Help
            | Atom::LastX
            | Atom::Push
            | Atom::Roll
            | Atom::Value(_) => false,
        }
    }

    pub fn operator(&self) -> Option<&'static str> {
        let oper = match self {
            Atom::Abs => "abs",
            Atom::Add => "+",
            Atom::CToF => "ctof",
            Atom::ChangeSign => "chs",
            Atom::ClearX => "clx",
            Atom::Cube => "x^3",
            Atom::CubeRoot => "cbrt",
            Atom::Div => "/",
            Atom::Euler => "e",
            Atom::Exchange => "x<>y",
            Atom::FToC => "ftoc",
            Atom::Factorial => "n!",
            Atom::Help => "help",
            Atom::IDiv => "//",
            Atom::LastX => "lstx",
            Atom::Mul => "*",
            Atom::PI => "pi",
            Atom::Push => "push",
            Atom::Random => "rand",
            Atom::Reciprocal => "1/x",
            Atom::Remainder => "rmd",
            Atom::Roll => "roll",
            Atom::Square => "x^2",
            Atom::SquareRoot => "sqrt",
            Atom::Sub => "-",
            Atom::YToX => "y^x",
            Atom::BadToken(_) | Atom::Value(_) => return None,
        };
        Some(oper)
    }
}

/// Implements the `Display` trait to pretty-print an `Atom` for use in the
/// ticker tape (calculation log).
impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.operator() {
            Some(oper) => write!(f, "{}", oper),
            None => match self {
                Atom::Value(n) => write!(f, "{}", n),
                Atom::BadToken(raw) => write!(f, "{}", raw),
                _ => panic!("Can't display unknown atom"),
            },
        }
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
            "ctof" => Atom::CToF,
            "chs" => Atom::ChangeSign,
            "clx" => Atom::ClearX,
            "x^3" => Atom::Cube,
            "cbrt" => Atom::CubeRoot,
            "/" => Atom::Div,
            "e" => Atom::Euler,
            "x<>y" => Atom::Exchange,
            "ftoc" => Atom::FToC,
            "n!" => Atom::Factorial,
            "help" => Atom::Help,
            "//" => Atom::IDiv,
            "lstx" => Atom::LastX,
            "*" => Atom::Mul,
            "pi" => Atom::PI,
            "push" => Atom::Push,
            "rand" => Atom::Random,
            "1/x" => Atom::Reciprocal,
            "rmd" => Atom::Remainder,
            "roll" => Atom::Roll,
            "x^2" => Atom::Square,
            "sqrt" => Atom::SquareRoot,
            "y^x" => Atom::YToX,
            "-" => Atom::Sub,
            _ => match token.parse::<Number>() {
                Ok(n) => Atom::Value(n),
                Err(_) => Atom::BadToken(token.to_string()),
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::atom::Atom;
    use crate::prelude::{FromPrimitive, Number, Zero};

    type TestResult = Result<(), ()>;

    #[test]
    fn test_bad_token() -> TestResult {
        match Atom::from("alskdj458gy") {
            Atom::BadToken(_) => Ok(()),
            _ => Err(()),
        }
    }

    #[test]
    fn test_atom_creation() {
        assert_eq!(Atom::Abs, Atom::from("abs"));
        assert_eq!(Atom::Add, Atom::from("+"));
        assert_eq!(Atom::CToF, Atom::from("ctof"));
        assert_eq!(Atom::ChangeSign, Atom::from("chs"));
        assert_eq!(Atom::ClearX, Atom::from("clx"));
        assert_eq!(Atom::Cube, Atom::from("x^3"));
        assert_eq!(Atom::CubeRoot, Atom::from("cbrt"));
        assert_eq!(Atom::Div, Atom::from("/"));
        assert_eq!(Atom::Euler, Atom::from("e"));
        assert_eq!(Atom::Exchange, Atom::from("x<>y"));
        assert_eq!(Atom::FToC, Atom::from("ftoc"));
        assert_eq!(Atom::Factorial, Atom::from("n!"));
        assert_eq!(Atom::Help, Atom::from("help"));
        assert_eq!(Atom::IDiv, Atom::from("//"));
        assert_eq!(Atom::LastX, Atom::from("lstx"));
        assert_eq!(Atom::Mul, Atom::from("*"));
        assert_eq!(Atom::PI, Atom::from("pi"));
        assert_eq!(Atom::Push, Atom::from("push"));
        assert_eq!(Atom::Random, Atom::from("rand"));
        assert_eq!(Atom::Reciprocal, Atom::from("1/x"));
        assert_eq!(Atom::Remainder, Atom::from("rmd"));
        assert_eq!(Atom::Roll, Atom::from("roll"));
        assert_eq!(Atom::Square, Atom::from("x^2"));
        assert_eq!(Atom::SquareRoot, Atom::from("sqrt"));
        assert_eq!(Atom::Sub, Atom::from("-"));
        assert_eq!(Atom::YToX, Atom::from("y^x"));
    }

    #[test]
    fn test_atom_to_str() {
        assert_eq!(Some("abs"), Atom::Abs.operator());
        assert_eq!(Some("+"), Atom::Add.operator());
        assert_eq!(Some("chs"), Atom::ChangeSign.operator());
        assert_eq!(Some("clx"), Atom::ClearX.operator());
        assert_eq!(Some("/"), Atom::Div.operator());
        assert_eq!(Some("e"), Atom::Euler.operator());
        assert_eq!(Some("x<>y"), Atom::Exchange.operator());
        assert_eq!(Some("n!"), Atom::Factorial.operator());
        assert_eq!(Some("help"), Atom::Help.operator());
        assert_eq!(Some("//"), Atom::IDiv.operator());
        assert_eq!(Some("lstx"), Atom::LastX.operator());
        assert_eq!(Some("*"), Atom::Mul.operator());
        assert_eq!(Some("pi"), Atom::PI.operator());
        assert_eq!(Some("push"), Atom::Push.operator());
        assert_eq!(Some("rand"), Atom::Random.operator());
        assert_eq!(Some("1/x"), Atom::Reciprocal.operator());
        assert_eq!(Some("rmd"), Atom::Remainder.operator());
        assert_eq!(Some("roll"), Atom::Roll.operator());
        assert_eq!(Some("-"), Atom::Sub.operator());
    }

    #[test]
    fn test_value_zero() {
        assert_eq!(Atom::Value(Number::zero()), Atom::from("0"),);
    }

    #[test]
    fn test_value_real() {
        let expected = Number::from_f64(-1.21).unwrap();
        assert_eq!(Atom::Value(expected), Atom::from("-1.21"));
    }
}
