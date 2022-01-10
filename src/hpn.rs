// Copyright 2022 Tim Hammerquist
//
// Licensed under the [MIT license](https://opensource.org/licenses/MIT).
// This file may not be copied, modified, or distributed
// except according to those terms.

//! HPN - HP-style RPN calculator
//!
//! The HPN calculator uses a 4-register stack-based RPN implementation based on
//! and inspired by the [HP Voyager][hp_voyager] series of calculators.
//!
//! [hp_voyager]: https://en.wikipedia.org/wiki/Hewlett-Packard_Voyager_series

use bigdecimal::{
    BigDecimal,
    FromPrimitive,
    ToPrimitive,
    Zero,
};
use lazy_static::lazy_static;
use rand::{Rng, thread_rng};
use std::fmt;

use crate::atom::Atom;
use crate::util::factorial;


const FIELD_WIDTH: usize = 6;


// Alias for the numeric data type.
pub type Number = BigDecimal;


/// Underlying implementation of the 4-register stack.
pub type Stack = [Number; 4];


#[derive(Clone, Debug, Default)]
pub(crate) struct Memory {
    last_x: Number,
}


/// Enum used to map registers (X, Y, Z, T) to stack index.
#[derive(Clone, Debug)]
enum Register { X = 0, Y, Z, T }


/// Primary struct backing the HPN engine.
#[derive(Debug)]
pub struct HPN {
    history: Vec<String>,
    stack: Stack,
    memory: Memory,
}


impl HPN {
    /// Constructs new HPN instance, with emtpy tape and 0 in each register.
    #[must_use]
    pub fn new() -> Self {
        HPN {
            history: vec![],
            memory: Memory::default(),
            stack: Stack::default(),
        }
    }

    /// Parses and evaluates the given string, applying each change in turn.
    pub fn evaluate(&mut self, line: &str) {
        Atom::tokenize(line).iter()
            .for_each(|atom| self.apply(atom));
    }

    /// Returns the value of the `x` register.
    #[must_use]
    pub fn x(&self) -> &Number {
        &self.stack[Register::X as usize]
    }

    /// Returns the value of the `y` register.
    #[must_use]
    pub fn y(&self) -> &Number {
        &self.stack[Register::Y as usize]
    }

    /// Returns the value of the `z` register.
    #[must_use]
    pub fn z(&self) -> &Number {
        &self.stack[Register::Z as usize]
    }

    /// Returns the value of the `t` register.
    #[must_use]
    pub fn t(&self) -> &Number {
        &self.stack[Register::T as usize]
    }

    /// Returns the accumulated history of operations
    /// performed in this calculator.
    #[must_use]
    pub fn tape(&self) -> &Vec<String> {
        &self.history
    }

    /// Applies an atom to the current stack.
    fn apply(&mut self, atom: &Atom) {
        self.log_operation(Some(atom));

        lazy_static!{
            static ref BIG_E: Number = {
                Number::from_f64(std::f64::consts::E)
                    .expect("should not fail")
            };
            static ref BIG_PI: Number = {
                Number::from_f64(std::f64::consts::PI)
                    .expect("should not fail")
            };
        }

        if atom.saves_last_x() {
            self.memory.last_x = self.x().clone();
        }

        match atom {
            Atom::Abs => self.replace(Register::X, self.x().abs()),
            Atom::Add => {
                let sum = self.y() + self.x();
                self.pop();
                self.replace(Register::X, sum);
            },
            Atom::ChangeSign => self.replace(Register::X, -self.x()),
            Atom::ClearX => self.replace(Register::X, Number::zero()),
            Atom::Div => {
                let (x, y) = (self.x(), self.y());
                if x.is_zero() {
                    self.log_message("Error 0: Cannot divide by zero");
                } else {
                    let dividend = y / x;
                    self.pop();
                    self.replace(Register::X, dividend);
                }
            },
            Atom::Euler => self.push(BIG_E.clone()),
            Atom::Exchange => self.stack.swap(0, 1),
            Atom::Factorial => match factorial(self.x()) {
                Some(n) => { self.replace(Register::X, n); },
                None => self.log_message("Error: failed to narrow X"),
            },
            Atom::IDiv => {
                let x = self.x();
                if x.is_zero() {
                    self.log_message("Error 0: Cannot divide by zero");
                } else {
                    let dividend = self.y() / x;
                    self.pop();
                    self.replace(Register::X, dividend.round(0));
                }
            },
            Atom::LastX => self.push(self.memory.last_x.clone()),
            Atom::Mul => {
                let product = self.y() * self.x();
                self.pop();
                self.replace(Register::X, product);
            },
            Atom::PI => self.push(BIG_PI.clone()),
            Atom::Push => self.push(self.x().clone()),
            Atom::Random => {
                let rnd_f64: f64 = thread_rng().gen();
                match Number::from_f64(rnd_f64) {
                    Some(rnd) => self.push(rnd),
                    None => self.log_message(&format!(
                            "Error: Failed to convert value {:?}", rnd_f64)),
                }
            },
            Atom::Reciprocal => match self.x().clone() {
                x if x.is_zero() =>
                    self.log_message("Error 0: Division by zero"),
                x => self.replace(Register::X, 1 / x),
            },
            Atom::Remainder => {
                let x = self.x();
                if x.is_zero() {
                    self.log_message("Error 0: Cannot divide by zero");
                } else {
                    let remainder = self.y() % x;
                    self.pop();
                    self.replace(Register::X, remainder);
                }
            },
            Atom::Roll => self.stack.rotate_left(1),
            Atom::Sub => {
                let difference = self.y() - self.x();
                self.pop();
                self.replace(Register::X, difference);
            },
            Atom::Value(n) => self.push(n.clone()),
            Atom::BadToken(_) => self.log_message(
                &format!("Error: {:?}", atom)),
        }
    }

    fn log_message(&mut self, message: &str) {
        self.history.push(message.to_owned());
    }

    fn log_operation(&mut self, opt_atom: Option<&Atom>) {
        let mut s = self.to_string();
        if let Some(atom) = opt_atom {
            s.push_str(&format!("  <- {}", atom));
        }
        self.log_message(&s);
    }

    fn pop(&mut self) -> Number {
        let x = self.x().clone();
        self.stack[Register::X as usize] = self.t().clone();
        self.stack.rotate_left(1);
        x
    }

    fn push(&mut self, n: Number) {
        self.stack.rotate_right(1);
        self.replace(Register::X, n);
    }

    fn replace(&mut self, reg: Register, value: Number) {
        self.stack[reg as usize] = value;
    }
}


impl Default for HPN {
    fn default() -> Self {
        HPN::new()
    }
}

impl fmt::Display for HPN {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "t: {t:<w$} | z: {z:<w$} | y: {y:<w$} | x: {x:<w$}", w=FIELD_WIDTH,
            x=self.x(), y=self.y(), z=self.z(), t=self.t())
    }
}

/// Constructs an HPN instance and applies tokens contained in the expression.
impl From<&str> for HPN {
    fn from(expr: &str) -> Self {
        let mut hp = HPN::new();
        hp.evaluate(expr);
        hp
    }
}

/// Constructs an HPN instance with the given initial stack.
impl From<[f64; 4]> for HPN {
    fn from(values: [f64; 4]) -> HPN {
        let stack: Stack = values.map(|n|
                Number::from_f64(n).unwrap_or_else(Number::zero));
        HPN::from(stack)
    }
}

/// Constructs an HPN instance with the given initial stack.
impl From<[i32; 4]> for HPN {
    fn from(values: [i32; 4]) -> HPN {
        let stack: Stack = values.map(|n|
                Number::from_i32(n).unwrap_or_else(Number::zero));
        HPN::from(stack)
    }
}

/// Constructs an HPN instance with the given initial stack.
impl From<[Number; 4]> for HPN {
    fn from(stack: Stack) -> HPN {
        let mut hp = HPN { stack, ..HPN::new() };
        hp.log_operation(None);
        hp
    }
}

impl TryFrom<&HPN> for [f64; 4] {
    type Error = &'static str;

    fn try_from(hp: &HPN) -> Result<Self, Self::Error> {
        hp.stack.iter()
            .enumerate()
            .try_fold([0.0, 0.0, 0.0, 0.0], |mut acc, (i, d)|
                Some({ acc[i] = d.to_f64()?; acc }))
            .ok_or("conversion failed")
    }
}

impl TryFrom<&HPN> for [i32; 4] {
    type Error = &'static str;

    fn try_from(hp: &HPN) -> Result<Self, Self::Error> {
        hp.stack.iter()
            .enumerate()
            .try_fold([0, 0, 0, 0], |mut acc, (i, d)|
                Some({ acc[i] = d.to_i32()?; acc }))
            .ok_or("conversion failed")
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;
    use bigdecimal::{
        One,
        Zero,
        ToPrimitive,
    };

    use super::*;

    #[test]
    fn test_returns_stack_set() {
        let hp = HPN::from([2, 3, 5, 8]);
        assert_eq!(Some(2), hp.x().to_i32());
        assert_eq!(Some(3), hp.y().to_i32());
        assert_eq!(Some(5), hp.z().to_i32());
        assert_eq!(Some(8), hp.t().to_i32());
    }

    #[test]
    fn test_returns_stack_unset() {
        let hp = HPN::new();
        let zero = Number::zero();
        assert_eq!(&zero, hp.x());
        assert_eq!(&zero, hp.y());
        assert_eq!(&zero, hp.z());
        assert_eq!(&zero, hp.t());
    }

    #[test]
    fn test_invalid_token() {
        let hp = HPN::from("IAmBad");
        dbg!(&hp);
        assert!(hp.tape().last().unwrap().contains("Error"));
    }

    #[test]
    fn test_abs() {
        let hp = HPN::from("3 5 - abs");
        assert_eq!(&Number::from(2), hp.x());
    }

    #[test]
    fn test_add() {
        let hp = HPN::from("2 3 +");
        assert_eq!(&Number::from(5), hp.x());
    }

    #[test]
    fn test_change_sign() {
        let hp = HPN::from("3 chs");
        assert_eq!(&Number::from(-3), hp.x());

        let hp = HPN::from("-7 chs");
        assert_eq!(&Number::from(7), hp.x());
    }

    #[test]
    fn test_clear_x() {
        let hp = HPN::from("2 3 5 + clx");
        assert_eq!(Ok([0, 2, 0, 0]), <[i32; 4]>::try_from(&hp));
    }

    #[test]
    fn test_div() {
        let hp = HPN::from("1.2 0.5 /");
        assert_eq!(&Number::from_str("2.4").unwrap(), hp.x());
    }

    #[test]
    fn test_div_by_zero() {
        let hp = HPN::from("3 0 /");
        let tape = &hp.tape();
        dbg!(&hp);
        dbg!(&tape);
        assert!(tape.last().unwrap().starts_with("Error 0"));
        assert_eq!(hp.y().to_i32(), Some(3));
        assert_eq!(hp.x().to_i32(), Some(0));
    }

    #[test]
    fn test_euler() {
        let hp = HPN::from("e");
        assert_eq!(Some(std::f64::consts::E), hp.x().to_f64());
    }

    #[test]
    fn test_exchange() {
        let hp = HPN::from("2 3 x<>y");
        assert_eq!(&Number::from(2), hp.x());
        assert_eq!(&Number::from(3), hp.y());
    }

    #[test]
    fn test_factorial_excl() {
        assert_eq!(&Number::from(39_916_800), HPN::from("11 n!").x());
    }

    #[test]
    fn test_idiv() {
        let hp = HPN::from("1.2 0.5 //");
        assert_eq!(&Number::from(2), hp.x());
    }

    #[test]
    fn test_idiv_by_zero() {
        let hp = HPN::from("3 0 //");
        let tape = &hp.tape();
        dbg!(&hp);
        dbg!(&tape);
        assert!(tape.last().unwrap().starts_with("Error 0"));
        assert_eq!(hp.y().to_i32(), Some(3));
        assert_eq!(hp.x().to_i32(), Some(0));
    }

    #[test]
    fn test_inv_x() {
        let hp = HPN::from("2 1/x");
        assert_eq!(Some(0.5), hp.x().to_f64());
    }

    #[test]
    fn test_last_x() {
        let hp = HPN::from("2 3 * lstx");
        assert_eq!(Ok([3, 6, 0, 0]), <[i32; 4]>::try_from(&hp));
    }

    #[test]
    fn test_mul() {
        let hp = HPN::from("2 3 *");
        assert_eq!(&Number::from(6), hp.x());
    }

    #[test]
    fn test_pi() {
        let hp = HPN::from("pi");
        assert_eq!(Some(std::f64::consts::PI), hp.x().to_f64());
    }

    #[test]
    fn test_push() {
        let hp = HPN::from("2 push");
        assert_eq!(Some(2), hp.x().to_i32());
        assert_eq!(Some(2), hp.y().to_i32());
    }

    #[test]
    fn test_random() {
        let mut hp = HPN::new();
        for _ in 0..4 {
            hp.apply(&Atom::Random);
            let rnd = hp.x();
            assert!(rnd >= &Number::zero() && rnd < &Number::one());
        }
    }

    #[test]
    fn test_remainder() {
        let hp = HPN::from("12 7 rmd");
        assert_eq!(Some(5.0), hp.x().to_f64());
    }

    #[test]
    fn test_roll() {
        let hp = HPN::from("2 3 5 8 roll");
        let expected = [5, 3, 2, 8].map(Number::from);
        assert_eq!(expected, hp.stack);
    }

    #[test]
    fn test_sub() {
        let hp = HPN::from("2 3 -");
        assert_eq!(&Number::from(-1), hp.x());
    }

    #[test]
    fn test_celsius_to_fahrenheit() {
        let result = HPN::from("100 9 * 5 / 32 +").x().to_i32();
        assert_eq!(Some(212), result);
    }

    #[test]
    fn test_fahrenheit_to_celsius() {
        let result = HPN::from("212 32 - 5 * 9 /").x().to_i32();
        assert_eq!(Some(100), result);
    }

    #[test]
    fn test_show_your_work() {
        let hp = HPN::from("100 9 * 5 / 32 +");
        // let expected = vec![
        //     "t: 0    z: 0    y: 0    x: 0     <- 100",
        //     "t: 0    z: 0    y: 0    x: 100   <- 9",
        //     "t: 0    z: 0    y: 100  x: 9     <- Mul",
        //     "t: 0    z: 0    y: 0    x: 900   <- 5",
        //     "t: 0    z: 0    y: 900  x: 5     <- Div",
        //     "t: 0    z: 0    y: 0    x: 180   <- 32",
        //     "t: 0    z: 0    y: 180  x: 32    <- Add",
        //     "t: 0    z: 0    y: 0    x: 212",
        // ];
        dbg!(&hp);
        dbg!(hp.tape());
        // for (i, line) in hp.tape().iter().enumerate() {
        //     assert_eq!(expected[i], line);
        // }
    }

    #[test]
    fn test_sample_stack_buster() {
        let mut hp = HPN::from("2 3 5 8 13");
        assert_eq!([13, 8, 5, 3], <[i32;4]>::try_from(&hp).unwrap());
        hp.evaluate("- + 1 / /");
        assert_eq!([0, 3, 3, 3], <[i32;4]>::try_from(&hp).unwrap());
    }

    #[test]
    fn test_stack_backfills_with_t() {
        let mut hp = HPN::from("2 3 5 8");
        assert_eq!(Some(2), hp.t().to_i32());
        hp.apply(&Atom::Add);
        assert_eq!(Some(2), hp.t().to_i32());
        hp.apply(&Atom::Add);
        assert_eq!(Some(2), hp.t().to_i32());
        hp.apply(&Atom::Add);
        assert_eq!(Some(2), hp.t().to_i32());
        hp.apply(&Atom::Mul);
    }

    #[test]
    fn test_hpn_to_array_f64() {
        let hp = HPN::from([1.0, 2.0, 4.0, 8.0]);
        let expected = [1.0, 2.0, 4.0, 8.0];

        let result = <[f64; 4]>::try_from(&hp).unwrap();
        for (i, n) in expected.iter().enumerate() {
            assert!((*n - result[i]).abs() < std::f64::EPSILON);
        }
    }

    #[test]
    fn test_hpn_to_array_i32() {
        let hp = HPN::from("2 3 5 8 13 push");
        let expected = [13, 13, 8, 5];
        let result = <[i32; 4]>::try_from(&hp).unwrap();
        assert_eq!(expected, result);
    }

    #[ignore]
    #[test]
    fn test_output() {
        let hp = HPN::from("100 9 * 5 / 32 +");
        dbg!(&hp);
        panic!()
    }
}
