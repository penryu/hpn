// Copyright 2023 Tim Hammerquist
//
// Licensed under the [MIT license](https://opensource.org/licenses/MIT).
// This file may not be copied, modified, or distributed except according to those terms.

use std::fmt::{self, Write};
use std::sync::OnceLock;

use crate::atom::Atom;
use crate::prelude::{FromPrimitive, Number, Rng, ToPrimitive, Zero};
use crate::util::{c_to_f, f_to_c, factorial, help, y_pow_x};

const PRECISION: usize = 3;
const WIDTH: usize = 8;

static BIG_E: OnceLock<Number> = OnceLock::new();
static BIG_PI: OnceLock<Number> = OnceLock::new();

/// Underlying implementation of the 4-register stack.
pub type Stack = [Number; 4];

#[derive(Clone, Debug, Default)]
pub(crate) struct Memory {
    last_x: Number,
}

/// Enum used to map registers (X, Y, Z, T) to stack index.
#[derive(Clone, Debug)]
enum Register {
    X = 0,
    Y,
    Z,
    T,
}

/// Stores history of operations, like paper tape
#[derive(Clone, Debug, Default)]
struct History(Vec<String>);

impl History {
    fn clear(&mut self) {
        self.0.clear();
    }

    fn lines(&self) -> impl Iterator<Item = String> {
        self.0.clone().into_iter()
    }

    fn log(&mut self, message: &str) {
        self.0.push(message.to_owned());
    }
}

impl ToString for History {
    fn to_string(&self) -> String {
        let rows = self.lines().collect::<Vec<_>>();
        rows.join("\n")
    }
}

/// Primary struct backing the HPN engine.
#[derive(Clone, Debug)]
pub struct HPN {
    history: History,
    stack: Stack,
    memory: Memory,
}

impl HPN {
    /// Clears the history for this calculator object. Does not alter the stack or memory.
    pub fn clear_tape(&mut self) {
        self.history.clear();
    }

    /// Parses and evaluates the given string, applying each change in turn.
    /// ```
    /// use hpn::prelude::*;
    /// let mut hp = HPN::default();
    /// hp.evaluate("4 3 2 1");
    /// println!("{hp}");
    /// // Output:
    /// //  0: [ T:    0.000 | Z:    0.000 | Y:    0.000 | X:    0.000 ]  <- 4
    /// //  1: [ T:    0.000 | Z:    0.000 | Y:    0.000 | X:    4.000 ]  <- 3
    /// //  2: [ T:    0.000 | Z:    0.000 | Y:    4.000 | X:    3.000 ]  <- 2
    /// //  3: [ T:    0.000 | Z:    4.000 | Y:    3.000 | X:    2.000 ]  <- 1
    /// //  4: [ T:    4.000 | Z:    3.000 | Y:    2.000 | X:    1.000 ]
    /// ```
    pub fn evaluate(&mut self, line: &str) {
        Atom::tokenize(line)
            .iter()
            .for_each(|atom| self.apply(atom));
    }

    /// Returns the value of the `x` register.
    /// ```
    /// # use hpn::prelude::*;
    /// # let hp = HPN::from("3 2 1 0");
    /// assert_eq!(*hp.x(), Number::zero());
    /// ```
    #[must_use]
    pub fn x(&self) -> &Number {
        &self.stack[Register::X as usize]
    }

    /// Returns the value of the `y` register.
    /// ```
    /// # use hpn::prelude::*;
    /// # let hp = HPN::from("3 2 1 0");
    /// assert_eq!(*hp.y(), Number::one());
    /// ```
    #[must_use]
    pub fn y(&self) -> &Number {
        &self.stack[Register::Y as usize]
    }

    /// Returns the value of the `z` register.
    /// ```
    /// # use hpn::prelude::*;
    /// let hp = HPN::from("3 2 1 0");
    /// assert_eq!(*hp.z(), Number::from(2));
    /// ```
    #[must_use]
    pub fn z(&self) -> &Number {
        &self.stack[Register::Z as usize]
    }

    /// Returns the value of the `t` register.
    /// ```
    /// # use hpn::prelude::*;
    /// let hp = HPN::from("3 2 1 0");
    /// assert_eq!(*hp.t(), Number::from(3));
    /// ```
    #[must_use]
    pub fn t(&self) -> &Number {
        &self.stack[Register::T as usize]
    }

    /// Returns the accumulated history of operations
    /// performed in this calculator as a lazy iterator of `String`s.
    /// ```
    /// # use hpn::prelude::*;
    /// let hp = HPN::from("3 4 7 - +");
    /// hp.tape().for_each(|line| println!("{}", line));
    /// ```
    pub fn tape(&self) -> impl Iterator<Item = String> {
        self.history
            .lines()
            .chain([self.to_string()])
            .enumerate()
            .map(|(i, line)| format!("{i:2}: {line}"))
    }

    /// Applies an atom to the current stack.
    #[allow(clippy::too_many_lines)]
    fn apply(&mut self, atom: &Atom) {
        self.log_operation(Some(atom));

        if matches!(atom, Atom::Help) {
            self.log_message(&help());
            return;
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
            }
            Atom::CToF => self.replace(Register::X, c_to_f(self.x())),
            Atom::ChangeSign => self.replace(Register::X, -self.x()),
            Atom::ClearX => self.replace(Register::X, Number::zero()),
            Atom::Cube => self.replace(Register::X, self.x().cube()),
            Atom::CubeRoot => self.replace(Register::X, self.x().cbrt()),
            Atom::Div => {
                let (x, y) = (self.x(), self.y());
                if x.is_zero() {
                    self.log_message("Error 0: Cannot divide by zero");
                } else {
                    let dividend = y / x;
                    self.pop();
                    self.replace(Register::X, dividend);
                }
            }
            Atom::Euler => self.push(
                BIG_E
                    .get_or_init(|| {
                        Number::from_f64(std::f64::consts::E)
                            .expect("failed to convert f64 to Number")
                    })
                    .clone(),
            ),
            Atom::Exchange => self.stack.swap(0, 1),
            Atom::FToC => self.replace(Register::X, f_to_c(self.x())),
            Atom::Factorial => match factorial(self.x()) {
                Some(n) => {
                    self.replace(Register::X, n);
                }
                None => self.log_message("Error: failed to narrow X"),
            },
            Atom::Help => self.log_message(&help()),
            Atom::IDiv => {
                let x = self.x();
                if x.is_zero() {
                    self.log_message("Error 0: Cannot divide by zero");
                } else {
                    let dividend = self.y() / x;
                    self.pop();
                    self.replace(Register::X, dividend.round(0));
                }
            }
            Atom::LastX => self.push(self.memory.last_x.clone()),
            Atom::Mul => {
                let product = self.y() * self.x();
                self.pop();
                self.replace(Register::X, product);
            }
            Atom::PI => self.push(
                BIG_PI
                    .get_or_init(|| {
                        Number::from_f64(std::f64::consts::PI)
                            .expect("failed to convert f64 to number")
                    })
                    .clone(),
            ),
            Atom::Push => self.push(self.x().clone()),
            Atom::Random => {
                let rnd_f64: f64 = rand::thread_rng().gen();
                match Number::from_f64(rnd_f64) {
                    Some(rnd) => self.push(rnd),
                    None => {
                        self.log_message(&format!("Error: Failed to convert value {rnd_f64:?}"));
                    }
                }
            }
            Atom::Reciprocal => match self.x().clone() {
                x if x.is_zero() => {
                    self.log_message("Error 0: Division by zero");
                }
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
            }
            Atom::Roll => self.stack.rotate_left(1),
            Atom::Square => self.replace(Register::X, self.x().square()),
            Atom::SquareRoot => match self.x().sqrt() {
                Some(result) => self.replace(Register::X, result),
                None => self.log_message("Error 0"),
            },
            Atom::Sub => {
                let difference = self.y() - self.x();
                self.pop();
                self.replace(Register::X, difference);
            }
            Atom::YToX => match y_pow_x(self.y(), self.x()) {
                Some(result) => self.replace(Register::X, result),
                None => self.log_message("Error 0"),
            },
            Atom::Value(n) => self.push(n.clone()),
            Atom::BadToken(_) => {
                self.log_message(&format!("Error: {atom:?}"));
            }
        }
    }

    fn log_message(&mut self, message: &str) {
        self.history.log(message);
    }

    fn log_operation(&mut self, opt_atom: Option<&Atom>) {
        let mut s = self.to_string();
        if let Some(atom) = opt_atom {
            write!(s, "  <- {atom}").unwrap();
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

/// Constructs new HPN instance, with emtpy tape and 0 in each register.
/// ```
/// use hpn::prelude::*;
///
/// let mut hp = HPN::default();
/// ```
impl Default for HPN {
    fn default() -> Self {
        HPN {
            history: History::default(),
            memory: Memory::default(),
            stack: Stack::default(),
        }
    }
}

/// Displays the current state of the stack.
impl fmt::Display for HPN {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "[ T: {t:w$.p$} | Z: {z:w$.p$} | Y: {y:w$.p$} | X: {x:w$.p$} ]",
            w = WIDTH,
            p = PRECISION,
            x = self.x(),
            y = self.y(),
            z = self.z(),
            t = self.t(),
        )
    }
}

/// Constructs an HPN instance and evaluates the expression passed.
impl From<&str> for HPN {
    fn from(expr: &str) -> Self {
        let mut hp = HPN::default();
        hp.evaluate(expr);
        hp
    }
}

/// Constructs an HPN instance with the given initial stack.
impl From<[f64; 4]> for HPN {
    fn from(values: [f64; 4]) -> Self {
        let stack: Stack = values.map(|n| Number::from_f64(n).unwrap_or_else(Number::zero));
        HPN::from(stack)
    }
}

/// Constructs an HPN instance with the given initial stack.
impl From<[i32; 4]> for HPN {
    fn from(values: [i32; 4]) -> Self {
        let stack: Stack = values.map(|n| Number::from_i32(n).unwrap_or_else(Number::zero));
        HPN::from(stack)
    }
}

/// Constructs an HPN instance with the given initial stack.
impl From<[Number; 4]> for HPN {
    fn from(stack: Stack) -> Self {
        let mut hp = Self {
            stack,
            ..HPN::default()
        };
        hp.log_operation(None);
        hp
    }
}

/// Attempts to convert an HPN instance to an [f64; 4].
impl TryFrom<&HPN> for [f64; 4] {
    type Error = &'static str;

    fn try_from(hp: &HPN) -> Result<Self, Self::Error> {
        hp.stack
            .iter()
            .enumerate()
            .try_fold([0.0, 0.0, 0.0, 0.0], |mut acc, (i, d)| {
                Some({
                    acc[i] = d.to_f64()?;
                    acc
                })
            })
            .ok_or("conversion failed")
    }
}

/// Attempts to convert an HPN instance to an [i32; 4].
impl TryFrom<&HPN> for [i32; 4] {
    type Error = &'static str;

    fn try_from(hp: &HPN) -> Result<Self, Self::Error> {
        hp.stack
            .iter()
            .enumerate()
            .try_fold([0, 0, 0, 0], |mut acc, (i, d)| {
                Some({
                    acc[i] = d.to_i32()?;
                    acc
                })
            })
            .ok_or("conversion failed")
    }
}

#[cfg(test)]
mod tests {
    use crate::prelude::{FromStr, One, ToPrimitive, Zero};

    use super::*;

    /*
     * History
     */

    #[test]
    fn history_log() {
        let mut hist = History::default();
        assert!(hist.0.len().is_zero());
        hist.log("message 1");
        hist.log("message 2");
        assert_eq!(2, hist.0.len());
        assert_eq!("message 2", hist.0.last().unwrap());
    }

    #[test]
    fn history_clear() {
        let mut hist = History::default();
        hist.log("message 1");
        hist.log("message 2");
        hist.clear();
        assert_eq!(0, hist.0.len());
    }

    #[test]
    fn history_lines() {
        let mut hist = History::default();
        hist.log("message 1");
        hist.log("message 2");
        let mut lines = hist.lines();
        assert_eq!("message 1", lines.next().unwrap());
        assert_eq!("message 2", lines.next().unwrap());
        assert!(lines.next().is_none());
    }

    #[test]
    fn history_clone() {
        let mut hist1 = History::default();
        hist1.log("message 1");
        hist1.log("message 2");
        let hist2 = hist1.clone();
        hist1.clear();
        assert_eq!(0, hist1.0.len());
        assert_eq!(2, hist2.0.len());
    }

    /*
     * HPN
     */

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
        let hp = HPN::default();
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
        assert!(hp.history.lines().last().unwrap().contains("Error"));
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
    fn test_cube() {
        let hp = HPN::from("2 x^3 1.1 x^3");
        assert_eq!(&Number::from(8), hp.y());
        assert_eq!(&Number::from_str("1.331").unwrap(), hp.x());
    }

    #[test]
    fn test_cube_root() {
        let hp = HPN::from("8 cbrt 1.331 cbrt");
        assert_eq!(&Number::from_i32(2).unwrap(), hp.y());
        assert_eq!(&Number::from_f64(1.1).unwrap(), hp.x());
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
        dbg!(&hp);
        assert!(hp.history.lines().last().unwrap().starts_with("Error 0"));
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
        dbg!(&hp);
        assert!(hp.history.lines().last().unwrap().starts_with("Error 0"));
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
        let mut hp = HPN::default();
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
    fn test_y_pow_x() {
        // floating point
        let hp = HPN::from("1.1 3 y^x");
        assert_eq!(&Number::from_str("1.331").unwrap(), hp.x());
        // (rough) integral
        let hp = HPN::from("2 3 y^x");
        assert_eq!(&Number::from(8), hp.x());
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
    fn test_sample_stack_buster() {
        let mut hp = HPN::from("2 3 5 8 13");
        assert_eq!([13, 8, 5, 3], <[i32; 4]>::try_from(&hp).unwrap());
        hp.evaluate("- + 1 / /");
        assert_eq!([0, 3, 3, 3], <[i32; 4]>::try_from(&hp).unwrap());
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

    /// Used to verify output when run explicitly. Ignored otherwise.
    #[ignore]
    #[test]
    fn test_output() {
        let hp = HPN::from("21 9 * 5 / 32 +");
        dbg!(&hp);
        dbg!(hp.tape().collect::<Vec<_>>());
        dbg!(hp.x());
        hp.tape().for_each(|line| println!("{line}"));
        panic!();
    }
}
