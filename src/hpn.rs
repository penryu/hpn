
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

use std::fmt;

use bigdecimal::{
    BigDecimal,
    FromPrimitive,
    Zero,
};
use lazy_static::lazy_static;
use rand::{Rng, thread_rng};

use crate::atom::Atom;
use crate::util::factorial;


/// Underlying implementation of the 4-register stack.
pub type Registers = [BigDecimal; 4];

/// Simple sequence of actions applied to an HPN instance, similar to tape
/// output on electronic calculators.
pub type Tape = Vec<String>;

/// Enum used to map registers (X, Y, Z, T) to index into the stack.
#[derive(Clone, Debug)]
pub enum Register {
    /// `x` register.
    X,
    /// `y` register.
    Y,
    /// `z` register.
    Z,
    /// `t` register.
    T,
}


/// Primary struct backing the HPN engine.
#[derive(Debug, Default)]
pub struct HPN {
    regs: Registers,
    tape: Tape,
}

impl HPN {
    /// Constructs new HPN instance, with emtpy tape and 0 in each register.
    #[must_use]
    pub fn new() -> Self {
        HPN {
            tape: vec![],
            regs: Registers::default(),
        }
    }

    /// Parses and evaluates the given string, applying each change in turn.
    pub fn evaluate(&mut self, line: &str) {
        Atom::tokenize(line).iter()
            .for_each(|atom| self.apply(atom));
    }

    /// Applies an atom to the current stack.
    fn apply(&mut self, atom: &Atom) {
        self.log(format!("{}   <- {}", self.to_string(), &atom));

        lazy_static!{
            static ref BIG_E: BigDecimal = {
                BigDecimal::from_f64(std::f64::consts::E)
                    .expect("should not fail")
            };
            static ref BIG_PI: BigDecimal = {
                BigDecimal::from_f64(std::f64::consts::PI)
                    .expect("should not fail")
            };
        }

        match atom {
            Atom::Abs => self.replace(Register::X, self.x().abs()),
            Atom::Add => {
                let sum = self.y() + self.x();
                self.pop();
                self.replace(Register::X, sum);
            },
            Atom::ChangeSign => self.replace(Register::X, -self.x()),
            Atom::Div => {
                let (x, y) = (self.x(), self.y());
                if x.is_zero() {
                    self.log("Error 0: Cannot divide by zero".to_owned());
                } else {
                    let dividend = y / x;
                    self.pop();
                    self.replace(Register::X, dividend);
                }
            },
            Atom::Euler => self.push(BIG_E.clone()),
            Atom::Exchange => self.regs.swap(0, 1),
            Atom::Factorial => match factorial(&self.x()) {
                Some(n) => { self.replace(Register::X, n); },
                None => self.log("Error: failed to narrow X".to_owned()),
            },
            Atom::IDiv => {
                let x = self.x();
                if x.is_zero() {
                    self.log("Error 0: Cannot divide by zero".to_owned());
                } else {
                    let dividend = self.y() / x;
                    self.pop();
                    self.replace(Register::X, dividend.round(0));
                }
            },
            Atom::InvX => {
                let x = self.x();
                if x.is_zero() {
                    self.log("Error 0: Cannot divide by zero".to_owned());
                } else {
                    self.replace(Register::X, 1 / x);
                }
            },
            Atom::Mul => {
                let product = self.y() * self.x();
                self.pop();
                self.replace(Register::X, product);
            },
            Atom::PI => self.push(BIG_PI.clone()),
            Atom::Push => self.push(self.x()),
            Atom::Random => {
                let rnd_f64: f64 = thread_rng().gen();
                match BigDecimal::from_f64(rnd_f64) {
                    Some(rnd) => self.push(rnd),
                    None => self.log(format!(
                            "Error: Failed to convert value {:?}", rnd_f64)),
                }
            },
            Atom::Remainder => {
                let x = self.x();
                if x.is_zero() {
                    self.log("Error 0: Cannot divide by zero".to_owned());
                } else {
                    let remainder = self.y() % x;
                    self.pop();
                    self.replace(Register::X, remainder);
                }
            },
            Atom::Sub => {
                let difference = self.y() - self.x();
                self.pop();
                self.replace(Register::X, difference);
            },
            Atom::Value(n) => self.push(n.clone()),
            Atom::BadToken(_) => self.log(format!("Error: {:?}", atom)),
        }
    }

    /// Returns the value of the `x` register.
    #[must_use]
    pub fn x(&self) -> BigDecimal {
        self.regs[Register::X as usize].clone()
    }

    /// Returns the value of the `y` register.
    #[must_use]
    pub fn y(&self) -> BigDecimal {
        self.regs[Register::Y as usize].clone()
    }

    /// Returns the value of the `z` register.
    #[must_use]
    pub fn z(&self) -> BigDecimal {
        self.regs[Register::Z as usize].clone()
    }

    /// Returns the value of the `t` register.
    #[must_use]
    pub fn t(&self) -> BigDecimal {
        self.regs[Register::T as usize].clone()
    }

    /// Pops the `x` register from the stack, backfilling with the contentx of
    /// the `t` register.
    pub fn pop(&mut self) -> BigDecimal {
        let x = self.x();
        self.regs[Register::X as usize] = self.t();
        self.regs.rotate_left(1);
        x
    }

    /// Pushes the value onto the stack, discarding the current value of `t`.
    pub fn push(&mut self, n: BigDecimal) {
        self.regs.rotate_right(1);
        self.replace(Register::X, n);
    }

    /// Adds the given message to the ticker tape history of the calculator.
    fn log(&mut self, message: String) {
        self.tape.push(message);
    }

    /// Replaces the value of the named register with the passed value.
    pub fn replace(&mut self, reg: Register, value: BigDecimal) {
        self.regs[reg as usize] = value;
    }
}

/// Constructing an HPN instance and applying each of the tokens parsed in the
/// given expression.
///
/// HPN objects can be further manipulated after being returned, either manually
/// or via the `evaluate()` method.
impl From<&str> for HPN {
    fn from(expr: &str) -> HPN {
        let mut hp = HPN::new();
        hp.evaluate(expr);
        hp
    }
}

impl From<[f64; 4]> for HPN {
    fn from(values: [f64; 4]) -> HPN {
        let regs: Registers = values.map(|n|
                BigDecimal::from_f64(n).unwrap_or_else(BigDecimal::zero));
        HPN::from(regs)
    }
}

impl From<[i32; 4]> for HPN {
    fn from(values: [i32; 4]) -> HPN {
        let regs: Registers = values.map(|n|
                BigDecimal::from_i32(n).unwrap_or_else(BigDecimal::zero));
        HPN::from(regs)
    }
}

impl From<[BigDecimal; 4]> for HPN {
    fn from(regs: Registers) -> HPN {
        let mut hp = HPN {
            tape: vec![],
            regs,
        };
        hp.tape.push(hp.to_string());
        hp
    }
}

impl fmt::Display for HPN {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "t: {:<3}  z: {:<3}  y: {:<3}  x: {:<3}",
            self.t(), self.z(), self.y(), self.x())
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
    fn test_returns_registers_set() {
        let hp = HPN::from([2, 3, 5, 8]);
        assert_eq!(Some(2), hp.x().to_i32());
        assert_eq!(Some(3), hp.y().to_i32());
        assert_eq!(Some(5), hp.z().to_i32());
        assert_eq!(Some(8), hp.t().to_i32());
    }

    #[test]
    fn test_returns_registers_unset() {
        let hp = HPN::new();
        let zero = BigDecimal::zero();
        assert_eq!(zero, hp.x());
        assert_eq!(zero, hp.y());
        assert_eq!(zero, hp.z());
        assert_eq!(zero, hp.t());
    }

    #[test]
    fn test_invalid_token() {
        let hp = HPN::from("IAmBad");
        dbg!(&hp);
        assert!(hp.tape.last().unwrap().contains("Error"));
    }

    #[test]
    fn test_atom_abs() {
        let hp = HPN::from("3 5 - abs");
        assert_eq!(BigDecimal::from(2), hp.x());
    }

    #[test]
    fn test_atom_add() {
        let hp = HPN::from("2 3 +");
        assert_eq!(BigDecimal::from(5), hp.x());
    }

    #[test]
    fn test_atom_change_sign() {
        let hp = HPN::from("3 chs");
        assert_eq!(BigDecimal::from(-3), hp.x());

        let hp = HPN::from("-7 chs");
        assert_eq!(BigDecimal::from(7), hp.x());
    }

    #[test]
    fn test_atom_div() {
        let hp = HPN::from("1.2 0.5 /");
        assert_eq!(BigDecimal::from_str("2.4").unwrap(), hp.x());
    }

    #[test]
    fn test_atom_div_by_zero() {
        let hp = HPN::from("3 0 /");
        let tape = &hp.tape;
        dbg!(&hp);
        assert!(tape.last().unwrap().starts_with("Error 0"));
        assert_eq!(hp.y().to_i32(), Some(3));
        assert_eq!(hp.x().to_i32(), Some(0));
    }

    #[test]
    fn test_atom_euler() {
        let hp = HPN::from("e");
        assert_eq!(Some(std::f64::consts::E), hp.x().to_f64());
    }

    #[test]
    fn test_atom_exchange() {
        let hp = HPN::from("2 3 exch");
        assert_eq!(BigDecimal::from(2), hp.x());
        assert_eq!(BigDecimal::from(3), hp.y());
    }

    #[test]
    fn test_atom_factorial_excl() {
        let hp = HPN::from("11 !");
        assert_eq!(BigDecimal::from(39_916_800), hp.x());
    }

    #[test]
    fn test_atom_factorial_n_excl() {
        let hp = HPN::from("11 n!");
        assert_eq!(BigDecimal::from(39_916_800), hp.x());
    }

    #[test]
    fn test_atom_factorial_big() {
        let hp = HPN::from("253 !");
        let expected = "51734609926400789218043308997295274695423561272066399607484636163134302903130041238314437828111213744932542876617296316904840977852744354743364096544589631199800576352102197345093407901685444661637384445171444589249826159309289810622514481898739824349965672944938199095203108731528570965561754517676626034976542767771987626709597099937322577683908278497279328468806763572731103332796695726049211496386749680456221513530752014396144012492800000000000000000000000000000000000000000000000000000000000000";
        assert_eq!(BigDecimal::from_str(expected).unwrap(), hp.x());
    }

    #[test]
    fn test_atom_factorial_bigger() {
        let hp = HPN::from("1001 !");
        let expected = "402789647337170867317246136356926989705094239074925347176343710340368450911027649612636252695456374205280468598807393254690298539867803367460225153499614535588421928591160833678742451354915921252299285456946271396995850437959540645019696372741142787347450281325324373824456300226871609431497826989489109522725791691167945698509282421538632966523376679891823696900982075223188279465194065489111498586522997573307838057934994706212934291477882221464914058745808179795130018969175605739824237247684512790169648013778158661520384916357285547219660337504067910087936301580874662367543921288988208261944834178369169805682489420504038334529389177845089679546075023305854006141256288633820079940395329251563788399404652902154519302928365169452383531030755684578503851488154092323576150311569325891190105926118761607100286827930472944913272420825078912158741589850136017030887975452922434889688775883386977825215904423682478943313806072144097432418695807412571292308739802481089407002523955080148184062810447564594783139830113821372260474145316521647368313934670783858482781506915288378941348078689691815657785305896912277993200639858696294199549107738635599538328374931258525869323348477334798827676297868823693023377418942304272267800509765805435653787530370118261219994752588866451072715583785495394684524593296728611334955079882857173250037068541860372512693170819259309411027837176612444692649174536429745421086287708588130082168792750697158901737130221751430550976429258055277255676893874108456870904122902259417224707137723406125811549952159629766771063079472679280213882978523785424760309678138268708239764925768714349554665438389311198715040908077757086900159389712443987670244241787904585093011546861502058550090914877900852701619648229332192401075747543562989953271508977501771085759521631427816116191761031257454497039673414248149210836002497114107565960458576525212556159634975715552638678172137468172843066451093984443636560722213668172225585711566558134467392654185460222589723312097599987253417831473939565071006344352518096564427781204200068323913056897090916602712260306869786107237077572445866572945760977721639408338430009976028970539150822336553856613962747814621747092348996915755983464741082000337526945990059365493439921937093368896754791416759604324895514660325913157843796039917819613717350380997781225472000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000";
        assert_eq!(
            BigDecimal::from_str(expected).unwrap(),
            hp.x());
    }

    #[test]
    fn test_atom_idiv() {
        let hp = HPN::from("1.2 0.5 //");
        assert_eq!(BigDecimal::from(2), hp.x());
    }

    #[test]
    fn test_atom_idiv_by_zero() {
        let hp = HPN::from("3 0 //");
        let tape = &hp.tape;
        dbg!(&hp);
        assert!(tape.last().unwrap().starts_with("Error 0"));
        assert_eq!(hp.y().to_i32(), Some(3));
        assert_eq!(hp.x().to_i32(), Some(0));
    }

    #[test]
    fn test_atom_inv_x() {
        let hp = HPN::from("2 1/x");
        assert_eq!(Some(0.5), hp.x().to_f64());
    }

    #[test]
    fn test_atom_mul() {
        let hp = HPN::from("2 3 *");
        assert_eq!(BigDecimal::from(6), hp.x());
    }

    #[test]
    fn test_atom_pi() {
        let hp = HPN::from("pi");
        assert_eq!(Some(std::f64::consts::PI), hp.x().to_f64());
    }

    #[test]
    fn test_atom_push() {
        let hp = HPN::from("2 push");
        assert_eq!(Some(2), hp.x().to_i32());
        assert_eq!(Some(2), hp.y().to_i32());
    }

    #[test]
    fn test_atom_random() {
        let mut hp = HPN::new();
        for _ in 0..4 {
            hp.apply(&Atom::Random);
            let rnd = hp.x();
            assert!(rnd >= BigDecimal::zero() && rnd < BigDecimal::one());
        }
    }

    #[test]
    fn test_atom_remainder() {
        let hp = HPN::from("12 7 rmd");
        assert_eq!(Some(5.0), hp.x().to_f64());
    }

    #[test]
    fn test_atom_sub() {
        let hp = HPN::from("2 3 -");
        assert_eq!(BigDecimal::from(-1), hp.x());
    }

    #[test]
    fn test_celsius_to_fahrenheit() {
        let hp = HPN::from("100 9 * 5 / 32 +");
        assert_eq!(Some(212), hp.x().to_i32());
    }

    #[test]
    fn test_fahrenheit_to_celsius() {
        let hp = HPN::from("212 32 - 5 * 9 /");
        assert_eq!(Some(100), hp.x().to_i32());
    }

    #[test]
    fn test_formats_stack() {
        let values = [2, 3, 5, 8].map(BigDecimal::from);
        let mut hp = HPN::from(values);
        assert_eq!(hp.to_string(), "t: 8    z: 5    y: 3    x: 2  ");
        hp.pop();
        assert_eq!(hp.to_string(), "t: 8    z: 8    y: 5    x: 3  ");
        hp.pop();
        assert_eq!(hp.to_string(), "t: 8    z: 8    y: 8    x: 5  ");
        hp.pop();
        assert_eq!(hp.to_string(), "t: 8    z: 8    y: 8    x: 8  ");
        hp.pop();
        assert_eq!(hp.to_string(), "t: 8    z: 8    y: 8    x: 8  ");
        hp.pop();
        assert_eq!(hp.to_string(), "t: 8    z: 8    y: 8    x: 8  ");
    }

    #[test]
    fn test_show_your_work() {
        let hp = HPN::from("100 9 * 5 / 32 +");
        let expected = vec![
            "t: 0    z: 0    y: 0    x: 0     <- 100",
            "t: 0    z: 0    y: 0    x: 100   <- 9",
            "t: 0    z: 0    y: 100  x: 9     <- Mul",
            "t: 0    z: 0    y: 0    x: 900   <- 5",
            "t: 0    z: 0    y: 900  x: 5     <- Div",
            "t: 0    z: 0    y: 0    x: 180   <- 32",
            "t: 0    z: 0    y: 180  x: 32    <- Add",
            "t: 0    z: 0    y: 0    x: 212",
        ];
        for (i, line) in hp.tape.iter().enumerate() {
            assert_eq!(expected[i], line);
        }
    }

    #[test]
    fn test_sample_stack_buster() {
        let hp = HPN::from("2 3 5 8 13 - + 1 / /");
        let expected = vec![
            "t: 0    z: 0    y: 0    x: 0     <- 2",
            "t: 0    z: 0    y: 0    x: 2     <- 3",
            "t: 0    z: 0    y: 2    x: 3     <- 5",
            "t: 0    z: 2    y: 3    x: 5     <- 8",
            "t: 2    z: 3    y: 5    x: 8     <- 13",
            "t: 3    z: 5    y: 8    x: 13    <- Sub",
            "t: 3    z: 3    y: 5    x: -5    <- Add",
            "t: 3    z: 3    y: 3    x: 0     <- 1",
            "t: 3    z: 3    y: 0    x: 1     <- Div",
            "t: 3    z: 3    y: 3    x: 0     <- Div",
            "Error 0: Cannot divide by zero",
        ];
        for (i, line) in hp.tape.iter().enumerate() {
            assert_eq!(expected[i], line);
        }
    }

    #[test]
    fn test_stack_backfills_zero() {
        let mut hp = HPN::from("2 +");
        assert_eq!(Some(2), hp.x().to_i32());
        hp.apply(&Atom::Add);
        assert_eq!(Some(2), hp.x().to_i32());
        hp.apply(&Atom::Add);
        assert_eq!(Some(2), hp.x().to_i32());
        hp.apply(&Atom::Add);
        assert_eq!(Some(2), hp.x().to_i32());
        hp.apply(&Atom::Mul);
        assert_eq!(Some(0), hp.x().to_i32());
        hp.apply(&Atom::Add);
        assert_eq!(Some(0), hp.x().to_i32());
    }
}
