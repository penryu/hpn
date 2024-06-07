//! Simple interactive calculator.
//!
//! Enter an expression to evaluate it.
//!
//! Calculator state carries across prompts.
//!
//! Execution stops on EOF (^D).

#![warn(clippy::pedantic)]
#![deny(clippy::all)]
#![deny(missing_docs)]

use std::env;
use std::io::{stdin, stdout, Write};

use hpn::prelude::*;

fn eval_print(hpnc: &mut HPN, expr: &str) {
    hpnc.evaluate(expr);
    hpnc.tape().for_each(|line| println!("{line}"));
    println!("=> {}", hpnc.x());
    hpnc.clear_tape();
}

fn read(message: &str) -> Option<String> {
    print!("{message}");
    stdout().flush().expect("failed to flush stdout");

    let mut buffer = String::new();
    match stdin().read_line(&mut buffer) {
        Ok(0) | Err(_) => None,
        Ok(_) => Some(buffer.trim_end().to_owned()),
    }
}

fn main() {
    let mut hp = HPN::default();
    let args = env::args().skip(1);

    match &args.collect::<Vec<_>>()[..] {
        [] => {
            println!("{}", HPN::version());

            while let Some(expr) = read("> ") {
                eval_print(&mut hp, &expr);
            }
        }
        expr => {
            eval_print(&mut hp, &expr.join(" "));
        }
    }
}
