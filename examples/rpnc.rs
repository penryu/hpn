//! Simple interactive calculator.
//!
//! Enter an expression to evaluate it.
//!
//! Calculator state carries across prompts.
//!
//! Execution stops on EOF (^D).

use hpn::prelude::*;
use std::io::{stdin, stdout, Write};

fn prompt(message: &str) -> Option<String> {
    print!("{}", message);
    stdout().flush().expect("failed to flush stdout");

    let mut buffer = String::new();
    match stdin().read_line(&mut buffer) {
        Ok(bytes) if bytes == 0 => None,
        Ok(_) => Some(buffer.trim_end().to_owned()),
        Err(_) => None,
    }
}

fn main() {
    let mut hp = HPN::new();

    while let Some(expr) = prompt("> ") {
        hp.evaluate(&expr);
        hp.tape().for_each(|line| println!("{}", line));
        println!("=> {}", hp.x());
        hp.clear_tape();
    }
}
