//! Simple interactive calculator.
//!
//! Enter an expression to evaluate it.
//!
//! Calculator state carries across prompts.
//!
//! Execution stops on EOF (^D).

use hpn::prelude::*;
use std::env;
use std::io::{stdin, stdout, Write};

fn read(message: &str) -> Option<String> {
    print!("{}", message);
    stdout().flush().expect("failed to flush stdout");

    let mut buffer = String::new();
    match stdin().read_line(&mut buffer) {
        Ok(bytes) if bytes == 0 => None,
        Ok(_) => Some(buffer.trim_end().to_owned()),
        Err(_) => None,
    }
}

fn eval_print(rpnc: &mut HPN, expr: &str) {
    rpnc.evaluate(expr);
    rpnc.tape().for_each(|line| println!("{}", line));
    println!("=> {}", rpnc.x());
    rpnc.clear_tape();
}

fn main() {
    let mut hp = HPN::new();

    let args: Vec<_> = env::args().skip(1).collect();

    match args.len() {
        0 => {
            while let Some(expr) = read("> ") {
                eval_print(&mut hp, &expr);
            }
        }
        _ => {
            eval_print(&mut hp, &args.join(" "));
        }
    }
}
