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

use hpn::prelude::*;
use std::env;
use std::io::{stdin, stdout, Write};
use std::path::Path;

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

fn print_version(path: &str) {
    let my_name = Path::new(path).file_name().unwrap().to_str().unwrap();
    let version = env!("CARGO_PKG_VERSION");

    println!("{my_name} {version}");
}

fn main() {
    let mut hp = HPN::default();
    let mut args = env::args();
    let bin_path = &args.next().unwrap();

    match &args.collect::<Vec<_>>()[..] {
        [] => {
            print_version(bin_path);

            while let Some(expr) = read("> ") {
                eval_print(&mut hp, &expr);
            }
        }
        expr => {
            eval_print(&mut hp, &expr.join(" "));
        }
    }
}
