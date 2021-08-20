use std::collections::HashSet;
use std::fs;
use std::hash::Hash;

use crate::core::symbols::{Expression, Literal};
use crate::core::symbols::Type;

mod parser;
mod core;
mod mathsymbols;

extern crate pest;
#[macro_use]
extern crate pest_derive;

fn main() {
    println!("Hello, world!");

    let unparsed_file = fs::read_to_string("test2.txt").expect("cannot read file");

    let (context, expressions) = parser::parser::parse_file(&unparsed_file);

    println!("===============================\nliterals\n===============================\n");
    for item in context.iter() {
        println!("{:?}", item);
    }

    println!("------------------------------------------------------------------------");

    println!("===============================\nexpressions\n===============================\n");
    for item in expressions.iter() {
        println!("{:?}", item);
    }
}
