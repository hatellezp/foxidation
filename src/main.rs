
use std::fs;




use crate::parser::cli::Cli;

mod core;
mod mathsymbols;
mod parser;

extern crate pest;
#[macro_use]
extern crate pest_derive;

// for cli interface, need to import it so the interface module works
use structopt::StructOpt;

// colors in the terminal


fn main() {
    println!("Hello, world!");

    let args = Cli::from_args();

    let filename_path_op: Option<std::path::PathBuf> = args.filename_path;

    if let Some(filename_path) = filename_path_op {
        let filename = filename_path.to_str().unwrap();

        let unparsed_file = fs::read_to_string(filename).expect("cannot read file");

        let (context, expressions) = parser::parser::parse_file(&unparsed_file);

        println!("===============================\nliterals\n===============================\n");
        for item in context.iter() {
            println!("{:?}: {}", item, item);
        }

        println!("------------------------------------------------------------------------");

        println!("===============================\nexpressions\n===============================\n");
        for item in expressions.iter() {
            println!(
                "{}, is pure propositional: {}",
                item,
                item.is_pure_propositional()
            );

            if item.is_pure_propositional() {
                println!("    pure: {}", item.to_pure_propositional().unwrap());
            }
        }
    }
}
