use std::fs;

use crate::parser::cli::Cli;

use intbits::Bits;

mod core;
mod mathsymbols;
mod parser;

extern crate pest;
#[macro_use]
extern crate pest_derive;

// for cli interface, need to import it so the interface module works
use structopt::StructOpt;
use crate::core::filter::Filter;

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
            println!("===========================================================================");


            println!(
                "{}, is pure propositional: {}",
                item,
                item.is_pure_propositional()
            );

            let atoms = item.atoms();

            if atoms.is_some() {
                println!("  -----");
                println!("  atoms");
                for inner_item in atoms.unwrap().iter() {
                    println!("  - {}", inner_item);
                }
                println!("  -----");
            }

            let sub_exprs = item.sub_expressions();

            println!("  ---------------");
            println!("  sub_expressions");
            for inner_item in sub_exprs {
                println!("  {}", inner_item);
            }
            println!("  ---------------");

            if item.is_pure_propositional() {
                println!("    pure: {}", item.to_pure_propositional().unwrap());
            }
        }
    }


   let mut fil = Filter::new(5);

    while !fil.is_done() {
        println!("{}: {:?}", fil.filter_index(), fil.filter());

        fil.next();
    }
}
