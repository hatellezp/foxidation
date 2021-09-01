use std::fs;

use crate::parser::cli::Cli;

mod core;
mod mathsymbols;
mod parser;

extern crate pest;
#[macro_use]
extern crate pest_derive;

// for cli interface, need to import it so the interface module works
use crate::core::filter::Filter;
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

        for item in expressions.iter() {
            println!("===========================================================================");

            println!(
                "{} is pure propositional: {}",
                item,
                item.is_pure_propositional()
            );

            if item.is_pure_propositional() {
                println!("{}", item.pure_propositional_string_truth_table());
            }

            if item.is_pure_propositional() {
                let item_pure = item.to_pure_and_push().unwrap();
                println!("    pure: {}", &item_pure);

                let sat_result = item_pure.pure_propositional_satisfiability_naive().unwrap(); //_or(false);
                let tau_result = item_pure.pure_propositional_tautology_naive().unwrap(); //_or(false);
                let unsat_result = item_pure
                    .pure_propositional_unsatisfiability_naive()
                    .unwrap(); //_or(false);

                println!("{}", item_pure.pure_propositional_string_truth_table());

                println!("    is satisfiable?: {}", sat_result);
                println!("    is a tautology?: {}", tau_result);
                println!("    is unsatsifiab?: {}", unsat_result);
            }
        }
    }
}
