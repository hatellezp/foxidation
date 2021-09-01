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
use unicode_segmentation::UnicodeSegmentation;
use pad::PadStr;

// colors in the terminal

fn main() {

    println!("===============================================================");
    println!("= Welcome to the revolutionary foxidation (under development) =");
    println!("= The next generation first order logic reasoner              =");
    println!("===============================================================");
    println!("\n\n");

    let args = Cli::from_args();

    let filename_path: std::path::PathBuf = args.filename_path;

    let filename = filename_path.to_str().unwrap();

    let unparsed_file = fs::read_to_string(filename).expect("cannot read file");

    let (context, expressions) = parser::parser::parse_file(&unparsed_file);


    if args.bool_sat {
        for item in expressions.iter() {
            if item.is_pure_propositional() {
                if args.silent {
                    let sat_result = item.pure_propositional_satisfiability_naive();

                    if sat_result.is_none() {
                        panic!("error during satisfiability test for expression: {}", item);
                    }

                    let phrase_length = ("is satisfiable?: false".graphemes(true).count()).max(item.printing_length() + "expression: ".graphemes(true).count());

                    let line: String = vec!["-"; phrase_length + 2].join("");

                    println!("{}", &line);
                    println!("| expression: {}\n| is satisfiable?: {}", item, sat_result.unwrap());
                    println!("{}", &line);

                } else {

                    let item_pure = item;

                    let sat_result = item_pure.pure_propositional_satisfiability_naive().unwrap(); //_or(false);
                    let tau_result = item_pure.pure_propositional_tautology_naive().unwrap(); //_or(false);
                    let unsat_result = item_pure
                        .pure_propositional_unsatisfiability_naive()
                        .unwrap(); //_or(false);


                    println!("expression: {}", item_pure);

                    println!("{}", item_pure.pure_propositional_string_truth_table());


                    let overview_length = "| is satisfiable: false".graphemes(true).count();

                    let mut satis = format!("| is satisfiable?: {}", sat_result).pad_to_width(overview_length);
                    satis.push_str(" |");

                    let mut tauto = format!("| is satisfiable?: {}", sat_result).pad_to_width(overview_length);
                    tauto.push_str(" |");

                    let mut unsat = format!("| is satisfiable?: {}", sat_result).pad_to_width(overview_length);
                    unsat.push_str(" |");

                    println!("-------------------------");
                    println!("{}", satis);
                    println!("{}", tauto);
                    println!("{}", unsat);
                    println!("-------------------------");

                    println!("\n");
                }
            }
        }
    } else {
        println!("no task demanded, exiting")
    }

}
