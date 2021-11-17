// for cli interface, need to import it so the interface module works
use structopt::StructOpt;

/// The binary dl_lite_r works through an interface of arguments of the
/// form '--argname'.
/// They should be self-explanatory.
#[derive(StructOpt, Debug)]
pub struct Cli {
    #[structopt(
        parse(from_os_str),
        short="fp",
        long="filename",
        help = "path to the file with the model"
    )]
    pub filename_path: std::path::PathBuf,

    #[structopt(
        short,long,
        help="decides the boolean satisfiability of all pure propositional expression in the file"
    )]
    pub bool_sat: bool,

    #[structopt(
        short,long,
        help="more verbose output for each task, in the case of boolean satisfiability it prints the whole truth table"
    )]
    pub silent: bool,
}
