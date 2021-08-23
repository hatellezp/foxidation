// for cli interface, need to import it so the interface module works
use structopt::StructOpt;

/// The binary dl_lite_r works through an interface of arguments of the
/// form '--argname'.
/// They should be self-explanatory.
#[derive(StructOpt, Debug)]
pub struct Cli {
    #[structopt(
        parse(from_os_str),
        long = "filename",
        help = "path to the file with the model"
    )]
    pub filename_path: Option<std::path::PathBuf>,
}
