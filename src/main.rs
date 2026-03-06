mod asm6510;
mod error;

use std::{fs::File, path::PathBuf};
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
#[structopt(about = "My Own 65xx assembler and disassembler")]
struct CliOpt {
    /// Execution mode
    #[structopt(subcommand)]
    mode: Option<Mode>,
}

#[derive(Debug, StructOpt)]
enum Mode {
    /// Assemble source to machine code
    Asm {
        /// Source file path
        #[structopt(parse(from_os_str))]
        src: PathBuf,
        /// Binary file path
        #[structopt(short = "o", parse(from_os_str))]
        bin: Option<PathBuf>,
        /// Dump symbol table
        #[structopt(short = "s")]
        dump_symbols: bool,
    },
    /// Disassemble machine code
    Dasm {
        /// Binary file path
        #[structopt(parse(from_os_str))]
        bin: PathBuf,
        /// Start address
        #[structopt(parse(try_from_str = parse_hex))]
        start_addr: u16,
        /// End address
        #[structopt(parse(try_from_str = parse_hex))]
        end_addr: Option<u16>,
    },
}

fn main() {
    let cliopt = CliOpt::from_args();
    let result = match cliopt.mode.unwrap_or(Mode::Console { clock_mhz: 1.0 }) {
        Mode::Asm {
            src,
            bin,
            dump_symbols,
        } => asm6510::assemble_file(src),
        Mode::Dasm {
            start_addr,
            end_addr,
            bin,
        } => asm6510::disassemble_file(start_addr, end_addr, bin),
        Mode::Console { clock_mhz } => Console::start(APP_NAME, clock_mhz * 1e6),
    };
    if let Err(apperr) = result {
        println!("\nerror: {:?}", apperr)
    }

    println!("Hello, world!");
}
