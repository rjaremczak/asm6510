#[macro_use]
extern crate lazy_static;

mod asm6510;

use std::path::PathBuf;
use structopt::StructOpt;
use asm6510::error::AppError;

fn parse_hex(hex: &str) -> Result<u16, AppError> {
    u16::from_str_radix(hex, 16).map_err(|e| AppError::ParseIntError(String::from(hex), e))
}

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
        /// Start address
        #[structopt(parse(try_from_str = parse_hex))]
        start_addr: u16,
        /// End address
        #[structopt(parse(try_from_str = parse_hex))]
        end_addr: Option<u16>,
        /// Binary file path
        #[structopt(parse(from_os_str))]
        bin: PathBuf,
    },
}

fn main() {
    let cliopt = CliOpt::from_args();
    let result = match cliopt.mode.unwrap_or() {
        Mode::Asm {src,bin,dump_symbols} => asm6510::assemble_file(src),
        Mode::Dasm {start_addr,end_addr,bin} => asm6510::disassemble_file(start_addr, end_addr, bin),
    };
    if let Err(apperr) = result {
        println!("\nerror: {:?}", apperr)
    }

    println!("Hello, world!");
}
