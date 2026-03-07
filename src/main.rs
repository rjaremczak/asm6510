#[macro_use]
extern crate lazy_static;

mod asm6510;

use clap::{Parser,Subcommand};
use std::path::PathBuf;
use asm6510::error::AppError;

fn parse_hex(hex: &str) -> Result<u16, AppError> {
    u16::from_str_radix(hex, 16).map_err(|e| AppError::ParseIntError(String::from(hex), e))
}

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
#[structopt(about = "My Own 65xx assembler and disassembler")]
struct Args {
    /// Execution mode
    #[command(subcommand)]
    mode: Option<Mode>,
}

#[derive(Debug, Subcommand)]
enum Mode {
    /// Assemble source to machine code
    Asm {
        /// Source file path
        #[arg(long)]
        src: PathBuf,
        /// Binary file path
        #[arg(long)]
        bin: Option<PathBuf>,
        /// Dump symbol table
        #[arg(long)]
        dump_symbols: bool,
    },
    /// Disassemble machine code
    Dis {
        /// Start address
        #[arg(long)]
        start_addr: u16,
        /// End address
        #[arg(long)]
        end_addr: Option<u16>,
        /// Binary file path
        #[arg(long)]
        bin: PathBuf,
    },
}

fn main() {

    let args = Args::parse();

    match args.mode {
        Some(Mode::Asm { src, bin, dump_symbols }) => {
            asm6510::assemble_file(src);
        },
        Some(Mode::Dis { start_addr, end_addr, bin }) => {
            asm6510::disassemble_file(start_addr, end_addr, fpath);
        },
        None => println!("\nerror: {:?}", apperr),
    }
}
