#[macro_use]
extern crate lazy_static;

mod asm6510;

use clap::{Parser,Subcommand};
use std::{fs::File, path::PathBuf};
use asm6510::error::AppError;
use std::io::Write;

fn parse_hex(hex: &str) -> Result<u16, AppError> {
    u16::from_str_radix(hex, 16).map_err(|e| AppError::ParseIntError(String::from(hex), e))
}

#[derive(Parser, Debug)]
#[command(version, about="My Own 65xx assembler and disassembler", long_about = None)]
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

fn mode_asm(src: PathBuf, bin: Option<PathBuf>, dump_symbols: bool) -> Result<(), AppError> {
    println!("source file {:?}, assembling ...", src);
    let (origin, code, symbols) = asm6510::assemble_file(&src)?;
    println!("code: {} B [{:04X}-{:04X}]", code.len(), origin, origin as usize + code.len() - 1);
    let bin = bin.unwrap_or({
        let mut path = PathBuf::new();
        path.set_file_name(src.file_name().unwrap());
        path.set_extension("bin");
        path
    });
    println!("writing file {:#?} ...", bin);
    File::create(&bin)?.write_all(&code)?;

    if dump_symbols {
        println!("symbol table ({} items):", symbols.len());
        symbols.iter().for_each(|(k, v)| println!("\"{}\" = {:04X}", *k, *v as u16));
    }

    Ok(())
}

fn mode_dis(start_addr: u16, end_addr: Option<u16>, bin: PathBuf) -> Result<(), AppError> {
    print!("binary file {:?}, disassemble from address {:04X} ", bin, start_addr);
    match end_addr {
        Some(addr) => println!("to {:04X} ...", addr),
        None => println!("..."),
    }
    asm6510::disassemble_file(start_addr, end_addr, bin)?.iter().for_each(|cols|println!("{}{}{}", cols.0, cols.1, cols.2));
    Ok(())
}

fn main() {

    let args = Args::parse();

    let res = match args.mode {
        Some(Mode::Asm { src, bin, dump_symbols }) => mode_asm(src, bin, dump_symbols),
        Some(Mode::Dis { start_addr, end_addr, bin }) => mode_dis(start_addr, end_addr, bin),
        None => Err(AppError::CliParsingError),
    };

    if let Err(err) = res { print!("\nerror: {:?}",err); }
}
