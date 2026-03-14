#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Copy, Clone, Hash)]
pub enum Instruction {
    Adc,
    Sbc,
    And,
    Ora,
    Asl,
    Lsr,
    Eor,
    Rol,
    Ror,
    Bit,
    Cmp,
    Cpx,
    Cpy,
    Inc,
    Inx,
    Iny,
    Dec,
    Dex,
    Dey,
    Bcc,
    Bcs,
    Beq,
    Bmi,
    Bne,
    Bpl,
    Bvc,
    Bvs,
    Clc,
    Cld,
    Cli,
    Clv,
    Sec,
    Sed,
    Sei,
    Jmp,
    Jsr,
    Brk,
    Rti,
    Rts,
    Lda,
    Ldx,
    Ldy,
    Sta,
    Stx,
    Sty,
    Tax,
    Tay,
    Tsx,
    Txa,
    Tya,
    Txs,
    Pha,
    Php,
    Pla,
    Plp,
    Nop,
    Kil,
}

use crate::asm6510::error::AppError;
use Instruction::*;
use std::str::FromStr;

static MNEMONICS: [(Instruction, &str); 57] = [
    (Kil, "KIL"),
    (Adc, "ADC"),
    (Sbc, "SBC"),
    (And, "AND"),
    (Ora, "ORA"),
    (Asl, "ASL"),
    (Lsr, "LSR"),
    (Eor, "EOR"),
    (Rol, "ROL"),
    (Ror, "ROR"),
    (Bit, "BIT"),
    (Cmp, "CMP"),
    (Cpx, "CPX"),
    (Cpy, "CPY"),
    (Inc, "INC"),
    (Inx, "INX"),
    (Iny, "INY"),
    (Dec, "DEC"),
    (Dex, "DEX"),
    (Dey, "DEY"),
    (Bcc, "BCC"),
    (Bcs, "BCS"),
    (Beq, "BEQ"),
    (Bmi, "BMI"),
    (Bne, "BNE"),
    (Bpl, "BPL"),
    (Bvc, "BVC"),
    (Bvs, "BVS"),
    (Clc, "CLC"),
    (Cld, "CLD"),
    (Cli, "CLI"),
    (Clv, "CLV"),
    (Sec, "SEC"),
    (Sed, "SED"),
    (Sei, "SEI"),
    (Jmp, "JMP"),
    (Jsr, "JSR"),
    (Brk, "BRK"),
    (Rti, "RTI"),
    (Rts, "RTS"),
    (Lda, "LDA"),
    (Ldx, "LDX"),
    (Ldy, "LDY"),
    (Sta, "STA"),
    (Stx, "STX"),
    (Sty, "STY"),
    (Tax, "TAX"),
    (Tay, "TAY"),
    (Tsx, "TSX"),
    (Txa, "TXA"),
    (Tya, "TYA"),
    (Txs, "TXS"),
    (Pha, "PHA"),
    (Php, "PHP"),
    (Pla, "PLA"),
    (Plp, "PLP"),
    (Nop, "NOP"),
];

impl FromStr for Instruction {
    type Err = AppError;

    fn from_str(mnemonic: &str) -> Result<Self, Self::Err> {
        let mn_norm = mnemonic.to_uppercase();
        for (i, m) in MNEMONICS {
            if mn_norm == m {
                return Ok(i);
            }
        }
        Err(AppError::InvalidMnemonic(mnemonic.to_string()))
    }
}

impl ToString for Instruction {
    fn to_string(&self) -> String {
        for (i, m) in MNEMONICS {
            if self == &i {
                return m.to_string();
            }
        }
        panic!("no mnemonic for instruction {:?}", &self);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{collections::HashSet, str::FromStr};

    #[test]
    fn check_uniqueness() {
        let mut instructions: HashSet<Instruction> = HashSet::new();
        let mut mnemonics: HashSet<&str> = HashSet::new();

        for (i, m) in MNEMONICS {
            assert!(instructions.insert(i), "instruction {:?} not unique", i);
            assert!(mnemonics.insert(m), "mnemonic {} not unique", m);
        }
    }

    #[test]
    fn find_mnemonic_ok() {
        assert_eq!(Instruction::from_str("LDX").unwrap(), Ldx);
        assert_eq!(Instruction::from_str("LDA").unwrap(), Lda);
        assert_eq!(Instruction::from_str("lda").unwrap(), Lda);
    }

    #[test]
    fn find_mnemonic_failed() {
        assert!(Instruction::from_str("JUH").is_err());
    }

    #[test]
    fn get_mnemonic() {
        assert_eq!(Lda.to_string(), "LDA");
        assert_eq!(Txa.to_string(), "TXA");
        assert_eq!(Kil.to_string(), "KIL");
        assert_eq!(Jmp.to_string(), "JMP");
    }
}
