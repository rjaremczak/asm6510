use std::str::FromStr;

use super::AsmError;

use crate::emu6510::instruction::Instruction::{self, *};

static MNEMONICS: [(Instruction, &str); 57] = [
    (KIL, "KIL"),
    (ADC, "ADC"),
    (SBC, "SBC"),
    (AND, "AND"),
    (ORA, "ORA"),
    (ASL, "ASL"),
    (LSR, "LSR"),
    (EOR, "EOR"),
    (ROL, "ROL"),
    (ROR, "ROR"),
    (BIT, "BIT"),
    (CMP, "CMP"),
    (CPX, "CPX"),
    (CPY, "CPY"),
    (INC, "INC"),
    (INX, "INX"),
    (INY, "INY"),
    (DEC, "DEC"),
    (DEX, "DEX"),
    (DEY, "DEY"),
    (BCC, "BCC"),
    (BCS, "BCS"),
    (BEQ, "BEQ"),
    (BMI, "BMI"),
    (BNE, "BNE"),
    (BPL, "BPL"),
    (BVC, "BVC"),
    (BVS, "BVS"),
    (CLC, "CLC"),
    (CLD, "CLD"),
    (CLI, "CLI"),
    (CLV, "CLV"),
    (SEC, "SEC"),
    (SED, "SED"),
    (SEI, "SEI"),
    (JMP, "JMP"),
    (JSR, "JSR"),
    (BRK, "BRK"),
    (RTI, "RTI"),
    (RTS, "RTS"),
    (LDA, "LDA"),
    (LDX, "LDX"),
    (LDY, "LDY"),
    (STA, "STA"),
    (STX, "STX"),
    (STY, "STY"),
    (TAX, "TAX"),
    (TAY, "TAY"),
    (TSX, "TSX"),
    (TXA, "TXA"),
    (TYA, "TYA"),
    (TXS, "TXS"),
    (PHA, "PHA"),
    (PHP, "PHP"),
    (PLA, "PLA"),
    (PLP, "PLP"),
    (NOP, "NOP"),
];

impl FromStr for Instruction {
    type Err = AsmError;

    fn from_str(mnemonic: &str) -> Result<Self, Self::Err> {
        let mn_norm = mnemonic.to_uppercase();
        for (i, m) in MNEMONICS {
            if mn_norm == m {
                return Ok(i);
            }
        }
        Err(AsmError::InvalidMnemonic(mnemonic.to_string()))
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
        assert_eq!(Instruction::from_str("LDX").unwrap(), LDX);
        assert_eq!(Instruction::from_str("LDA").unwrap(), LDA);
        assert_eq!(Instruction::from_str("lda").unwrap(), LDA);
    }

    #[test]
    fn find_mnemonic_failed() {
        assert!(Instruction::from_str("JUH").is_err());
    }

    #[test]
    fn get_mnemonic() {
        assert_eq!(LDA.to_string(), "LDA");
        assert_eq!(TXA.to_string(), "TXA");
        assert_eq!(KIL.to_string(), "KIL");
        assert_eq!(JMP.to_string(), "JMP");
    }
}
