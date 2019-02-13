// Copyright 2019 King's College London.
// Created by the Software Development Team <http://soft-dev.org/>.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/// YkMir -- Metadata serialiser and deserialiser for Yorick.
///
/// This crate allows ykrustc to serialise the compiler's MIR structures for later deserialisation
/// by the Yorick runtime. The encoded data is specialised to a particular Rust input program (this
/// is in contrast to rustc's notion of crate metadata which is stored in a generic form, so that
/// later compilation sessions can perform their own specialisations). By storing specialised MIR,
/// we avoid the need to carry a whole instance of the compiler with us at runtime to resolve
/// generic metadata into specialised metadata (Rust's metadata loader API would require us to pass
/// a `TyCtxt`).
///
/// The encoder and decoder API is structured in such a way that MIRs can be streamed in and out one
/// at a time. This helps to reduce memory consumption in the compiler, avoiding the need to have
/// an entire second version of the compiler's metadata in memory at compile-time.
///
/// The MIR data is serialised to msgpack data in the following form:
///
///  version            -- The ABI version number of the serialised data.
///  index:             -- A struct outlining the contents of the serialised data.
///    num_mirs: usize  -- The number of MIR objects serialised.
///  mir_0:             \
///  ...⋮                - MIR entries.
///  mir_n              /

#[macro_use]
extern crate serde_derive;

mod decode;
mod encode;

pub use decode::Decoder;
pub use encode::Encoder;

/// The version number of the data structures.
const SER_VERSION: usize = 0;

pub type CrateHash = u64;
pub type DefIndex = u32;
pub type BasicBlockIndex = u32;

/// A mirror of the compiler's notion of a "definition ID".
#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub struct DefId {
    crate_hash: CrateHash,
    def_idx: DefIndex,
}

impl DefId {
    pub fn new(crate_hash: CrateHash, def_idx: DefIndex) -> Self {
        Self {
            crate_hash,
            def_idx,
        }
    }
}

/// A MIR.
#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub struct Mir {
    def_id: DefId,
    blocks: Vec<BasicBlock>,
}

impl Mir {
    /// Create a new MIR.
    pub fn new(def_id: DefId, blocks: Vec<BasicBlock>) -> Self {
        Self { def_id, blocks }
    }
}

/// A MIR block.
#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub struct BasicBlock {
    stmts: Vec<Statement>,
    term: Terminator,
}

impl BasicBlock {
    /// Create a new MIR block.
    pub fn new(stmts: Vec<Statement>, term: Terminator) -> Self {
        Self { stmts, term }
    }
}

/// A MIR statement.
/// FIXME to be populated.
#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub enum Statement {
    Nop,
}

/// A call target.
#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub enum CallOperand {
    /// A statically known function identified by its DefId.
    Fn(DefId),
    /// An unknown or unhandled callable.
    Unknown, // FIXME -- Find out what else. Closures jump to mind.
}

/// A MIR block terminator.
#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub enum Terminator {
    Goto {
        target_bb: BasicBlockIndex,
    },
    SwitchInt {
        target_bbs: Vec<BasicBlockIndex>,
    },
    Resume,
    Abort,
    Return,
    Unreachable,
    Drop {
        target_bb: BasicBlockIndex,
        unwind_bb: Option<BasicBlockIndex>,
    },
    DropAndReplace {
        target_bb: BasicBlockIndex,
        unwind_bb: Option<BasicBlockIndex>,
    },
    Call {
        operand: CallOperand,
        cleanup_bb: Option<BasicBlockIndex>,
    },
    Assert {
        target_bb: BasicBlockIndex,
        cleanup_bb: Option<BasicBlockIndex>,
    },
    Yield {
        resume_bb: BasicBlockIndex,
        drop_bb: Option<BasicBlockIndex>,
    },
    GeneratorDrop,
    FalseEdges {
        real_target_bb: BasicBlockIndex,
    },
    FalseUnwind {
        real_target_bb: BasicBlockIndex,
    },
}

/// The top-level meta-data type.
#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub enum MetaData {
    Mir(Mir),
}

#[cfg(test)]
mod tests {
    use super::{BasicBlock, Decoder, DefId, Encoder, Mir, Statement, Terminator, MetaData};
    use fallible_iterator::FallibleIterator;
    use std::io::{Cursor, Seek, SeekFrom};

    // Get a cursor to serialise to and deserialise from. For real, we'd be reading from a file,
    // but for tests we use a vector of bytes.
    fn get_curs() -> Cursor<Vec<u8>> {
        let buf: Vec<u8> = Vec::new();
        Cursor::new(buf)
    }

    // Rewind a cursor to the beginning.
    fn rewind_curs(curs: &mut Cursor<Vec<u8>>) {
        curs.seek(SeekFrom::Start(0)).unwrap();
    }

    // Check serialising and deserialising works for zero MIRs.
    #[test]
    fn test_empty() {
        let mut curs = get_curs();

        let enc = Encoder::from(&mut curs).unwrap();
        enc.done().unwrap();

        rewind_curs(&mut curs);
        let dec = Decoder::new(&mut curs).unwrap();
        assert!(dec.iter().next().unwrap().is_none());
    }

    // Check a typical serialising and deserialising session.
    #[test]
    fn test_basic() {
        let dummy_term = Terminator::Abort;

        let stmts1_b1 = vec![Statement::Nop; 16];
        let stmts1_b2 = vec![Statement::Nop; 3];
        let blocks1 = vec![
            BasicBlock::new(stmts1_b1, dummy_term.clone()),
            BasicBlock::new(stmts1_b2, dummy_term.clone()),
        ];
        let mir1 = MetaData::Mir(Mir::new(DefId::new(1, 2), blocks1));

        let stmts2_b1 = vec![Statement::Nop; 7];
        let stmts2_b2 = vec![Statement::Nop; 200];
        let stmts2_b3 = vec![Statement::Nop; 1];
        let blocks2 = vec![
            BasicBlock::new(stmts2_b1, dummy_term.clone()),
            BasicBlock::new(stmts2_b2, dummy_term.clone()),
            BasicBlock::new(stmts2_b3, dummy_term.clone()),
        ];
        let mir2 = MetaData::Mir(Mir::new(DefId::new(4, 5), blocks2));

        let mut curs = get_curs();

        let mut enc = Encoder::from(&mut curs).unwrap();
        enc.serialise(mir1.clone()).unwrap();
        enc.serialise(mir2.clone()).unwrap();
        enc.done().unwrap();

        rewind_curs(&mut curs);

        let dec = Decoder::new(&mut curs).unwrap();
        let mut itr = dec.iter();

        let got_mir1 = itr.next().unwrap();
        assert_eq!(got_mir1, Some(mir1));

        let got_mir2 = itr.next().unwrap();
        assert_eq!(got_mir2, Some(mir2));

        assert!(itr.next().unwrap().is_none());
    }
}
