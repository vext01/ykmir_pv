// Copyright 2019 King's College London.
// Created by the Software Development Team <http://soft-dev.org/>.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/// ykpack -- Serialiser and deserialiser for carrying data from compile-time to run-time.
///
/// This crate allows ykrustc to serialise various compile-time information for later
/// deserialisation by the Yorick runtime.
///
/// The encoder and decoder API is structured in such a way that each item -- or "Pack" -- can be
/// streamed to/from the serialised format one item at a time. This helps to reduce memory
/// consumption.
///
/// The MIR data is serialised in the msgpack format in the following form:
///
///  -----------
///  pack_0:             \
///  ...                  - Packs.
///  pack_n              /
///  sentinel           -- End of packs marker.
///  -----------
///
///  Where each pack_i is an instance of `Some(Pack)` and the sentinel is a `None`.
///
///  The version field is automatically written and checked by the `Encoder` and `Decoder`
///  respectively.
use serde::{Deserialize, Serialize};

mod decode;
mod encode;

pub use decode::Decoder;
pub use encode::Encoder;

pub type CrateHash = u64;
pub type DefIndex = u32;
pub type BasicBlockIndex = u32;
pub type LocalIndex = u32;

/// A mirror of the compiler's notion of a "definition ID".
#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone, Hash)]
pub struct DefId {
    pub crate_hash: CrateHash,
    pub def_idx: DefIndex,
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
    pub def_id: DefId,
    pub blocks: Vec<BasicBlock>,
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
    pub stmts: Vec<Statement>,
    pub term: Terminator,
}

impl BasicBlock {
    /// Create a new MIR block.
    pub fn new(stmts: Vec<Statement>, term: Terminator) -> Self {
        Self { stmts, term }
    }
}

/// A MIR statement.
/// See the compiler sources for the meanings of these variants.
#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub enum Statement {
    Assign(Place, Rvalue),
    //FakeRead(FakeReadCause, Place),
    //SetDiscriminant {
    //    place: Place,
    //    variant_index: VariantIdx,
    //},
    //StorageLive(Local),
    //StorageDead(Local),
    //InlineAsm {
    //    asm: Box<InlineAsm>,
    //    outputs: Box<[Place]>,
    //    inputs: Box<[(Span, Operand)]>,
    //},
    //Retag(RetagKind, Place),
    //AscribeUserType(Place, ty::Variance, Box<UserTypeProjection>),
    Nop,
}

#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub enum Rvalue {
    //Use(Operand),
    //Repeat(Operand, u64),
    //Ref(Region, BorrowKind, Place),
    //Len(Place),
    //Cast(CastKind, Operand, Ty),
    //BinaryOp(BinOp, Operand, Operand),
    //CheckedBinaryOp(BinOp, Operand, Operand),
    //NullaryOp(NullOp, Ty),
    //UnaryOp(UnOp, Operand),
    //Discriminant(Place),
    //Aggregate(Box<AggregateKind>, Vec<Operand>),
}

#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub enum Operand {
    /// Copy: The value must be available for use afterwards.
    ///
    /// This implies that the type of the place must be `Copy`; this is true
    /// by construction during build, but also checked by the MIR type checker.
    Copy(Place),

    /// Move: The value (including old borrows of it) will not be used again.
    ///
    /// Safe for values of all types (modulo future developments towards `?Move`).
    /// Correct usage patterns are enforced by the borrow checker for safe code.
    /// `Copy` may be converted to `Move` to enable "last-use" optimizations.
    Move(Place),

    /// Synthesizes a constant value.
    Constant(Box<Constant>),
}

#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub struct Constant {
    //pub ty: Ty,
    // FIXME ensure this is evaluated
    //pub literal: &'tcx ty::LazyConst<'tcx>,
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
        ret_bb: Option<BasicBlockIndex>,
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

/// A place is a location for MIR statement operands and return values.
#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub enum Place {
    /// A MIR-local variable.
    Local(LocalIndex),
    // A static variable.
    //Static(Box<Static>),
    // Constant code which has been promoted.
    //Promoted(Box<(Promoted, Ty<'tcx>)>),
    // A "projection".
    //Projection(PlaceProjection),
}

/// The top-level pack type.
#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub enum Pack {
    Mir(Mir),
}

#[cfg(test)]
mod tests {
    use super::{BasicBlock, Decoder, DefId, Encoder, Mir, Pack, Statement, Terminator};
    use fallible_iterator::{self, FallibleIterator};
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

    // Makes some sample stuff to round trip test.
    fn get_sample_packs() -> Vec<Pack> {
        let dummy_term = Terminator::Abort;

        let stmts1_b1 = vec![Statement::Nop; 16];
        let stmts1_b2 = vec![Statement::Nop; 3];
        let blocks1 = vec![
            BasicBlock::new(stmts1_b1, dummy_term.clone()),
            BasicBlock::new(stmts1_b2, dummy_term.clone()),
        ];
        let mir1 = Pack::Mir(Mir::new(DefId::new(1, 2), blocks1));

        let stmts2_b1 = vec![Statement::Nop; 7];
        let stmts2_b2 = vec![Statement::Nop; 200];
        let stmts2_b3 = vec![Statement::Nop; 1];
        let blocks2 = vec![
            BasicBlock::new(stmts2_b1, dummy_term.clone()),
            BasicBlock::new(stmts2_b2, dummy_term.clone()),
            BasicBlock::new(stmts2_b3, dummy_term.clone()),
        ];
        let mir2 = Pack::Mir(Mir::new(DefId::new(4, 5), blocks2));

        vec![mir1, mir2]
    }

    // Check serialising and deserialising works for zero packs.
    #[test]
    fn test_empty() {
        let mut curs = get_curs();

        let enc = Encoder::from(&mut curs);
        enc.done().unwrap();

        rewind_curs(&mut curs);
        let mut dec = Decoder::from(&mut curs);
        assert!(dec.next().unwrap().is_none());
    }

    // Check a typical serialising and deserialising session.
    #[test]
    fn test_basic() {
        let inputs = get_sample_packs();
        let mut curs = get_curs();

        let mut enc = Encoder::from(&mut curs);
        for md in &inputs {
            enc.serialise(md.clone()).unwrap();
        }
        enc.done().unwrap();

        rewind_curs(&mut curs);
        let dec = Decoder::from(&mut curs);

        // Obtain two fallible iterators, so we can zip them.
        let expect_iter = fallible_iterator::convert(inputs.into_iter().map(|e| Ok(e)));

        let mut itr = dec.zip(expect_iter);
        while let Some((got, expect)) = itr.next().unwrap() {
            assert_eq!(expect, got);
        }
    }

    #[test]
    #[should_panic(expected = "not marked done")]
    fn test_encode_not_done() {
        let inputs = get_sample_packs();
        let mut curs = get_curs();

        let mut enc = Encoder::from(&mut curs);
        for md in &inputs {
            enc.serialise(md.clone()).unwrap();
        }
        // We expect this to panic, as the encoder wasn't finalised with a call to `enc.done()`.
    }
}
