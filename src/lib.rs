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
pub type VariantIndex = u32;
pub type PromotedIndex = u32;
pub type FieldIndex = u32;
pub type AdtFlags = u32;
pub type VariantFlags = u32;
pub type ReprFlags = u32;
pub type SymbolIndex = u32;
pub type TypeFlags = u32;
pub type DebruijnIndex = u32;
pub type AllocId = u64;
pub type Size = u64;

// We used thes "reference indices" to work around the fact that serde can't serialise parts of the
// MIR which are references. We replace the reference with an index into a separately packed
// vector.
pub type RegionRef = u32;
pub type TyRef = u32;
pub type AdtDefRef = u32;
pub type SubstsRef = u32;
pub type ConstRef = u32;

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
    pub stmts: Vec<StatementKind>,
    pub term: TerminatorKind,
}

impl BasicBlock {
    /// Create a new MIR block.
    pub fn new(stmts: Vec<StatementKind>, term: TerminatorKind) -> Self {
        Self { stmts, term }
    }
}

/// A MIR statement.
/// See the compiler sources for the meanings of these variants.
#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub enum StatementKind {
    Assign(Place, Rvalue),
    FakeRead(Place),
    SetDiscriminant {
        place: Place,
        variant_index: VariantIndex,
    },
    StorageLive(LocalIndex),
    StorageDead(LocalIndex),
    InlineAsm, // We make no attempt to deal with inline asm for now.
    Retag(RetagKind, Place),
    AscribeUserType, // FIXME flesh this variant out.
    Nop,
}

// FIXME implement
#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub enum Rvalue {
    Dummy
}

#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub enum Operand {
    Copy(Place),
    Move(Place),
    Constant(Constant),
}

#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub struct Constant {
    pub ty: TyRef,
    pub literal: ConstRef,
}

/// An evaluated const.
/// Note that at compile-time there is the notion of unevaluated and evaluated constants. Since
/// evaluation requires a tcx, we do all evaluation and compile-time, and there is no notion of an
/// unevaluated constant in ykpack.
#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub struct Const {
    pub ty: TyRef,
    pub val: ConstValue,
}

#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub enum ConstValue {
    Scalar(Scalar),
    Slice(Scalar, u64),
    ByRef(AllocId, Allocation, Size),
}


#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
// FIXME implement
pub struct Allocation{}

#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub enum Scalar<Tag=(), Id=AllocId> {
    Bits {
        size: u8,
        bits: u128,
    },
    Ptr(Pointer<Tag, Id>),
}

#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub struct Pointer<Tag=(),Id=AllocId> {
    pub alloc_id: Id,
    pub offset: Size,
    pub tag: Tag,
}

// FIXME -- revert to mirroring what rustc has here instead of specialising.
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
pub enum TerminatorKind {
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
    Local(LocalIndex),
    Static(Static),
    Promoted((PromotedIndex, TyRef)),
    Projection(Box<PlaceProjection>),
}

#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub struct Static {
    pub def_id: DefId,
    pub ty: TyRef,
}

#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub struct TyS {
    pub sty: TyKind,
    pub flags: TypeFlags,
    outer_exclusive_binder: DebruijnIndex,
}

// FIXME implement
#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub enum TyKind {
    Dummy,
}

// FIXME implement
#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub enum RegionKind {
    Dummy,
}

#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub struct TypeAndMut {
    pub ty: TyRef,
    pub mutbl: Mutability,
}

#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub enum Mutability {
    MutMutable,
    MutImmutable,
}

// In the Rust compiler, this is an interned pointer.
pub type Substs = Vec<(TyRef, RegionRef)>;

#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub struct Projection<B, V, T> {
    base: B,
    elem: ProjectionElem<V, T>,
}

pub type PlaceProjection = Projection<Place, LocalIndex, TyRef>;
pub type PlaceElem = ProjectionElem<LocalIndex, TyRef>;

#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub enum ProjectionElem<V, T> {
    Deref,
    Field(FieldIndex, T),
    Index(V),
    ConstantIndex {
        offset: u32,
        min_length: u32,
        from_end: bool,
    },
    Subslice {
        from: u32,
        to: u32,
    },
    Downcast(AdtDefRef, VariantIndex),
}

#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub struct AdtDef {
    pub did: DefId,
    pub variants: Vec<VariantDef>,
    flags: AdtFlags,
    pub repr: ReprOptions,
}

#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub struct ReprOptions {
    pub int: Option<IntType>,
    pub align: u32,
    pub pack: u32,
    pub flags: ReprFlags,
}

#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub enum IntType {
    SignedInt(IntTy),
    UnsignedInt(UintTy)
}

#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub enum UintTy {
    Usize,
    U8,
    U16,
    U32,
    U64,
    U128,
}

#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub enum IntTy {
    Isize,
    I8,
    I16,
    I32,
    I64,
    I128,
}

#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub enum FloatTy {
    F32,
    F64,
}

#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub struct VariantDef {
    /// The variant's `DefId`. If this is a tuple-like struct,
    /// this is the `DefId` of the struct's ctor.
    pub did: DefId,
    pub ident: SymbolIndex, // struct's name if this is a struct
    pub discr: VariantDiscr,
    pub fields: Vec<FieldDef>,
    pub ctor_kind: CtorKind,
    flags: VariantFlags,
}

#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub enum CtorKind {
    Fn,
    Const,
    Fictive,
}

#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub struct FieldDef {
    pub did: DefId,
    pub ident: SymbolIndex,
    pub vis: Visibility,
}

#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub enum Visibility {
    Public,
    Restricted(DefId),
    Invisible,
}

#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub enum VariantDiscr {
    Explicit(DefId),
    Relative(u32),
}

#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub enum RetagKind {
    FnEntry,
    TwoPhase,
    Raw,
    Default,
}

/// The top-level pack type.
#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub enum Pack {
    Mir(Mir),
}

#[cfg(test)]
mod tests {
    use super::{BasicBlock, Decoder, DefId, Encoder, Mir, Pack, StatementKind, TerminatorKind};
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
        let dummy_term = TerminatorKind::Abort;

        let stmts1_b1 = vec![StatementKind::Nop; 16];
        let stmts1_b2 = vec![StatementKind::Nop; 3];
        let blocks1 = vec![
            BasicBlock::new(stmts1_b1, dummy_term.clone()),
            BasicBlock::new(stmts1_b2, dummy_term.clone()),
        ];
        let mir1 = Pack::Mir(Mir::new(DefId::new(1, 2), blocks1));

        let stmts2_b1 = vec![StatementKind::Nop; 7];
        let stmts2_b2 = vec![StatementKind::Nop; 200];
        let stmts2_b3 = vec![StatementKind::Nop; 1];
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
