// Copyright 2019 King's College London.
// Created by the Software Development Team <http://soft-dev.org/>.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Types for the Yorick intermediate language.

use serde::{Deserialize, Serialize};
use std::fmt::{self, Display};

pub type CrateHash = u64;
pub type DefIndex = u32;
pub type BasicBlockIndex = u32;
pub type LocalIndex = u32;

/// A mirror of the compiler's notion of a "definition ID".
#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
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

impl Display for DefId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "DefId({}, {})", self.crate_hash, self.def_idx)
    }
}

#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub struct Mir {
    pub def_id: DefId,
    pub item_path_str: String,
    pub blocks: Vec<BasicBlock>,
}

impl Mir {
    pub fn new(def_id: DefId, item_path_str: String, blocks: Vec<BasicBlock>) -> Self {
        Self {
            def_id,
            item_path_str,
            blocks,
        }
    }
}

impl Display for Mir {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "[Begin TIR for {}]", self.item_path_str)?;
        writeln!(f, "    {}:", self.def_id)?;
        for (i, b) in self.blocks.iter().enumerate() {
            write!(f, "    bb{}:\n{}", i, b)?;
        }
        writeln!(f, "[End TIR for {}]", self.item_path_str)?;
        Ok(())
    }
}

#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub struct BasicBlock {
    pub stmts: Vec<Statement>,
    pub term: Terminator,
}

impl BasicBlock {
    pub fn new(stmts: Vec<Statement>, term: Terminator) -> Self {
        Self { stmts, term }
    }
}

impl Display for BasicBlock {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for s in self.stmts.iter() {
            write!(f, "        {}", s)?;
        }
        writeln!(f, "        term: {}\n", self.term)
    }
}

#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub enum Statement {
    Nop,
    Assign(Place, Rvalue),
    Unimplemented, // FIXME
}

impl Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "{:?}", self)
    }
}

impl Statement {
    pub fn uses_vars(&self) -> Vec<LocalIndex> {
        match self {
            Statement::Nop | Statement::Unimplemented => vec![],
            Statement::Assign(_, rv) => rv.uses_vars(),
        }
    }

    pub fn defs_vars(&self) -> Vec<LocalIndex> {
        match self {
            Statement::Nop | Statement::Unimplemented => vec![],
            Statement::Assign(p, _) => p.defs_vars(),
        }
    }

    pub fn is_phi(&self) -> bool {
        if let Statement::Assign(_, Rvalue::Phi(..)) = self {
            return true;
        }
        false
    }
}

#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub enum Place {
    Local(LocalIndex),
    Unimplemented, // FIXME
}

impl Place {
    fn uses_vars(&self) -> Vec<LocalIndex> {
        match self {
            Place::Local(l) => vec![*l],
            Place::Unimplemented => vec![],
        }
    }

    fn defs_vars(&self) -> Vec<LocalIndex> {
        match self {
            Place::Local(l) => vec![*l],
            Place::Unimplemented => vec![],
        }
    }
}

#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub enum Rvalue {
    Place(Place),
    Phi(Vec<Place>),
    Unimplemented, // FIXME
}

impl Rvalue {
    fn uses_vars(&self) -> Vec<LocalIndex> {
        match self {
            Rvalue::Place(p) => p.uses_vars(),
            Rvalue::Phi(ps) => {
                let mut res = Vec::new();
                ps.iter().fold(&mut res, |r, p| {
                    r.extend(p.uses_vars());
                    r
                });
                res
            },
            Rvalue::Unimplemented => vec![],
        }
    }
}

/// A call target.
#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub enum CallOperand {
    /// A statically known function identified by its DefId.
    Fn(DefId),
    /// An unknown or unhandled callable.
    Unknown, // FIXME -- Find out what else. Closures jump to mind.
}

/// A basic block terminator.
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
}

impl Display for Terminator {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

/// The top-level pack type.
#[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
pub enum Pack {
    Mir(Mir),
}

impl Display for Pack {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let Pack::Mir(mir) = self;
        write!(f, "{}", mir)
    }
}

#[cfg(test)]
mod tests {
    use super::{Statement, Place, Rvalue};

    #[test]
    fn assign_uses_vars() {
        let s = Statement::Assign(Place::Local(42), Rvalue::Place(Place::Local(43)));
        assert_eq!(s.uses_vars(), vec![43]);
    }

    #[test]
    fn assign_defs_vars() {
        let s = Statement::Assign(Place::Local(42), Rvalue::Place(Place::Local(43)));
        assert_eq!(s.defs_vars(), vec![42]);
    }

    #[test]
    fn phi_uses_vars() {
        let s = Statement::Assign(Place::Local(44),
            Rvalue::Phi(vec![Place::Local(100), Place::Local(200)]));
        assert_eq!(s.uses_vars(), vec![100, 200]);
    }

    #[test]
    fn phi_defs_vars() {
        let s = Statement::Assign(Place::Local(44),
            Rvalue::Phi(vec![Place::Local(100), Place::Local(200)]));
        assert_eq!(s.defs_vars(), vec![44]);
    }
}
