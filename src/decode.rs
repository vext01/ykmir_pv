// Copyright 2019 King's College London.
// Created by the Software Development Team <http://soft-dev.org/>.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use crate::{Expect, Index, Mir, FORMAT_VERSION};
use rmp_serde::{
    decode::{self, ReadReader},
    Deserializer,
};
use serde::Deserialize;
use std::io::Read;

/// A decoder.
pub struct Decoder<'a> {
    deser: Deserializer<ReadReader<&'a mut dyn Read>>,
    index: Index,
}

impl<'a> Decoder<'a> {
    /// Returns a new decoder which will deserialise from `read_from` and also an `Index` informing
    /// the consumer of the expected contents.
    pub fn new(read_from: &'a mut dyn Read) -> Result<(Index, Self), decode::Error> {
        let mut deser = Deserializer::new(read_from);
        let ver = usize::deserialize(&mut deser)?;
        if ver != FORMAT_VERSION {
            panic!("incorrect version number!");
        }

        let index = Index::deserialize(&mut deser)?;
        Ok((
            index.clone(),
            Self {
                deser,
                // The decoder uses a copy of the index to keep track of what comes next.
                index,
            },
        ))
    }

    /// Deserialize one MIR's worth of data.
    pub fn read_mir(&mut self) -> Result<Mir, decode::Error> {
        if self.index.expect_next() != Expect::Mir {
            panic!("Tried to decode a MIR entry at the wrong position");
        }
        Ok(Mir::deserialize(&mut self.deser)?)
    }
}
