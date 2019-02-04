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
    encode::{self, StructArrayWriter},
    Serializer,
};
use serde::Serialize;
use std::{io::prelude::*, ops::Drop};

/// The encoder.
pub struct Encoder<'a> {
    ser: Serializer<&'a mut dyn Write, StructArrayWriter>,
    // A copy of the initial index which is mutated to keep track of what's left to serialize.
    state: Index,
}

impl<'a> Encoder<'a> {
    /// Creates a new encoder which will serialise into `write_into`. The `index` informs the
    /// encoder what to expect to encode. The user must encode exactly as many data structures as
    /// what is outlined in the index, or the encoder will panic.
    pub fn new(write_into: &'a mut dyn Write, index: Index) -> Result<Self, encode::Error> {
        let mut ser = Serializer::new(write_into);
        FORMAT_VERSION.serialize(&mut ser)?;
        index.serialize(&mut ser)?;
        Ok(Self { ser, state: index })
    }

    /// Serialises one MIR's worth of data.
    pub fn write_mir(&mut self, mir: Mir) -> Result<(), encode::Error> {
        if self.state.expect_next() != Expect::Mir {
            panic!("Tried to encode a MIR at the wrong position");
        }

        mir.serialize(&mut self.ser)?;
        Ok(())
    }
}

/// Drop implementation prevents partial encodings from going unnoticed.
/// E.g. We wrote an index saying there'd be 10 MIRs, but the encoder was dropped after 9.
impl<'a> Drop for Encoder<'a> {
    fn drop(&mut self) {
        if self.state.expect_next() != Expect::NoMore {
            panic!("MIR decoder dropped before all expected data serialised");
        }
    }
}
