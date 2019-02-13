// Copyright 2019 King's College London.
// Created by the Software Development Team <http://soft-dev.org/>.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use crate::{MetaData, SER_VERSION};
use fallible_iterator::FallibleIterator;
use rmp_serde::{
    decode::{self, ReadReader},
    Deserializer,
};
use serde::Deserialize;
use std::io::Read;

/// The meta-data decoder.
/// Offfers a simple iterator interface to serialised meta-data.
pub struct Decoder<'a> {
    deser: Deserializer<ReadReader<&'a mut dyn Read>>,
}

impl<'a> Decoder<'a> {
    /// Returns a new decoder which will deserialise from `read_from`.
    pub fn new(read_from: &'a mut dyn Read) -> Result<Self, decode::Error> {
        let mut deser = Deserializer::new(read_from);
        let ver = usize::deserialize(&mut deser)?;
        if ver != SER_VERSION {
            panic!("incorrect version number!");
        }
        Ok(Self { deser })
    }

    // Iterate over meta-data.
    pub fn iter(self) -> MetaDataIterator<'a> {
        MetaDataIterator { deser: self.deser }
    }
}

/// A (fallible) meta-data iterator.
/// Reusing the iterator once is has yielded `None` leads to undefined behaviour.
pub struct MetaDataIterator<'a> {
    deser: Deserializer<ReadReader<&'a mut dyn Read>>,
}

impl<'a> FallibleIterator for MetaDataIterator<'a> {
    type Item = MetaData;
    type Error = decode::Error;

    fn next(&mut self) -> Result<Option<Self::Item>, Self::Error> {
        Option::<MetaData>::deserialize(&mut self.deser)
    }
}
