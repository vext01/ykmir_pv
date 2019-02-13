// Copyright 2019 King's College London.
// Created by the Software Development Team <http://soft-dev.org/>.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use crate::{SER_VERSION, MetaData};
use rmp_serde::{
    decode::{self, ReadReader},
    Deserializer,
};
use serde::Deserialize;
use std::io::Read;
use std::iter::Iterator; //{IntoIter, Iterator};

/// A decoder.
pub struct Decoder<'a> {
    deser: Deserializer<ReadReader<&'a mut dyn Read>>,
}

impl<'a> Decoder<'a> {
    /// Returns a new decoder which will deserialise from `read_from` and also an `Index` informing
    /// the consumer of the expected contents.
    pub fn new(read_from: &'a mut dyn Read) -> Result<Self, decode::Error> {
        let mut deser = Deserializer::new(read_from);
        let ver = usize::deserialize(&mut deser)?;
        if ver != SER_VERSION {
            panic!("incorrect version number!");
        }
        Ok(Self { deser })
    }

    pub fn iter(self) -> MetaDataIterator<'a> {
        MetaDataIterator { deser: self.deser }
    }
}

pub struct MetaDataIterator<'a> {
    deser: Deserializer<ReadReader<&'a mut dyn Read>>,
}

impl<'a> Iterator for MetaDataIterator<'a> {
    type Item = MetaData;

    fn next(&mut self) -> Option<MetaData> { //Option<Self::Item> {
        //Option::<MetaData>::deserialize(&mut self.deser).unwrap()
        let f = Option::<MetaData>::deserialize(&mut self.deser);
        eprintln!("{:?}", f);
        f.unwrap()
    }
}
