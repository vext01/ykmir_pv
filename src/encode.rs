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
    encode::{self},
    Serializer,
};
use serde::Serialize;
use std::io::prelude::*;

/// The encoder.
pub struct Encoder<'a> {
    ser: Serializer<&'a mut dyn Write>,
}

impl<'a> Encoder<'a> {
    /// Creates a new encoder which will serialise into `write_into`. The `index` informs the
    /// encoder what to expect to encode. The user must encode exactly as many data structures as
    /// what is outlined in the index, or the encoder will panic.
    pub fn from(write_into: &'a mut dyn Write) -> Result<Self, encode::Error> {
        let mut ser = Serializer::new(write_into);
        SER_VERSION.serialize(&mut ser)?;
        Ok(Self { ser })
    }

    /// Serialises one MIR's worth of data.
    pub fn serialise(&mut self, md: MetaData) -> Result<(), encode::Error> {
        let to_ser: Option<MetaData> = Some(md);
        //Some(md).serialize(&mut self.ser)?;
        println!("encoding: {:?}", to_ser);
        to_ser.serialize(&mut self.ser)?;
        Ok(())
    }

    /// Finalises an encoding session.
    pub fn done(mut self) -> Result<(), encode::Error> {
        let to_ser: Option<MetaData> = None;
        to_ser.serialize(&mut self.ser)?;
        Ok(())
    }
}
