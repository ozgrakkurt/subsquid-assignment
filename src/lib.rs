use std::convert::TryFrom;
use std::{io, mem};

pub trait Encode: Sized {
    type Error;

    fn encode<W: io::Write>(&self, writer: &mut W) -> Result<(), Error>;
}

pub trait Decode: Sized {
    type Error;

    fn decode<R: io::Read>(reader: &mut R) -> Result<Self, Error>;
}

macro_rules! impl_encode_decode_primary {
    ($i:ident) => {
        impl Encode for $i {
            type Error = Error;

            fn encode<W: io::Write>(&self, writer: &mut W) -> Result<(), Error> {
                writer.write_all(&self.to_le_bytes())?;

                Ok(())
            }
        }

        impl Decode for $i {
            type Error = Error;

            fn decode<R: io::Read>(reader: &mut R) -> Result<Self, Error> {
                let mut buf = [0; mem::size_of::<Self>()];

                reader.read_exact(&mut buf)?;

                Ok(Self::from_le_bytes(buf))
            }
        }
    };
}

impl_encode_decode_primary!(i8);
impl_encode_decode_primary!(i16);
impl_encode_decode_primary!(i32);
impl_encode_decode_primary!(i64);
impl_encode_decode_primary!(i128);
impl_encode_decode_primary!(u8);
impl_encode_decode_primary!(u16);
impl_encode_decode_primary!(u32);
impl_encode_decode_primary!(u64);
impl_encode_decode_primary!(u128);

#[derive(Debug, Eq, PartialEq, Clone, Copy)]
pub struct OptionBool(pub Option<bool>);

impl Encode for OptionBool {
    type Error = Error;

    fn encode<W: io::Write>(&self, writer: &mut W) -> Result<(), Error> {
        match self.0 {
            None => {
                writer.write_all(&[0])?;
            }
            Some(true) => {
                writer.write_all(&[1])?;
            }
            Some(false) => {
                writer.write_all(&[2])?;
            }
        }

        Ok(())
    }
}

impl Decode for OptionBool {
    type Error = Error;

    fn decode<R: io::Read>(reader: &mut R) -> Result<Self, Error> {
        let mut buf = [0; 1];

        reader.read_exact(&mut buf)?;

        match buf[0] {
            0 => Ok(OptionBool(None)),
            1 => Ok(OptionBool(Some(true))),
            2 => Ok(OptionBool(Some(false))),
            idx => Err(Error::InvalidVariantInEnum(idx)),
        }
    }
}

impl<T: Encode> Encode for Option<T> {
    type Error = Error;

    fn encode<W: io::Write>(&self, writer: &mut W) -> Result<(), Error> {
        if std::any::type_name::<T>() == "bool" {
            panic!("use OptionBool instead of Option<bool>");
        }

        match self {
            Some(v) => {
                writer.write_all(&[1])?;
                v.encode(writer)?;
            }
            None => {
                writer.write_all(&[0])?;
            }
        }

        Ok(())
    }
}

impl<T: Decode> Decode for Option<T> {
    type Error = Error;

    fn decode<R: io::Read>(reader: &mut R) -> Result<Self, Error> {
        if std::any::type_name::<T>() == "bool" {
            panic!("use OptionBool instead of Option<bool>");
        }

        let mut buf = [0; 1];

        reader.read_exact(&mut buf)?;

        match buf[0] {
            0 => Ok(None),
            1 => Ok(Some(T::decode(reader)?)),
            idx => Err(Error::InvalidVariantInEnum(idx)),
        }
    }
}

impl<T: Encode, E: Encode> Encode for Result<T, E> {
    type Error = Error;

    fn encode<W: io::Write>(&self, writer: &mut W) -> Result<(), Error> {
        match self {
            Ok(t) => {
                writer.write_all(&[0])?;
                t.encode(writer)?;
            }
            Err(e) => {
                writer.write_all(&[1])?;
                e.encode(writer)?;
            }
        }

        Ok(())
    }
}

impl<T: Decode, E: Decode> Decode for Result<T, E> {
    type Error = Error;

    fn decode<R: io::Read>(reader: &mut R) -> Result<Self, Error> {
        let mut buf = [0; 1];

        reader.read_exact(&mut buf)?;

        match buf[0] {
            1 => Ok(Err(E::decode(reader)?)),
            0 => Ok(Ok(T::decode(reader)?)),
            idx => Err(Error::InvalidVariantInEnum(idx)),
        }
    }
}

impl Encode for bool {
    type Error = Error;

    fn encode<W: io::Write>(&self, writer: &mut W) -> Result<(), Error> {
        writer.write_all(&[if *self { 1 } else { 0 }])?;

        Ok(())
    }
}

impl Decode for bool {
    type Error = Error;

    fn decode<R: io::Read>(reader: &mut R) -> Result<Self, Error> {
        let mut buf = [0; 1];

        reader.read_exact(&mut buf)?;

        match buf[0] {
            1 => Ok(true),
            0 => Ok(false),
            val => Err(Error::InvalidBoolValue(val)),
        }
    }
}

impl<T: Encode> Encode for Vec<T> {
    type Error = Error;

    fn encode<W: io::Write>(&self, writer: &mut W) -> Result<(), Error> {
        let len = self.len();

        if len > usize::try_from(std::u32::MAX).unwrap() {
            return Err(Error::SequenceTooBig(len));
        }

        Compact(self.len() as u32).encode(writer)?;

        for elem in self {
            elem.encode(writer)?;
        }

        Ok(())
    }
}

impl<T: Decode> Decode for Vec<T> {
    type Error = Error;

    fn decode<R: io::Read>(reader: &mut R) -> Result<Self, Error> {
        let len = Compact::decode(reader)?.0;

        let mut vector = Vec::with_capacity(usize::try_from(len).unwrap());

        for _ in 0..len {
            vector.push(T::decode(reader)?);
        }

        Ok(vector)
    }
}

impl<T: Encode> Encode for &[T] {
    type Error = Error;

    fn encode<W: io::Write>(&self, writer: &mut W) -> Result<(), Error> {
        let len = self.len();

        if len > usize::try_from(std::u32::MAX).unwrap() {
            return Err(Error::SequenceTooBig(len));
        }

        Compact(self.len() as u32).encode(writer)?;

        for elem in self.iter() {
            elem.encode(writer)?;
        }

        Ok(())
    }
}

impl Encode for String {
    type Error = Error;

    fn encode<W: io::Write>(&self, writer: &mut W) -> Result<(), Error> {
        self.as_bytes().encode(writer)
    }
}

impl Decode for String {
    type Error = Error;

    fn decode<R: io::Read>(reader: &mut R) -> Result<Self, Error> {
        let bytes: Vec<u8> = Vec::decode(reader)?;

        let s = String::from_utf8(bytes).map_err(Error::FromUtf8)?;

        Ok(s)
    }
}

#[derive(Debug, Eq, PartialEq, Clone, Copy)]
struct Compact(u32);

impl Encode for Compact {
    type Error = Error;

    fn encode<W: io::Write>(&self, writer: &mut W) -> Result<(), Error> {
        let val = self.0;

        if val < 64 {
            let val = val as u8;
            let val_with_mask = val << 2;

            val_with_mask.encode(writer)
        } else if val < ((1 << 14) - 1) {
            let val = val as u16;

            let val = val.to_le().rotate_left(2) | 0b01;

            let val = u16::from_le(val).to_le_bytes();

            writer.write_all(&val)?;

            Ok(())
        } else if val < ((1 << 30) - 1) {
            let val = val as u32;

            let val = val.to_le().rotate_left(2) | 0b10;

            let val = u32::from_le(val).to_le_bytes();

            writer.write_all(&val)?;

            Ok(())
        } else {
            unreachable!();
        }
    }
}

impl Decode for Compact {
    type Error = Error;

    fn decode<R: io::Read>(reader: &mut R) -> Result<Self, Error> {
        let byte = u8::decode(reader)?;

        let mode = byte & 0b00000011;

        match mode {
            0b00 => Ok(Compact(byte as u32 >> 2)),
            0b01 => {
                let val = u16::from_le_bytes([byte, u8::decode(reader)?]);

                Ok(Compact(val as u32 >> 2))
            }
            0b10 => {
                let val = u32::from_le_bytes([
                    byte,
                    u8::decode(reader)?,
                    u8::decode(reader)?,
                    u8::decode(reader)?,
                ]);

                Ok(Compact(val as u32 >> 2))
            }
            _ => Err(Error::UnsupportedCompactIntMode(mode)),
        }
    }
}

#[derive(Debug)]
pub enum Error {
    Io(io::Error),
    InvalidVariantInEnum(u8),
    InvalidBoolValue(u8),
    SequenceTooBig(usize),
    FromUtf8(std::string::FromUtf8Error),
    UnsupportedCompactIntMode(u8),
}

impl From<io::Error> for Error {
    fn from(err: io::Error) -> Error {
        Error::Io(err)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    fn test_impl<T: Encode + Decode + PartialEq + std::fmt::Debug>(val: T, buf: &[u8]) {
        assert_eq!(T::decode(&mut Cursor::new(buf)).unwrap(), val);

        let mut cursor = Cursor::new(Vec::new());

        val.encode(&mut cursor).unwrap();

        assert_eq!(cursor.into_inner().as_slice(), buf);
    }

    #[test]
    fn test_u32() {
        test_impl(100u32, &[0x64, 0x00, 0x00, 0x00]);
    }

    #[test]
    fn test_i16() {
        test_impl(-1234i16, &[0x2e, 0xfb]);
    }

    #[test]
    fn test_option() {
        test_impl(Some(-1234i16), &[0x01, 0x2e, 0xfb]);
        test_impl::<Option<u16>>(None, &[0x00]);
    }

    #[test]
    #[should_panic]
    fn test_option_bool_panic() {
        test_impl(Some(false), &[0x00]);
    }

    #[test]
    fn test_option_bool() {
        test_impl(OptionBool(None), &[0x00]);
        test_impl(OptionBool(Some(true)), &[0x01]);
        test_impl(OptionBool(Some(false)), &[0x02]);
    }

    #[test]
    fn test_result() {
        test_impl::<Result<i16, bool>>(Ok(-1234i16), &[0x00, 0x2e, 0xfb]);
        test_impl::<Result<i16, bool>>(Err(false), &[0x01, 0x00]);
    }

    #[test]
    fn test_bool() {
        test_impl(false, &[0x00]);
        test_impl(true, &[0x01]);
    }

    #[test]
    fn test_vector() {
        test_impl(
            vec![100u32, 100, 100],
            &[
                0b00001100, 0x64, 0x00, 0x00, 0x00, 0x64, 0x00, 0x00, 0x00, 0x64, 0x00, 0x00, 0x00,
            ],
        );
    }

    #[test]
    fn test_string() {
        test_impl("Test".to_owned(), &[0x10, 0x54, 0x65, 0x73, 0x74]);
    }

    #[test]
    fn test_compact() {
        test_impl(Compact(0), &[0x00]);
        test_impl(Compact(1), &[0x04]);
        test_impl(Compact(42), &[0xa8]);
        test_impl(Compact(69), &[0x15, 0x01]);
        test_impl(Compact(65535), &[0xfe, 0xff, 0x03, 0x00]);
    }
}
