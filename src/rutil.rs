pub use core::{fmt, marker::PhantomData};
pub use paste::paste;

pub type RegisterBank = u8;
pub const BANK0: RegisterBank = 0x00;
pub const BANK1: RegisterBank = 0x01;
pub const BANK2: RegisterBank = 0x02;
pub const BANK3: RegisterBank = 0x03;
pub const BANK4: RegisterBank = 0x04;

#[derive(Debug, PartialEq, Eq)]
pub struct Registers<'b, BUS, const BANK: RegisterBank> {
    bus: &'b mut BUS,
}

impl<'b, BUS, const BANK: RegisterBank> Registers<'b, BUS, BANK> {
    /// Create a new instance of `Registers`
    ///
    /// Requires the BUS peripheral and the chip select pin that are connected
    /// to the Registers.
    pub fn new(bus: &'b mut BUS) -> Self {
        Registers { bus }
    }

    /// Direct access to the BUS bus
    pub fn bus(&mut self) -> &mut BUS {
        self.bus
    }

    /// Current register bank
    ///
    /// This method is used to get the current register bank.
    #[inline(always)]
    pub fn current_bank(&self) -> RegisterBank {
        BANK
    }
}

/// Provides access to a register
///
/// You can get an instance for a given register using one of the methods on
/// [`Registers`].
pub struct RegAccessor<'s, 'b, R, BUS, const BANK: RegisterBank>(
    pub &'s Registers<'b, BUS, BANK>,
    pub PhantomData<R>,
);

/// Implemented for all registers
///
/// This is a mostly internal crate that should not be implemented or used
/// directly by users of this crate. It is exposed through the public API
/// though, so it can't be made private.
pub trait Register {
    /// The register index
    const ID: u8;

    /// The length of the register
    const LEN: usize;
}

/// Marker trait for registers that can be read from
///
/// This is a mostly internal crate that should not be implemented or used
/// directly by users of this crate. It is exposed through the public API
/// though, so it can't be made private.
pub trait Readable {
    /// The type that is used to read from the register
    type Read;

    /// Return the read type for this register
    fn read() -> Self::Read;

    /// Return the read type's internal buffer
    fn buffer(r: &mut Self::Read) -> &mut [u8];
}

/// Marker trait for registers that can be written to
///
/// This is a mostly internal crate that should not be implemented or used
/// directly by users of this crate. It is exposed through the public API
/// though, so it can't be made private.
pub trait Writable {
    /// The type that is used to write to the register
    type Write;

    /// Return the write type for this register
    fn write() -> Self::Write;

    /// Return the write type's internal buffer
    fn buffer(w: &mut Self::Write) -> &mut [u8];
}

/// Generates register implementations
#[macro_export]
// #[macro_use]
macro_rules! impl_register {
    (
        $bank: ident,
        $(
            $id:expr,
            $len:expr,
            $rw:tt,
            $name:ident($name_lower:ident) {
            #[$doc:meta]
            $(
                $field:ident,
                $first_bit:expr,
                $last_bit:expr,
                $ty:ty;
                #[$field_doc:meta]
            )*
            }
        )*
    ) => {
        paste! {
            pub mod [<$bank:lower>] {
                use super::*;

                $(
                    #[$doc]
                    #[allow(non_camel_case_types)]
                    pub struct $name;

                    impl Register for $name {
                        const ID:     u8    = $id;
                        const LEN:    usize = $len;
                    }

                    impl $name {
                        const HEADER_LEN: usize = 1; // Always one byte for the header
                    }

                    #[$doc]
                    pub mod $name_lower {
                        use core::fmt;


                        const HEADER_LEN: usize = super::$name::HEADER_LEN;


                        /// Used to read from the register
                        pub struct R(pub(crate) [u8; HEADER_LEN + $len]);

                        impl R {
                            $(
                                #[$field_doc]
                                pub fn $field(&self) -> $ty {
                                    use core::mem::size_of;
                                    use crate::rutil::FromBytes;

                                    // The index (in the register data) of the first
                                    // byte that contains a part of this field.
                                    const START: usize = $first_bit / 8;

                                    // The index (in the register data) of the byte
                                    // after the last byte that contains a part of this
                                    // field.
                                    const END: usize = $last_bit  / 8 + 1;

                                    // The number of bytes in the register data that
                                    // contain part of this field.
                                    const LEN: usize = END - START;

                                    // Get all bytes that contain our field. The field
                                    // might fill out these bytes completely, or only
                                    // some bits in them.
                                    let mut bytes = [0; LEN];
                                    bytes[..LEN].copy_from_slice(
                                        &self.0[START+HEADER_LEN .. END+HEADER_LEN]
                                    );

                                    // Before we can convert the field into a number and
                                    // return it, we need to shift it, to make sure
                                    // there are no other bits to the right of it. Let's
                                    // start by determining the offset of the field
                                    // within a byte.
                                    const OFFSET_IN_BYTE: usize = $first_bit % 8;

                                    if OFFSET_IN_BYTE > 0 {
                                        // Shift the first byte. We always have at least
                                        // one byte here, so this always works.
                                        bytes[0] >>= OFFSET_IN_BYTE;

                                        // If there are more bytes, let's shift those
                                        // too.
                                        // We need to allow exceeding bitshifts in this
                                        // loop, as we run into that if `OFFSET_IN_BYTE`
                                        // equals `0`. Please note that we never
                                        // actually encounter that at runtime, due to
                                        // the if condition above.
                                        let mut i = 1;
                                        #[allow(arithmetic_overflow)]
                                        while i < LEN {
                                            bytes[i - 1] |=
                                                bytes[i] << 8 - OFFSET_IN_BYTE;
                                            bytes[i] >>= OFFSET_IN_BYTE;
                                            i += 1;
                                        }
                                    }

                                    // If the field didn't completely fill out its last
                                    // byte, we might have bits from unrelated fields
                                    // there. Let's erase those before doing the final
                                    // conversion into the field's data type.
                                    const SIZE_IN_BITS: usize =
                                        $last_bit - $first_bit + 1;
                                    const BITS_ABOVE_FIELD: usize =
                                        8 - (SIZE_IN_BITS % 8);
                                    const SIZE_IN_BYTES: usize =
                                        (SIZE_IN_BITS - 1) / 8 + 1;
                                    const LAST_INDEX: usize =
                                        SIZE_IN_BYTES - 1;
                                    if BITS_ABOVE_FIELD < 8 {
                                        // Need to allow exceeding bitshifts to make the
                                        // compiler happy. They're never actually
                                        // encountered at runtime, due to the if
                                        // condition.
                                        #[allow(arithmetic_overflow)]
                                        {
                                            bytes[LAST_INDEX] <<= BITS_ABOVE_FIELD;
                                            bytes[LAST_INDEX] >>= BITS_ABOVE_FIELD;
                                        }
                                    }

                                    // Now all that's left is to convert the bytes into
                                    // the field's type. Please note that methods for
                                    // converting numbers to/from bytes are coming to
                                    // stable Rust, so we might be able to remove our
                                    // custom infrastructure here. Tracking issue:
                                    // https://github.com/rust-lang/rust/issues/52963
                                    let bytes = if bytes.len() > size_of::<$ty>() {
                                        &bytes[..size_of::<$ty>()]
                                    }
                                    else {
                                        &bytes
                                    };
                                    <$ty as FromBytes>::from_bytes(bytes)
                                }
                            )*
                        }

                        impl fmt::Debug for R {
                            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                                write!(f, "0x")?;
                                for i in (0 .. $len).rev() {
                                    write!(f, "{:02x}", self.0[HEADER_LEN + i])?;
                                }

                                Ok(())
                            }
                        }


                        /// Used to write to the register
                        pub struct W(pub(crate) [u8; HEADER_LEN + $len]);

                        impl W {
                            $(
                                #[$field_doc]
                                pub fn $field(&mut self, value: $ty) -> &mut Self {
                                    use crate::rutil::ToBytes;

                                    // Convert value into bytes
                                    let source = <$ty as ToBytes>::to_bytes(value);

                                    // Now, let's figure out where the bytes are located
                                    // within the register array.
                                    const START:          usize = $first_bit / 8;
                                    const END:            usize = $last_bit  / 8 + 1;
                                    const OFFSET_IN_BYTE: usize = $first_bit % 8;

                                    // Also figure out the length of the value in bits.
                                    // That's going to come in handy.
                                    const LEN: usize = $last_bit - $first_bit + 1;


                                    // We need to track how many bits are left in the
                                    // value overall, and in the value's current byte.
                                    let mut bits_left         = LEN;
                                    let mut bits_left_in_byte = 8;

                                    // We also need to track how many bits have already
                                    // been written to the current target byte.
                                    let mut bits_written_to_byte = 0;

                                    // Now we can take the bytes from the value, shift
                                    // them, mask them, and write them into the target
                                    // array.
                                    let mut source_i  = 0;
                                    let mut target_i  = START;
                                    while target_i < END {
                                        // Values don't always end at byte boundaries,
                                        // so we need to mask the bytes when writing to
                                        // the slice.
                                        // Let's start out assuming we can write to the
                                        // whole byte of the slice. This will be true
                                        // for the middle bytes of our value.
                                        let mut mask = 0xff;

                                        // Let's keep track of the offset we're using to
                                        // write to this byte. We're going to need it.
                                        let mut offset_in_this_byte = 0;

                                        // If this is the first byte we're writing to
                                        // the slice, we need to remove the lower bits
                                        // of the mask.
                                        if target_i == START {
                                            mask <<= OFFSET_IN_BYTE;
                                            offset_in_this_byte = OFFSET_IN_BYTE;
                                        }

                                        // If this is the last byte we're writing to the
                                        // slice, we need to remove the higher bits of
                                        // the mask. Please note that we could be
                                        // writing to _both_ the first and the last
                                        // byte.
                                        if target_i == END - 1 {
                                            let shift =
                                                8 - bits_left - offset_in_this_byte;
                                            mask <<= shift;
                                            mask >>= shift;
                                        }

                                        mask <<= bits_written_to_byte;

                                        // Read the value from `source`
                                        let value = source[source_i]
                                            >> 8 - bits_left_in_byte
                                            << offset_in_this_byte
                                            << bits_written_to_byte;

                                        // Zero the target bits in the slice, then write
                                        // the value.
                                        self.0[HEADER_LEN + target_i] &= !mask;
                                        self.0[HEADER_LEN + target_i] |= value & mask;

                                        // The number of bits that were expected to be
                                        // written to the target byte.
                                        let bits_needed = mask.count_ones() as usize;

                                        // The number of bits we actually wrote to the
                                        // target byte.
                                        let bits_used = bits_needed.min(
                                            bits_left_in_byte - offset_in_this_byte
                                        );

                                        bits_left -= bits_used;
                                        bits_written_to_byte += bits_used;

                                        // Did we use up all the bits in the source
                                        // byte? If so, we can move on to the next one.
                                        if bits_left_in_byte > bits_used {
                                            bits_left_in_byte -= bits_used;
                                        }
                                        else {
                                            bits_left_in_byte =
                                                8 - (bits_used - bits_left_in_byte);

                                            source_i += 1;
                                        }

                                        // Did we write all the bits in the target byte?
                                        // If so, we can move on to the next one.
                                        if bits_used == bits_needed {
                                            target_i += 1;
                                            bits_written_to_byte = 0;
                                        }
                                    }

                                    self
                                }
                            )*
                        }
                    }

                    impl_rw!($rw, $name, $name_lower, $len);
                )*
            }

            impl<'b, BUS> Registers<'b, BUS, $bank> {
                $(
                    #[$doc]
                    pub fn $name_lower(&mut self) -> RegAccessor<'_, 'b, [<$bank:lower>]::$name, BUS, $bank> {
                        RegAccessor(self, PhantomData)
                    }
                )*
            }
        }
    }
}

// Helper macro, used internally by `impl_register!`
#[macro_export]
macro_rules! impl_rw {
    (RO, $name:ident, $name_lower:ident, $len:expr) => {
        impl_rw!(@R, $name, $name_lower, $len);
    };
    (RW, $name:ident, $name_lower:ident, $len:expr) => {
        impl_rw!(@R, $name, $name_lower, $len);
        impl_rw!(@W, $name, $name_lower, $len);
    };

    (@R, $name:ident, $name_lower:ident, $len:expr) => {
        impl Readable for $name {
            type Read = $name_lower::R;

            fn read() -> Self::Read {
                $name_lower::R([0; Self::HEADER_LEN + $len])
            }

            fn buffer(r: &mut Self::Read) -> &mut [u8] {
                &mut r.0
            }
        }
    };
    (@W, $name:ident, $name_lower:ident, $len:expr) => {
        impl Writable for $name {
            type Write = $name_lower::W;

            fn write() -> Self::Write {
                $name_lower::W([0; Self::HEADER_LEN + $len])
            }

            fn buffer(w: &mut Self::Write) -> &mut [u8] {
                &mut w.0
            }
        }
    };
}

pub trait FromBytes {
    fn from_bytes(bytes: &[u8]) -> Self;
}

pub trait ToBytes {
    type Bytes;
    fn to_bytes(self) -> Self::Bytes;
}

/// Internal macro used to implement `FromBytes`/`ToBytes`
#[macro_export]
macro_rules! impl_bytes {
    ($($ty:ty,)*) => {
        $(
            impl FromBytes for $ty {
                fn from_bytes(bytes: &[u8]) -> Self {
                    let mut val = 0;

                    for (i, &b) in bytes.iter().enumerate() {
                        val |= (b as $ty) << (i * 8);
                    }

                    val
                }
            }

            impl ToBytes for $ty {
                type Bytes = [u8; ::core::mem::size_of::<$ty>()];

                fn to_bytes(self) -> Self::Bytes {
                    let mut bytes = [0; ::core::mem::size_of::<$ty>()];

                    for (i, b) in bytes.iter_mut().enumerate() {
                        let shift = 8 * i;
                        let mask  = 0xff << shift;

                        *b = ((self & mask) >> shift) as u8;
                    }

                    bytes
                }
            }
        )*
    }
}

impl_bytes! {
    u8,
    u16,
    u32,
    u64,
    u128,
}
