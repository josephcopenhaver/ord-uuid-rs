use std::fmt::{Display, Formatter, Result};

use rand::{rngs::StdRng, RngCore, SeedableRng};
use uuid::{Context, Timestamp, Uuid};

const NUM_BYTES: usize = 16;
const NUM_NODE_BYTES: usize = 6;

pub struct OrdUuid([u8; NUM_BYTES]);

impl OrdUuid {
    fn as_u128(&self) -> u128 {
        return ((self.0[0] as u128) << 120)
            | ((self.0[1] as u128) << 112)
            | ((self.0[2] as u128) << 104)
            | ((self.0[3] as u128) << 96)
            | ((self.0[4] as u128) << 88)
            | ((self.0[5] as u128) << 80)
            | ((self.0[6] as u128) << 72)
            | ((self.0[7] as u128) << 64)
            | ((self.0[8] as u128) << 56)
            | ((self.0[9] as u128) << 48)
            | ((self.0[10] as u128) << 40)
            | ((self.0[11] as u128) << 32)
            | ((self.0[12] as u128) << 24)
            | ((self.0[13] as u128) << 16)
            | ((self.0[14] as u128) << 8)
            | self.0[15] as u128;
    }
}

#[cfg(test)]
mod test_ord_uuid_x_as_u128 {
    use super::*;

    #[test]
    fn unique_nib_pairs() {
        let input = 0x112233445566778899AABBCCDDEEFFE5;
        let actual = OrdUuid(u128_to_bytes(input)).as_u128();
        let expected = input;
        assert_eq!(actual, expected);
    }
}

impl Display for OrdUuid {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "{:032x}", self.as_u128())
    }
}

#[cfg(test)]
mod test_ord_uuid_x_fmt {
    use super::*;

    #[test]
    fn unique_nib_pairs() {
        let input = 0x112233445566778899AABBCCDDEEFFE5;
        let actual = format!("{}", OrdUuid(u128_to_bytes(input)));
        let expected = "112233445566778899aabbccddeeffe5";
        assert_eq!(actual, expected);
    }

    #[test]
    fn leading_zero() {
        let input = 0x012233445566778899AABBCCDDEEFFE5;
        let actual = format!("{}", OrdUuid(u128_to_bytes(input)));
        let expected = "012233445566778899aabbccddeeffe5";
        assert_eq!(actual, expected);
    }
}

struct OrdUuidGen {
    rng: StdRng,
    ctx: Context,
    node: [u8; NUM_NODE_BYTES],
}

fn order_bits_lexically_for_v1(v: u128) -> u128 {
    //
    // move time high nibs
    // 0x0000000000000FFF0000
    ((v & (0xFFF << 64)) << 52)
    // 0xFFF00000000000000000
    //
    // move time mid nibs
    // 0x00000000FFFF00000000
    | ((v & (0xFFFF << 80)) << 20)
    // 0xFFFFFFF0000000000000
    //
    // move time low nibs
    // 0xFFFFFFFF000000000000
    | ((v & (0xFFFFFFFF << 96)) >> 28)
    // 0xFFFFFFFFFFFFFFF00000
    //
    // move clock seq high and low bits, leaving variants bits prefix behind
    // 0x00000000000000003FFF
    | ((v & (0x3FFF << 48) ) << 6)
    // 0xFFFFFFFFFFFFFFFFFFC0
    //
    // preserve node bits with multicast bit moved to end
    | ((v & (0xFE << 40)) << 6)
    | ((v & 0xFFFFFFFFFF) << 7)
    | ((v & (1 << 40)) >> 34)
    //
    // move two variant bits
    // 0x0000000000000000C000
    | ((v & (3 << 62)) >> 58) // shift all the way to the right, but leave a nib of space for version
    //
    // move version nib
    // 0x000000000000F0000000
    | ((v & (0xF << 76)) >> 76)
}

#[cfg(test)]
mod test_order_bits_lexically_for_v1 {
    use super::*;

    fn undo_order_bits_lexically_for_v1(v: u128) -> u128 {
        // time high
        ((v >> 52) & (0xFFF << 64))
        // time mid
        | ((v >> 20) & (0xFFFF << 80))
        // time low
        | ((v << 28) & (0xFFFFFFFF << 96))
        // clock seq
        | ((v >> 6) & (0x3FFF << 48))
        // node
        | ((v >> 6) & (0xFE << 40))
        | ((v >> 7) & 0xFFFFFFFFFF)
        | ((v << 34) & (1 << 40))
        // variant
        | ((v << 58) & (0xC << 60))
        // version
        | ((v << 76) & (0xF << 76))
    }

    #[test]
    fn returns_unique_nib_pairs() {
        let expected = 0x112233445566778899aabbccddeeffe5 as u128;
        let input = undo_order_bits_lexically_for_v1(expected);
        let actual = order_bits_lexically_for_v1(input);
        assert_eq!(actual, expected);
    }

    #[test]
    fn unique_nib_pairs() {
        let input = 0x112233445566778899AABBCCDDEEFFe5;
        let actual = order_bits_lexically_for_v1(input);
        let expected = 0x78855661122334466aaee66ef77ff2e7 as u128;
        assert_eq!(actual, expected);
    }
}

fn order_bits_lexically_for_v4(v: u128) -> u128 {
    //
    // move time high nibs
    // 0x0000000000000FFF0000
    ((v & (0xFFF << 64)) << 52)
    // 0xFFF00000000000000000
    //
    // move time mid nibs
    // 0x00000000FFFF00000000
    | ((v & (0xFFFF << 80)) << 20)
    // 0xFFFFFFF0000000000000
    //
    // move time low nibs
    // 0xFFFFFFFF000000000000
    | ((v & (0xFFFFFFFF << 96)) >> 28)
    // 0xFFFFFFFFFFFFFFF00000
    //
    // move clock seq high and low bits, leaving variants bits prefix behind
    // 0x00000000000000003FFF
    | ((v & (0x3FFF << 48) ) << 6)
    // 0xFFFFFFFFFFFFFFFFFFC0
    //
    // preserve node bits
    | ((v & 0xFFFFFFFFFFFF) << 6)
    //
    // move two variant bits
    // 0x0000000000000000C000
    | ((v & (3 << 62)) >> 58) // shift all the way to the right, but leave a nib of space for version
    //
    // move version nib
    // 0x000000000000F0000000
    | ((v & (0xF << 76)) >> 76)
}

#[cfg(test)]
mod test_order_bits_lexically_for_v4 {
    use super::*;

    fn undo_order_bits_lexically_for_v4(v: u128) -> u128 {
        // time high
        ((v >> 52) & (0xFFF << 64))
        // time mid
        | ((v >> 20) & (0xFFFF << 80))
        // time low
        | ((v << 28) & (0xFFFFFFFF << 96))
        // clock seq
        | ((v >> 6) & (0x3FFF << 48))
        // node
        | ((v >> 6) & 0xFFFFFFFFFFFF)
        // variant
        | ((v << 58) & (0xC << 60))
        // version
        | ((v << 76) & (0xF << 76))
    }

    #[test]
    fn returns_unique_nib_pairs() {
        let expected = 0x112233445566778899aabbccddeeffe5 as u128;
        let input = undo_order_bits_lexically_for_v4(expected);
        let actual = order_bits_lexically_for_v4(input);
        assert_eq!(actual, expected);
    }

    #[test]
    fn unique_nib_pairs() {
        let input = 0x112233445566778899AABBCCDDEEFFe5;
        let actual = order_bits_lexically_for_v4(input);
        let expected = 0x78855661122334466aaef3377bbff967 as u128;
        assert_eq!(actual, expected);
    }
}

fn u128_to_bytes(v: u128) -> [u8; NUM_BYTES] {
    [
        (v >> 120) as u8,
        (v >> 112) as u8,
        (v >> 104) as u8,
        (v >> 96) as u8,
        (v >> 88) as u8,
        (v >> 80) as u8,
        (v >> 72) as u8,
        (v >> 64) as u8,
        (v >> 56) as u8,
        (v >> 48) as u8,
        (v >> 40) as u8,
        (v >> 32) as u8,
        (v >> 24) as u8,
        (v >> 16) as u8,
        (v >> 8) as u8,
        v as u8,
    ]
}

#[cfg(test)]
mod test_u128_to_bytes {
    use super::*;

    #[test]
    fn zero() {
        let value = 0 as u128;
        let expected = [0x00 as u8; NUM_BYTES];
        assert_eq!(u128_to_bytes(value), expected);
    }

    #[test]
    fn max() {
        let value = u128::MAX;
        let expected = [0xFF as u8; NUM_BYTES];
        assert_eq!(u128_to_bytes(value), expected);
    }

    #[test]
    fn nib_cycle_set_unset() {
        let value: u128 = 0xF0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0;
        let expected = [0xF0 as u8; NUM_BYTES];
        assert_eq!(u128_to_bytes(value), expected);
    }

    #[test]
    fn nib_cycle_unset_set() {
        let value: u128 = 0x0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F;
        let expected = [0x0F as u8; NUM_BYTES];
        assert_eq!(u128_to_bytes(value), expected);
    }

    #[test]
    fn bit_cycle_set_unset() {
        let value: u128 = 0xAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA;
        let expected = [0xAA as u8; NUM_BYTES];
        assert_eq!(u128_to_bytes(value), expected);
    }

    #[test]
    fn bit_cycle_unset_set() {
        let value: u128 = 0x55555555555555555555555555555555;
        let expected = [0x55 as u8; NUM_BYTES];
        assert_eq!(u128_to_bytes(value), expected);
    }
}

impl OrdUuidGen {
    pub fn new() -> Self {
        let mut node = [0; NUM_NODE_BYTES];
        let mut rng = StdRng::from_entropy();
        let seed = rng.next_u32() as u16;
        rng.fill_bytes(&mut node);

        OrdUuidGen {
            rng: rng,
            ctx: Context::new(seed),
            node: node,
        }
    }

    pub fn new_v1(&self) -> OrdUuid {
        // https://datatracker.ietf.org/doc/html/rfc4122

        let ts = Timestamp::now(&self.ctx);

        let mut node = self.node;

        // set the multicast bit as uuid is not based on mac address as required by the RFC 4122
        node[0] |= 1;

        let v = Uuid::new_v1(ts, &node).as_u128();

        let v = order_bits_lexically_for_v1(v);

        // note that the LSBs will always be 0b110_0001
        //
        // leading 1 is the last bit of the node which
        // is the multicast bit and must be set because
        // we are not sampling from a mac address
        //
        // the next `10` bits are from the variant field
        // which is guaranteed to be set to 10 in v1 of rfc4122
        // the last `0001` bits are from the version field
        // which indicates the uuid version ( obviously 1 in this case )
        //
        // these last seven bits could be reclaimed and used for another purpose
        // however that purpose should likely not be to increase the number of
        // bits used to ensure uniqueness of a uuid node or randomness if the goal
        // is to simply reorder the bits and remain v1 compatible

        OrdUuid(u128_to_bytes(v))
    }

    pub fn new_v4(&mut self) -> OrdUuid {
        // https://datatracker.ietf.org/doc/html/rfc4122

        let ts = Timestamp::now(&self.ctx);

        let mut bytes = [0 as u8; NUM_NODE_BYTES];
        self.rng.fill_bytes(&mut bytes);

        // `^ (0b101 as u128)` converts the ordered uuid v1 to a v4 uuid with a time based prefix
        let v = order_bits_lexically_for_v4(Uuid::new_v1(ts, &bytes).as_u128()) ^ (0b101 as u128);

        // note that the LSBs will always be 0b10_0100
        //
        // the leading `10` bits are from the variant field
        // which is guaranteed to be set to 10 in v4 of rfc4122
        // the last `0100` bits are from the version field
        // which indicates the uuid version ( obviously 4 in this case )
        //
        // these last six bits could be reclaimed and used for another purpose
        // however that purpose should likely not be to increase the number of
        // bits used to ensure uniqueness of a uuid node or randomness if the goal
        // is to simply reorder the bits and remain v4 compatible

        OrdUuid(u128_to_bytes(v))
    }
}

#[cfg(test)]
mod test_ord_uuid_gen {
    use super::*;

    #[test]
    fn new() {
        let v = OrdUuidGen::new();
        assert_eq!(v.node.len(), NUM_NODE_BYTES);
    }

    #[test]
    fn new_v1() {
        let mask = 0x3FFFFFFFFFFFFF;
        let oug = OrdUuidGen::new();
        let v = oug.new_v1().as_u128() & mask;
        let expected = // node with multicast bit always set, with variant, with version
            (((oug.node[0] & 0xFE) as u128) << 46)
            | ((oug.node[1] as u128) << 39)
            | ((oug.node[2] as u128) << 31)
            | ((oug.node[3] as u128) << 23)
            | ((oug.node[4] as u128) << 15)
            | ((oug.node[5] as u128) << 7)
            | 0x61;
        assert_eq!(0b110_0001, 0x61);
        assert_eq!(v, expected);
    }

    #[test]
    fn new_v4() {
        let mask = 0x3F;
        let mut oug = OrdUuidGen::new();
        let v = oug.new_v4().as_u128() & mask;
        assert_eq!(0b10_0100, 0x24);
        assert_eq!(v, 0x24);
    }
}

pub fn new_v4(rng: &mut StdRng) -> OrdUuid {
    // https://datatracker.ietf.org/doc/html/rfc4122

    let mut bytes = [0 as u8; NUM_BYTES];
    {
        rng.fill_bytes(&mut bytes);
        let b = &mut bytes[NUM_BYTES - 1];
        *b = (*b & 0xC0) | 0x24;
    }

    // note that the LSBs will always be 0b10_0100
    //
    // the leading `10` bits are from the variant field
    // which is guaranteed to be set to 10 in v1
    // the last `0100` bits are from the version field
    // which indicates the uuid version ( obviously 4 in this case )
    //
    // these last six bits could be reclaimed and used for another purpose
    // however that purpose should likely not be to increase the number of
    // bits used to ensure uniqueness of a uuid node or randomness if the goal
    // is to simply reorder the bits and remain v1 compatible

    OrdUuid(bytes)
}

#[cfg(test)]
mod test_new_v4 {
    use super::*;

    #[test]
    fn end_in_0b10_0100() {
        let mut rng = StdRng::from_entropy();
        let mask = 0x3F;

        let v = new_v4(&mut rng).as_u128() & mask;
        let expected = 0b10_0100;
        assert_eq!(expected, 0x24);
        assert_eq!(v, expected);
    }
}
