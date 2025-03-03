use std::fmt::{Debug, Display, Formatter, Result};

use rand::{rngs::StdRng, RngCore, SeedableRng};
use uuid::{Context, Timestamp, Uuid};

const NUM_BYTES: usize = 16;
const NUM_NODE_BYTES: usize = 6;

type OrdVersionBits = u8;
const ORD_VERSION_BITS6: OrdVersionBits = 6;
const ORD_VERSION_BITS7: OrdVersionBits = 7;

//
// some inspiration was taken from the following blog post
// https://www.percona.com/blog/store-uuid-optimized-way/
//

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct OrdUuid([u8; NUM_BYTES]);

impl Debug for OrdUuid {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "OrdUuid({})", self)
    }
}

#[cfg(test)]
mod test_equality {
    use super::*;

    #[test]
    fn lsb_diff() {
        let mut v1 = [0; NUM_BYTES];
        v1[NUM_BYTES - 1] = 1;
        let mut v2 = [0; NUM_BYTES];
        v2[NUM_BYTES - 1] = 2;
        let v1 = OrdUuid(v1);
        let v2 = OrdUuid(v2);
        assert_ne!(v1, v2);
    }

    #[test]
    fn msb_diff() {
        let mut v1 = [0; NUM_BYTES];
        v1[0] = 1;
        let mut v2 = [0; NUM_BYTES];
        v2[0] = 2;
        let v1 = OrdUuid(v1);
        let v2 = OrdUuid(v2);
        assert_ne!(v1, v2);
    }

    #[test]
    fn lsb_msb_diff() {
        let mut v1 = [0; NUM_BYTES];
        v1[NUM_BYTES - 1] = 1;
        let mut v2 = [0; NUM_BYTES];
        v2[0] = 1;
        let v1 = OrdUuid(v1);
        let v2 = OrdUuid(v2);
        assert_ne!(v1, v2);
    }

    #[test]
    fn zero_and_v6() {
        let g = OrdUuidGen::new();
        let v1 = OrdUuid([0; NUM_BYTES]);
        let v2 = OrdUuid([0; NUM_BYTES]);
        assert_eq!(v1, v2);
        assert_eq!(v1 == v2, true);
        assert_eq!(
            format!("{:?}", v1),
            "OrdUuid(00000000000000000000000000000000)"
        );
        let t1 = g.new_v6();
        assert_ne!(t1, v2);
        let t2 = g.new_v6();
        assert_ne!(t2, v2);
        assert_ne!(t1, t2);
        let v = g.new_v6();
        assert_eq!(format!("OrdUuid({})", format!("{}", v)), format!("{:?}", v));
    }
}

#[cfg(test)]
mod test_ordering {
    use super::*;

    #[test]
    fn lsb_diff() {
        let mut v1 = [0; NUM_BYTES];
        v1[NUM_BYTES - 1] = 1;
        let mut v2 = [0; NUM_BYTES];
        v2[NUM_BYTES - 1] = 2;
        let v1 = OrdUuid(v1);
        let v2 = OrdUuid(v2);
        assert_ne!(v1, v2);
        assert_eq!(v1 < v2, true);
        assert_eq!(v1 > v2, false);
        assert_eq!(v1 == v2, false);
        let set = [v1.clone(), v2.clone()];
        assert_eq!(set.iter().min(), Some(&v1.clone()));
        assert_eq!(set.iter().max(), Some(&v2.clone()));
        let set = [v2.clone(), v1.clone()];
        assert_eq!(set.iter().min(), Some(&v1.clone()));
        assert_eq!(set.iter().max(), Some(&v2.clone()));
    }

    #[test]
    fn msb_diff() {
        let mut v1 = [0; NUM_BYTES];
        v1[0] = 1;
        let mut v2 = [0; NUM_BYTES];
        v2[0] = 2;
        let v1 = OrdUuid(v1);
        let v2 = OrdUuid(v2);
        assert_ne!(v1, v2);
        assert_eq!(v1 < v2, true);
        assert_eq!(v1 > v2, false);
        assert_eq!(v1 == v2, false);
        let set = [v1.clone(), v2.clone()];
        assert_eq!(set.iter().min(), Some(&v1.clone()));
        assert_eq!(set.iter().max(), Some(&v2.clone()));
        let set = [v2.clone(), v1.clone()];
        assert_eq!(set.iter().min(), Some(&v1.clone()));
        assert_eq!(set.iter().max(), Some(&v2.clone()));
    }

    #[test]
    fn lsb_msb_diff() {
        let mut v1 = [0; NUM_BYTES];
        v1[NUM_BYTES - 1] = 1;
        let mut v2 = [0; NUM_BYTES];
        v2[0] = 1;
        let v1 = OrdUuid(v1);
        let v2 = OrdUuid(v2);
        assert_ne!(v1, v2);
        assert_eq!(v1 < v2, true);
        assert_eq!(v1 > v2, false);
        assert_eq!(v1 == v2, false);
        let set = [v1.clone(), v2.clone()];
        assert_eq!(set.iter().min(), Some(&v1.clone()));
        assert_eq!(set.iter().max(), Some(&v2.clone()));
        let set = [v2.clone(), v1.clone()];
        assert_eq!(set.iter().min(), Some(&v1.clone()));
        assert_eq!(set.iter().max(), Some(&v2.clone()));
    }

    #[test]
    fn zero() {
        // verify zero value case
        {
            let v1 = OrdUuid([0; NUM_BYTES]);
            let v2 = OrdUuid([0; NUM_BYTES]);
            assert_eq!(v1 > v2, false);
            assert_eq!(v1 < v2, false);
            assert_eq!(v1 == v2, true);
        }

        // verify v6 case
        {
            let g = OrdUuidGen::new();
            let v1 = g.new_v6();
            let v2 = g.new_v6();
            assert_eq!(v1 > v2, false);
            assert_eq!(v1 < v2, true);
            assert_eq!(v1 == v2, false);
            let set = [v1.clone(), v2.clone()];
            assert_eq!(set.iter().min(), Some(&v1.clone()));
            assert_eq!(set.iter().max(), Some(&v2.clone()));
            let set = [v2.clone(), v1.clone()];
            assert_eq!(set.iter().min(), Some(&v1.clone()));
            assert_eq!(set.iter().max(), Some(&v2.clone()));
        }
    }
}

impl OrdUuid {
    fn as_u128(&self) -> u128 {
        ((self.0[0] as u128) << 120)
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
            | self.0[15] as u128
    }

    pub fn as_bytes(&self) -> [u8; NUM_BYTES] {
        self.0
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

#[cfg(test)]
mod test_ord_uuid_x_as_bytes {
    use std::any::Any;

    use super::*;

    #[test]
    fn unique_nib_pairs() {
        let input = 0x112233445566778899AABBCCDDEEFFE5;
        let input = OrdUuid(u128_to_bytes(input));
        let dst = input.as_bytes();
        let src = &input.0;
        assert_eq!(src, &dst);
        assert_ne!(src as *const dyn Any, &dst as *const dyn Any);
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

pub struct OrdUuidGen {
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
    // // move clock seq high and low bits, leaving variants bits prefix behind
    // // 0x00000000000000003FFF
    // | ((v & (0x3FFF << 48) ) << 6)
    // // 0xFFFFFFFFFFFFFFFFFFC0
    // //
    // // preserve node bits with multicast bit moved to end
    // | ((v & (0xFE << 40)) << 6)
    //
    // combine the above blocks
    // moves clock seq bits without variant bits prefix
    // also move first byte of node without last multicast bit
    | ((v & (0x3FFFFE << 40) ) << 6)
    //
    // rest of node (5 bytes)
    //
    | ((v & 0xFFFFFFFFFF) << 7)
    // | ((v & (1 << 40)) >> 34)
    // not using the above as this is for v1
    // and it should be using a mac address
    // but RFC 4122 says this bit should be set
    // if not using a mac address and we're definitely not
    //
    //
    // | 0x40
    // | 0x21
    // combining the above as well into `0x61`
    //
    // set variant and version bits
    | 0x61
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
        // clock seq and first byte of node
        | ((v >> 6) & (0x3FFFFE << 40))
        // rest of node (5 bytes)
        | ((v >> 7) & 0xFFFFFFFFFF)
        | ((v << 34) & (1 << 40))
        // variant
        | ((v << 58) & (0xC << 60))
        // version
        | ((v << 76) & (0xF << 76))
    }

    #[test]
    fn returns_unique_nib_pairs() {
        let expected = 0x112233445566778899aabbccddeeffe1 as u128;
        let input = undo_order_bits_lexically_for_v1(expected);
        let actual = order_bits_lexically_for_v1(input);
        assert_eq!(actual, expected);
    }

    #[test]
    fn unique_nib_pairs() {
        let input = 0x1122334455661788D9AABBCCDDEEFFe5;
        let actual = order_bits_lexically_for_v1(input);
        let expected = 0x78855661122334466aaee66ef77ff2e1 as u128;
        assert_eq!(format!("{:x}", actual), format!("{:x}", expected));
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
    // // move clock seq high and low bits, leaving variants bits prefix behind
    // // 0x00000000000000003FFF
    // | ((v & (0x3FFF << 48) ) << 6)
    // // 0xFFFFFFFFFFFFFFFFFFC0
    // //
    // // preserve node bits
    // | ((v & 0xFFFFFFFFFFFF) << 6)
    //
    // combine the above blocks
    // moves clock seq bits without variant bits prefix
    | ((v & 0x3FFF_FFFFFFFFFFFF) << 6)
    //
    // set variant and version bits
    | 0x24
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
        // clock seq and node
        | ((v >> 6) & 0x3FFF_FFFFFFFFFFFF)
        // variant
        | ((v << 58) & (0xC << 60))
        // version
        | ((v << 76) & (0xF << 76))
    }

    #[test]
    fn returns_unique_nib_pairs() {
        let expected = 0x112233445566778899aabbccddeeffe4 as u128;
        let input = undo_order_bits_lexically_for_v4(expected);
        let actual = order_bits_lexically_for_v4(input);
        assert_eq!(actual, expected);
    }

    #[test]
    fn unique_nib_pairs() {
        let input = 0x1122334455664788D9AABBCCDDEEFFe5;
        let actual = order_bits_lexically_for_v4(input);
        let expected = 0x78855661122334466aaef3377bbff964 as u128;
        assert_eq!(actual, expected);
    }
}

fn order_bits_lexically_for_ord_v(v: u128, version_bits: OrdVersionBits) -> u128 {
    //
    // preserve before version bits
    // 0xFFFFFFFFFFFF00000000
    (v & (0xFFFFFFFFFFFF << 80))
    // 0xFFFFFFFFFFFF00000000
    //
    // move after version - before variant bits
    // 0x0000000000000FFF0000
    | ((v & (0xFFF << 64)) << 4)
    // 0xFFFFFFFFFFFFFFF00000
    //
    // move after variant bits (including node bits)
    // 0x00000000000000003FFF
    | ((v & 0x3FFF_FFFFFFFFFFFF) << 6)
    //
    // set variant and version bits
    | 0x20 | (version_bits as u128)
}

#[cfg(test)]
mod test_order_bits_lexically_for_ord_v {
    use super::*;

    fn undo_order_bits_lexically_for_ord_v(v: u128, version_bits: OrdVersionBits) -> u128 {
        // time high
        (v & (0xFFFFFFFFFFFF << 80))
        // time low
        | ((v >> 4) & (0xFFF << 64))
        // clock seq and node bits
        | ((v >> 6) & 0x3FFF_FFFFFFFFFFFF)
        // variant
        | ((v << 58) & (0xC << 60))
        // version
        | ((version_bits as u128) << 76)
    }

    #[test]
    fn returns_unique_nib_pairs_v6() {
        let expected = 0x112233445566778899aabbccddeeffe6 as u128;
        let input = undo_order_bits_lexically_for_ord_v(expected, ORD_VERSION_BITS6);
        let actual = order_bits_lexically_for_ord_v(input, ORD_VERSION_BITS6);
        assert_eq!(format!("{:x}", actual), format!("{:x}", expected));
    }

    #[test]
    fn unique_nib_pairs_v6() {
        let input = 0x1122334455666788D9AABBCCDDEEFFe5;
        let actual = order_bits_lexically_for_ord_v(input, ORD_VERSION_BITS6);
        let expected = 0x11223344556678866aaef3377bbff966 as u128;
        assert_eq!(actual, expected);
    }

    #[test]
    fn returns_unique_nib_pairs_v7() {
        let expected = 0x112233445566778899aabbccddeeffe7 as u128;
        let input = undo_order_bits_lexically_for_ord_v(expected, ORD_VERSION_BITS7);
        let actual = order_bits_lexically_for_ord_v(input, ORD_VERSION_BITS7);
        assert_eq!(format!("{:x}", actual), format!("{:x}", expected));
    }

    #[test]
    fn unique_nib_pairs_v7() {
        let input = 0x1122334455667788D9AABBCCDDEEFFe5;
        let actual = order_bits_lexically_for_ord_v(input, ORD_VERSION_BITS7);
        let expected = 0x11223344556678866aaef3377bbff967 as u128;
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
        let mut rng = StdRng::from_os_rng();
        let seed = rng.next_u32() as u16;
        rng.fill_bytes(&mut node);

        OrdUuidGen {
            ctx: Context::new(seed),
            node: node,
        }
    }

    pub fn new_v1(&self) -> OrdUuid {
        // https://datatracker.ietf.org/doc/html/rfc4122

        let ts = Timestamp::now(&self.ctx);

        let v = Uuid::new_v1(ts, &self.node).as_u128();

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
        // is to simply reorder the bits and remain v1 compatible with simple bit shifts

        OrdUuid(u128_to_bytes(v))
    }

    pub fn new_v4(&self) -> OrdUuid {
        // https://datatracker.ietf.org/doc/html/rfc4122

        let ts = Timestamp::now(&self.ctx);

        let v = order_bits_lexically_for_v4(Uuid::new_v1(ts, &self.node).as_u128());

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
        // is to simply reorder the bits and remain v4 compatible with simple bit shifts

        OrdUuid(u128_to_bytes(v))
    }

    pub fn new_v6(&self) -> OrdUuid {
        // https://www.ietf.org/archive/id/draft-peabody-dispatch-new-uuid-format-01.html#name-uuidv6-layout-and-bit-order

        let ts = Timestamp::now(&self.ctx);

        let v = order_bits_lexically_for_ord_v(
            Uuid::new_v6(ts, &self.node).as_u128(),
            ORD_VERSION_BITS6,
        );

        // note that the LSBs will always be 0b10_0110
        //
        // the leading `10` bits are from the variant field
        // which is guaranteed to be set to 10 in v4 of rfc4122
        // the last `0110` bits are from the version field
        // which indicates the uuid version ( obviously 6 in this case )
        //
        // these last six bits could be reclaimed and used for another purpose
        // however that purpose should likely not be to increase the number of
        // bits used to ensure uniqueness of a uuid node or randomness if the goal
        // is to simply reorder the bits and remain v4 compatible with simple bit shifts

        OrdUuid(u128_to_bytes(v))
    }

    pub fn new_v7(&self) -> OrdUuid {
        // https://www.ietf.org/archive/id/draft-peabody-dispatch-new-uuid-format-01.html#name-uuidv6-layout-and-bit-order

        let ts = Timestamp::now(&self.ctx);

        let v = order_bits_lexically_for_ord_v(Uuid::new_v7(ts).as_u128(), ORD_VERSION_BITS7);

        // note that the LSBs will always be 0b10_0111
        //
        // the leading `10` bits are from the variant field
        // which is guaranteed to be set to 10 in v4 of rfc4122
        // the last `0111` bits are from the version field
        // which indicates the uuid version ( obviously 7 in this case )
        //
        // these last six bits could be reclaimed and used for another purpose
        // however that purpose should likely not be to increase the number of
        // bits used to ensure uniqueness of a uuid node or randomness if the goal
        // is to simply reorder the bits and remain v4 compatible with simple bit shifts

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
        let oug = OrdUuidGen::new();
        let v = oug.new_v4().as_u128() & mask;
        assert_eq!(0b10_0100, 0x24);
        assert_eq!(v, 0x24);
    }

    #[test]
    fn new_v4_node_reuse() {
        let mask = 0x3FFFFFFFFFFFFF;
        let oug = OrdUuidGen::new();
        let v1 = oug.new_v4().as_u128();
        let mut v2 = v1;
        while v1 == v2 {
            v2 = oug.new_v4().as_u128();
        }
        assert_ne!(v1, v2);
        assert_eq!(v1 & mask, v2 & mask);
    }

    #[test]
    fn new_v6() {
        let mask = 0x3FFFFFFFFFFFFF;
        let oug = OrdUuidGen::new();
        let v = oug.new_v6().as_u128() & mask;
        let expected = // node with multicast bit always set, with variant, with version
            ((oug.node[0] as u128) << 46)
            | ((oug.node[1] as u128) << 38)
            | ((oug.node[2] as u128) << 30)
            | ((oug.node[3] as u128) << 22)
            | ((oug.node[4] as u128) << 14)
            | ((oug.node[5] as u128) << 6)
            | 0x26;
        assert_eq!(0b10_0110, 0x26);
        assert_eq!(v, expected);
    }

    #[test]
    fn new_v7() {
        let mask = 0x3F;
        let oug = OrdUuidGen::new();
        let v = oug.new_v7().as_u128() & mask;
        assert_eq!(0b10_0111, 0x27);
        assert_eq!(v, 0x27);
    }
}
