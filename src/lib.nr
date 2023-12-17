use dep::std::println;
use dep::curves::ecdsa_secp256k1::swcurve::{Point, Curve};
use dep::curves::ecdsa_secp256k1::fp::PrimeField as BaseField;

use dep::biguint::BigUint56;

mod expand_message_xmd;
mod map_to_curve;
use map_to_curve::map_to_curve;

mod nestedslices_problem;
use nestedslices_problem::{nestedslices_problem_bf_32, nestedslices_problem_bf_16};

global x_num_arr = [
    BaseField { val: BigUint56 { limbs: [0x1c72a8b4000000, 0x3b, 0x00, 0x00, 0x00] } },
    BaseField { val: BigUint56 { limbs: [0x666113c79a8d01, 0xb86bcdd5bd51a2, 0x4a002cc06f7c86, 0x7950b37e74f329, 0x4a9da736] } },
    BaseField { val: BigUint56 { limbs: [0x16e0b2e2326cf1, 0xfccce348c18b1b, 0xd3575a3f74c29b, 0x05be55a02e5e8b, 0x8d11fff9] } },
    BaseField { val: BigUint56 { limbs: [0x1c71c789000000, 0x00, 0x00, 0x00, 0x00] } }
];
global x_den_arr = [
    BaseField { val: BigUint56 { limbs: [0xcc3d1d0d4cf9d2, 0x735eb58af79c20, 0xce04b84bc22235, 0xcb82ee5655a55a, 0xdea0a2be] } },
    BaseField { val: BigUint56 { limbs: [0xcde64df3c5e3bd, 0xe333fd8ecde3f3, 0x6e122c3b1ad77b, 0x33b102a1a152ea, 0xf5a1ffc1] } },
    BaseField { val: BigUint56 { limbs: [0x03d1000000, 0x01, 0x00, 0x00, 0x00] } },
    BaseField { val: BigUint56 { limbs: [0x00, 0x00, 0x00, 0x00, 0x00] } }
];
global y_num_arr = [
    BaseField { val: BigUint56 { limbs: [0x425e1593fffc2f, 0xffffffffffffcf, 0xffffffffffffff, 0xffffffffffffff, 0xffffffff] } },
    BaseField { val: BigUint56 { limbs: [0x220e9edbe15e2a, 0xa435f2ba60d5fe, 0x64ab4ec198c898, 0x1227e77a577b97, 0x1197651d] } },
    BaseField { val: BigUint56 { limbs: [0x8b7058f1193490, 0xfe6671a460c58d, 0xe9abad1fba614d, 0x82df2ad0172f45, 0xc688fffc] } },
    BaseField { val: BigUint56 { limbs: [0x097b4283000000, 0x00, 0x00, 0x00, 0x00] } }
];
global y_den_arr = [
    BaseField { val: BigUint56 { limbs: [0xfff4b9cbfffc2f, 0xfffffffffffd0b, 0xffffffffffffff, 0xffffffffffffff, 0xffffffff] } },
    BaseField { val: BigUint56 { limbs: [0x64b75927e6f518, 0x5a1c20a0e6d462, 0x6a0e28e34666a0, 0x6288cb0300f010, 0x9be1e83c] } },
    BaseField { val: BigUint56 { limbs: [0xb4d9756da8d784, 0xd4cdfc5634d5ed, 0xa51b4258a84339, 0xcd8983f271fc5f, 0xf072ffa1] } },
    BaseField { val: BigUint56 { limbs: [0x03d1000000, 0x01, 0x00, 0x00, 0x00] } }
];

// remainder in LE: [209, 3, 0, 0, 1]
global remainder_32bytes = BaseField{ val: BigUint56 { limbs: [0x0e90a1000000, 0x01000007a2, 0x00, 0x00, 0x00] } };

/* I don't see a case for constant-time in a Noir programm yet, so the implementation
is simplified/optimized. See <https://www.rfc-editor.org/rfc/rfc9380.html#section-4-4.6.1>
 */
fn inv0(x: BaseField) -> BaseField {
    if x.is_zero() {BaseField::zero()}
    else {
        let res = inv_unsafe(x);
        assert(res.mul(x).eq(BaseField::one()));
        res
    }
}
unconstrained fn inv_unsafe(x: BaseField) -> BaseField {x.invert()}
#[test] fn test_inv0_zero() {assert(inv0(BaseField::zero()).eq(BaseField::zero()));}

/* TODO Analyze possible optimization (note *upstream impact*) with replacing `u8` for bigger `Field` elements 
to represent and operate with bytes */
// `count` is $2$ for `secp256k1` _RO_, and it's hardcoded into the function
pub fn hash_to_field(msg: [u8], dst: [u8]) -> [BaseField; 2] {
    // `len_in_bytes` is constant set to 96
    // as `count` is $2$, `for` loop is replaced to boilerplate for optimization
    // `L` is hardcoded to $48$

    let uniform_bytes = expand_message_xmd::expand_message_xmd_dst_conventional_len(
        msg, dst
    );

    // `i` is $0$
    //      `elm_offset` is $0$
    
    // let mut tv = [0; 48];
    let mut tv_lo = [0; 32];
    let mut tv_hi = [0; 16];
    
    // for i in 0..48 {
    //     // `PrimeField` has only LE `from`
    //     tv[47 - i] = uniform_bytes[i];
    // }
    for i in 16..48 {
        tv_lo[47 - i] = uniform_bytes[i];
    }
    for i in 0..16 {
        tv_hi[15 - i] = uniform_bytes[i];
    }

    // (tv_hi mod MODULUS) * modulusOf2^32 + (tv_lo mod MODULUS)
    let u_0 = nestedslices_problem_bf_16(tv_hi).mul(remainder_32bytes).add(
        nestedslices_problem_bf_32(tv_lo)
    );
    
    // `i` is $1$
    //      `elm_offset` is $48$
    
    let mut tv_lo = [0; 32];
    let mut tv_hi = [0; 16];
    for i in 16..48 {
        tv_lo[47 - i] = uniform_bytes[i + 48];
    }
    for i in 0..16 {
        tv_hi[15 - i] = uniform_bytes[i + 48];
    }
    // #nestedslices 
    let u_1 = nestedslices_problem_bf_16(tv_hi).mul(remainder_32bytes).add(
        nestedslices_problem_bf_32(tv_lo)
    );
    
    [u_0, u_1]
}

/* TODO check if there's optimizations to this reference implementation (from 
`redox_ecc`), start with <https://www.rfc-editor.org/rfc/rfc9380.html#appendix-E-2>
 */
fn iso_map(x: BaseField, y: BaseField) -> Point {
    let mut x_num = BaseField::zero();
    let mut x_den = BaseField::zero();
    let mut y_num = BaseField::zero();
    let mut y_den = BaseField::zero();

    for j in 0..4 {
        let i = 3 - j;    

        x_num = (x_num.mul(x)).add(x_num_arr[i]);
        x_den = (x_den.mul(x)).add(x_den_arr[i]);
        y_num = (y_num.mul(x)).add(y_num_arr[i]);
        y_den = (y_den.mul(x)).add(y_den_arr[i]);
    }
    
    // https://www.rfc-editor.org/rfc/rfc9380.html#section-6.6.3-12
    let x_den = inv0(x_den);
    let y_den = inv0(y_den);
    if x_den.is_zero() | y_den.is_zero() {Point::zero()}
    else {
        /* TODO Remove after stabilization. */
        assert(secp256k1().curve.contains(Point::from_affine(
            x_num.mul(x_den),
            y.mul(y_num.mul(y_den))
        )));

        Point::from_affine(
            x_num.mul(x_den),
            y.mul(y_num.mul(y_den))
        )
    }
}

/* TODO ["a small optimization by first mapping u0 and u1 to E', adding the resulting 
points on E'"](https://www.rfc-editor.org/rfc/rfc9380.html#section-6.6.3-7) \
it's a good first issue: needs to add definition of _ISO3_ #isocurvedefine
 */
pub fn hash_to_curve(msg: [u8], dst: [u8]) -> Point {
    let u = hash_to_field(msg, dst);
    let Q0 = map_to_curve(u[0]);
    let Q1 = map_to_curve(u[1]);
    
    let Q0 = iso_map(Q0.0, Q0.1);
    let Q1 = iso_map(Q1.0, Q1.1);

    secp256k1().curve.add(Q0, Q1)
    // `secp256k1` cofactor is $1$
}

// pasted from `curves` crate
struct Secp256k1 {
    curve: Curve,
}
fn secp256k1() -> Secp256k1 {
    Secp256k1 {
        curve: Curve::new(
            BaseField::zero(),
            BaseField::from_u56(7),
            Point::from_affine( 
                BaseField::from_bytes(
                    [
                        0x98, 0x17, 0xf8, 0x16, 0x5b, 0x81, 0xf2, 0x59, 
                        0xd9, 0x28, 0xce, 0x2d, 0xdb, 0xfc, 0x9b, 0x02, 
                        0x07, 0x0b, 0x87, 0xce, 0x95, 0x62, 0xa0, 0x55, 
                        0xac, 0xbb, 0xdc, 0xf9, 0x7e, 0x66, 0xbe, 0x79
                    ]
                ),
                BaseField::from_bytes(
                    [
                        0xb8, 0xd4, 0x10, 0xfb, 0x8f, 0xd0, 0x47, 0x9c,
                        0x19, 0x54, 0x85, 0xa6, 0x48, 0xb4, 0x17, 0xfd,
                        0xa8, 0x08, 0x11, 0x0e, 0xfc, 0xfb, 0xa4, 0x5d,
                        0x65, 0xc4, 0xa3, 0x26, 0x77, 0xda, 0x3a, 0x48
                    ]
                ),
            ),
        ),
    }
}

/* Unfortunately tests currently use insanely long arrays to feed the inputs.
Seems like slices aren't there yet. Watch documentation for the _experimental_ notice disappearance.
That will allow much more convenient data input like
`"QUUX-V01-CS02-with-secp256k1_XMD:SHA-256_SSWU_RO_".as_bytes().as_slice()`. */
// Upstream provides/allows only `assert` currently. I guess adding `assert_eq` one day would be idiomatic.

#[test]
fn J81_field_msg_empty() {
    let u = [
        BaseField::from_bytes([179, 47, 0, 171, 60, 87, 30, 234, 171, 1, 167, 115, 199, 127, 95, 76, 95, 59, 215, 4, 159, 238, 242, 120, 28, 167, 43, 221, 16, 153, 15, 107]),
        BaseField::from_bytes([22, 158, 240, 216, 159, 121, 213, 176, 104, 219, 130, 151, 91, 238, 244, 142, 204, 162, 41, 249, 2, 98, 127, 147, 165, 225, 143, 224, 18, 194, 230, 26])
    ];
    
    let result = hash_to_field(
        [], 
        [
            81,
            85,
            85,
            88,
            45,
            86,
            48,
            49,
            45,
            67,
            83,
            48,
            50,
            45,
            119,
            105,
            116,
            104,
            45,
            115,
            101,
            99,
            112,
            50,
            53,
            54,
            107,
            49,
            95,
            88,
            77,
            68,
            58,
            83,
            72,
            65,
            45,
            50,
            53,
            54,
            95,
            83,
            83,
            87,
            85,
            95,
            82,
            79,
            95,
        ]
    );
    
    assert(result[0].eq(u[0]));
    assert(result[1].eq(u[1]));
}

#[test]
fn field_all_empty() {
    hash_to_field([], []); // testing for smoke in the edge case
}

#[test]
fn J81_curve_msg_empty_performance_intermediate_values() {
    hash_to_field(
        [], 
        /* Seems like slices aren't there yet. Watch documentation for the _experimental_ notice disappearance.
        "QUUX-V01-CS02-with-secp256k1_XMD:SHA-256_SSWU_RO_".as_bytes().as_slice() */
        [
            81,
            85,
            85,
            88,
            45,
            86,
            48,
            49,
            45,
            67,
            83,
            48,
            50,
            45,
            119,
            105,
            116,
            104,
            45,
            115,
            101,
            99,
            112,
            50,
            53,
            54,
            107,
            49,
            95,
            88,
            77,
            68,
            58,
            83,
            72,
            65,
            45,
            50,
            53,
            54,
            95,
            83,
            83,
            87,
            85,
            95,
            82,
            79,
            95,
        ]
    );
    // u[0]
    map_to_curve(
        BaseField { val: BigUint56 { limbs: [0xa5f61ad58d6bd0, 0x7bb85593daba7d, 0x1679ec1da9dc4a, 0x489bf7e840c5c9, 0x788c8bb2] } }
    );
    // u[1]
    map_to_curve(
        BaseField { val: BigUint56 { limbs: [0x24320ed25a6c7b, 0x3cd42ad28c8c01, 0x3d092c4486f5eb, 0xeae24eb02576db, 0xb0989b8a] } }
    );
    
    iso_map(
        // Q0.0
        BaseField { val: BigUint56 { limbs: [0x1055503cba2ffc, 0x2265923d3cd114, 0xb53658c38b5aa6, 0xcacdfefbbad204, 0x3e68f9af] } },
        // Q0.1
        BaseField { val: BigUint56 { limbs: [0xe321c9a66dbf51, 0xd15780d656a38e, 0xfe2659931e0790, 0x639292bb3a8a38, 0x6b1d5b16] } }
    );
    iso_map(
        // Q1.0
        BaseField { val: BigUint56 { limbs: [0x6297010d4bb2bb, 0xb9adb42e8953cd, 0x52f995c57f384d, 0x5aae21aa31f25f, 0x49dcc6e7] } },
        // Q1.1
        BaseField { val: BigUint56 { limbs: [0x8626e53e690900, 0x4febbc040c54f6, 0x162153c4f875ec, 0x8f17e3c2d670, 0x8481a53a] } }
    );
    
    secp256k1().curve.add(
        Point { x: BaseField { val: BigUint56 { limbs: [0x2da0f836fed746, 0x74d7ecb619d875, 0xa34e87eda89375, 0x85a8938002ebe6, 0xb0dd1768] } }, y: BaseField { val: BigUint56 { limbs: [0x1cd49d3c2d558b, 0x5f44b04065cdee, 0x98d305a181db14, 0x4bf72255b07105, 0x07e8610a] } }, z: BaseField { val: BigUint56 { limbs: [0x03d1000000, 0x01, 0x00, 0x00, 0x00] } } },
        Point { x: BaseField { val: BigUint56 { limbs: [0x7959d94005f780, 0xa6b7fcc1cfcb71, 0xe8482a06d05089, 0x2ab94ac0a4a258, 0x96c58b00] } }, y: BaseField { val: BigUint56 { limbs: [0xb2e794c6263237, 0xf1c2cce7b49a99, 0x97a3b8c9b6363a, 0xf7ec967fc71a3a, 0x63e55e78] } }, z: BaseField { val: BigUint56 { limbs: [0x03d1000000, 0x01, 0x00, 0x00, 0x00] } } }
    );
    // result
    // Point { x: BaseField { val: BigUint56 { limbs: [0x8aa9644949e388, 0xada1ba2976702d, 0x06b6de8ce0366f, 0xd12606cac166e3, 0x76fb4a0b] } }, y: PrimeField { val: BigUint56 { limbs: [0x4c362752875cd2, 0xe83f3417fd8c75, 0xb470b2a95b6c70, 0xddb3ffa63039a5, 0xd07ff2f0] } }, z: PrimeField { val: BigUint56 { limbs: [0x4bb8e009071c69, 0x31e0100bb5f2fc, 0x44f9a21927bd14, 0xa510b740a1b672, 0xe5e87397] } } }
}

#[test]
fn J81_curve_msg_empty() {
    let P = Point::from_affine(
        BaseField::from_bytes([70, 19, 235, 223, 45, 133, 181, 183, 169, 171, 30, 132, 139, 196, 121, 20, 134, 115, 109, 190, 241, 174, 235, 23, 230, 174, 145, 226, 144, 226, 202, 193]),
        BaseField::from_bytes([103, 16, 229, 96, 169, 6, 196, 100, 27, 169, 195, 150, 201, 133, 89, 225, 109, 175, 148, 42, 2, 139, 240, 38, 97, 17, 174, 7, 142, 103, 250, 100])
    );
    
    let result = hash_to_curve(
        [], 
        /* Seems like slices aren't there yet. Watch documentation for the _experimental_ notice disappearance.
        "QUUX-V01-CS02-with-secp256k1_XMD:SHA-256_SSWU_RO_".as_bytes().as_slice() */
        [
            81,
            85,
            85,
            88,
            45,
            86,
            48,
            49,
            45,
            67,
            83,
            48,
            50,
            45,
            119,
            105,
            116,
            104,
            45,
            115,
            101,
            99,
            112,
            50,
            53,
            54,
            107,
            49,
            95,
            88,
            77,
            68,
            58,
            83,
            72,
            65,
            45,
            50,
            53,
            54,
            95,
            83,
            83,
            87,
            85,
            95,
            82,
            79,
            95,
        ]
    );
    println(result);
    
    assert(result.eq(P));
    // assert(result.eq(
    //     Point { x: BaseField { val: BigUint56 { limbs: [0x8aa9644949e388, 0xada1ba2976702d, 0x06b6de8ce0366f, 0xd12606cac166e3, 0x76fb4a0b] } }, y: BaseField { val: BigUint56 { limbs: [0x4c362752875cd2, 0xe83f3417fd8c75, 0xb470b2a95b6c70, 0xddb3ffa63039a5, 0xd07ff2f0] } }, z: BaseField { val: BigUint56 { limbs: [0x4bb8e009071c69, 0x31e0100bb5f2fc, 0x44f9a21927bd14, 0xa510b740a1b672, 0xe5e87397] } } }
    // ));
    /* 
        // u[0]
        [9380_J81] Testing J81_curve_msg_empty... PrimeField { val: BigUint56 { limbs: [0xa5f61ad58d6bd0, 0x7bb85593daba7d, 0x1679ec1da9dc4a, 0x489bf7e840c5c9, 0x788c8bb2] } }
        // u[1]
        PrimeField { val: BigUint56 { limbs: [0x24320ed25a6c7b, 0x3cd42ad28c8c01, 0x3d092c4486f5eb, 0xeae24eb02576db, 0xb0989b8a] } }
        // Q0.0
        PrimeField { val: BigUint56 { limbs: [0x1055503cba2ffc, 0x2265923d3cd114, 0xb53658c38b5aa6, 0xcacdfefbbad204, 0x3e68f9af] } }
        // Q0.1
        PrimeField { val: BigUint56 { limbs: [0xe321c9a66dbf51, 0xd15780d656a38e, 0xfe2659931e0790, 0x639292bb3a8a38, 0x6b1d5b16] } }
        // Q1.0
        PrimeField { val: BigUint56 { limbs: [0x6297010d4bb2bb, 0xb9adb42e8953cd, 0x52f995c57f384d, 0x5aae21aa31f25f, 0x49dcc6e7] } }
        // Q1.1
        PrimeField { val: BigUint56 { limbs: [0x8626e53e690900, 0x4febbc040c54f6, 0x162153c4f875ec, 0x8f17e3c2d670, 0x8481a53a] } }
        // iso_map(Q0)
        Point { x: PrimeField { val: BigUint56 { limbs: [0x2da0f836fed746, 0x74d7ecb619d875, 0xa34e87eda89375, 0x85a8938002ebe6, 0xb0dd1768] } }, y: PrimeField { val: BigUint56 { limbs: [0x1cd49d3c2d558b, 0x5f44b04065cdee, 0x98d305a181db14, 0x4bf72255b07105, 0x07e8610a] } }, z: PrimeField { val: BigUint56 { limbs: [0x03d1000000, 0x01, 0x00, 0x00, 0x00] } } }
        // iso_map(Q1)
        Point { x: PrimeField { val: BigUint56 { limbs: [0x7959d94005f780, 0xa6b7fcc1cfcb71, 0xe8482a06d05089, 0x2ab94ac0a4a258, 0x96c58b00] } }, y: PrimeField { val: BigUint56 { limbs: [0xb2e794c6263237, 0xf1c2cce7b49a99, 0x97a3b8c9b6363a, 0xf7ec967fc71a3a, 0x63e55e78] } }, z: PrimeField { val: BigUint56 { limbs: [0x03d1000000, 0x01, 0x00, 0x00, 0x00] } } }
        // result
        Point { x: PrimeField { val: BigUint56 { limbs: [0x8aa9644949e388, 0xada1ba2976702d, 0x06b6de8ce0366f, 0xd12606cac166e3, 0x76fb4a0b] } }, y: PrimeField { val: BigUint56 { limbs: [0x4c362752875cd2, 0xe83f3417fd8c75, 0xb470b2a95b6c70, 0xddb3ffa63039a5, 0xd07ff2f0] } }, z: PrimeField { val: BigUint56 { limbs: [0x4bb8e009071c69, 0x31e0100bb5f2fc, 0x44f9a21927bd14, 0xa510b740a1b672, 0xe5e87397] } } }
        ok
        [9380_J81] All tests passed
    */
}

#[test]
fn J81_curve_msg_abc() {
    let P = Point::from_affine(
        BaseField::from_bytes([75, 44, 203, 179, 31, 241, 159, 189, 96, 87, 32, 249, 249, 236, 182, 114, 238, 108, 12, 18, 147, 34, 81, 107, 41, 219, 66, 171, 30, 224, 119, 51]),
        BaseField::from_bytes([246, 113, 131, 156, 123, 108, 124, 72, 141, 104, 148, 111, 17, 182, 15, 144, 224, 190, 177, 1, 42, 56, 77, 4, 209, 235, 239, 51, 15, 137, 149, 127])
    );
    
    let result = hash_to_curve(
        [
            97,
            98,
            99,
        ], 
        [
            81,
            85,
            85,
            88,
            45,
            86,
            48,
            49,
            45,
            67,
            83,
            48,
            50,
            45,
            119,
            105,
            116,
            104,
            45,
            115,
            101,
            99,
            112,
            50,
            53,
            54,
            107,
            49,
            95,
            88,
            77,
            68,
            58,
            83,
            72,
            65,
            45,
            50,
            53,
            54,
            95,
            83,
            83,
            87,
            85,
            95,
            82,
            79,
            95,
        ]
    );
    
    assert(result.eq(P));
}

#[test]
fn J81_curve_msg_abcdef0123456789() {
    let P = Point::from_affine(
        BaseField::from_bytes([58, 14, 75, 103, 208, 36, 179, 72, 88, 243, 211, 132, 203, 165, 131, 7, 169, 10, 38, 55, 1, 167, 228, 8, 254, 241, 147, 242, 131, 64, 197, 186]),
        BaseField::from_bytes([40, 216, 88, 151, 161, 188, 39, 238, 189, 152, 179, 86, 231, 220, 106, 23, 64, 156, 56, 244, 252, 96, 139, 80, 196, 195, 212, 133, 96, 71, 54, 68])
    );
    
    let result = hash_to_curve(
        [
            97,
            98,
            99,
            100,
            101,
            102,
            48,
            49,
            50,
            51,
            52,
            53,
            54,
            55,
            56,
            57,
        ], 
        [
            81,
            85,
            85,
            88,
            45,
            86,
            48,
            49,
            45,
            67,
            83,
            48,
            50,
            45,
            119,
            105,
            116,
            104,
            45,
            115,
            101,
            99,
            112,
            50,
            53,
            54,
            107,
            49,
            95,
            88,
            77,
            68,
            58,
            83,
            72,
            65,
            45,
            50,
            53,
            54,
            95,
            83,
            83,
            87,
            85,
            95,
            82,
            79,
            95,
        ]
    );
    
    assert(result.eq(P));
}

#[test]
fn J81_curve_msg_q128() {
    let P = Point::from_affine(
        BaseField::from_bytes([233, 144, 24, 228, 2, 177, 114, 127, 42, 245, 171, 155, 131, 83, 184, 239, 29, 136, 30, 31, 2, 47, 86, 170, 55, 58, 51, 133, 199, 123, 22, 226]),
        BaseField::from_bytes([115, 216, 133, 102, 30, 106, 73, 184, 159, 150, 62, 165, 198, 251, 25, 55, 118, 100, 213, 124, 54, 79, 237, 255, 103, 88, 195, 92, 217, 29, 64, 242])
    );

    // let e_prime_point_0 = map_to_curve(BaseField::from_bytes(
    //     [245, 205, 91, 176, 65, 115, 184, 222, 48, 26, 80, 93, 116, 16, 206, 59, 170, 133, 78, 204, 232, 135, 122, 32, 168, 192, 250, 36, 80, 154, 168, 237]
    // ));
    // let e_target_point_0 = iso_map(e_prime_point_0.0, e_prime_point_0.1);
    // let e_prime_point_1 = map_to_curve(BaseField::from_bytes(
    //     [29, 197, 10, 101, 191, 69, 146, 254, 157, 172, 126, 64, 44, 1, 171, 159, 99, 226, 219, 254, 55, 56, 111, 193, 194, 143, 129, 22, 209, 140, 231, 223]
    //  // [29, 197, 10, 101, 191, 69, 146, 254, 157, 172, 126, 64, 44, 1, 171, 159, 99, 226, 219, 254, 55, 56, 111, 193, 194, 143, 129, 22, 209, 140, 231, 223]
    // ));
    // println(e_prime_point_1.0.to_bytes());
    // println(e_prime_point_1.1.to_bytes());
    // let e_target_point_1 = iso_map(e_prime_point_1.0, e_prime_point_1.1);

    // let Q0 = Point::from_affine(
    //     BaseField::from_bytes([122, 36, 88, 235, 146, 209, 32, 215, 28, 111, 171, 212, 106, 175, 46, 233, 180, 249, 245, 223, 136, 85, 100, 156, 12, 82, 233, 207, 60, 81, 145, 156]),
    //     BaseField::from_bytes([184, 31, 138, 191, 63, 6, 74, 61, 22, 110, 103, 55, 144, 111, 163, 127, 158, 244, 104, 141, 111, 56, 30, 34, 47, 65, 52, 1, 205, 29, 55, 199]),
    // );
    // let Q1 = Point::from_affine(
    //     BaseField::from_bytes([155, 134, 141, 132, 54, 174, 198, 241, 21, 0, 26, 20, 71, 31, 118, 244, 43, 197, 47, 151, 59, 80, 18, 89, 189, 230, 123, 77, 40, 227, 254, 16]),
    //     BaseField::from_bytes([114, 182, 225, 176, 110, 154, 198, 15, 144, 50, 135, 80, 207, 83, 160, 15, 135, 60, 255, 62, 190, 50, 67, 54, 135, 24, 242, 75, 155, 61, 22, 11]),
    // );
    // assert(e_target_point_0.eq(Q0));
    // // assert(e_target_point_1.eq(Q1));

    // let result = secp256k1().curve.add(Q0, Q1);
    // assert(result.eq(P));
    /* 
    (Plus, [122, 36, 88, 235, 146, 209, 32, 215, 28, 111, 171, 212, 106, 175, 46, 233, 180, 249, 245, 223, 136, 85, 100, 156, 12, 82, 233, 207, 60, 81, 145, 156])
    (Plus, [184, 31, 138, 191, 63, 6, 74, 61, 22, 110, 103, 55, 144, 111, 163, 127, 158, 244, 104, 141, 111, 56, 30, 34, 47, 65, 52, 1, 205, 29, 55, 199])
    (Plus, [155, 134, 141, 132, 54, 174, 198, 241, 21, 0, 26, 20, 71, 31, 118, 244, 43, 197, 47, 151, 59, 80, 18, 89, 189, 230, 123, 77, 40, 227, 254, 16])
    (Plus, [114, 182, 225, 176, 110, 154, 198, 15, 144, 50, 135, 80, 207, 83, 160, 15, 135, 60, 255, 62, 190, 50, 67, 54, 135, 24, 242, 75, 155, 61, 22, 11])
     */
    
    let result = hash_to_curve(
        [
            113,
            49,
            50,
            56,
            95,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
            113,
        ], 
        /* Seems like slices aren't there yet. Watch documentation for 
        the _experimental_ notice disappearance.
        "QUUX-V01-CS02-with-secp256k1_XMD:SHA-256_SSWU_RO_".as_bytes().as_slice() */
        [
            81,
            85,
            85,
            88,
            45,
            86,
            48,
            49,
            45,
            67,
            83,
            48,
            50,
            45,
            119,
            105,
            116,
            104,
            45,
            115,
            101,
            99,
            112,
            50,
            53,
            54,
            107,
            49,
            95,
            88,
            77,
            68,
            58,
            83,
            72,
            65,
            45,
            50,
            53,
            54,
            95,
            83,
            83,
            87,
            85,
            95,
            82,
            79,
            95,
        ]
    );
    
    assert(result.eq(P));
}

#[test]
fn J81_curve_msg_a512() {
    let P = Point::from_affine(
        BaseField::from_bytes([152, 201, 183, 140, 31, 140, 253, 230, 228, 82, 129, 35, 56, 173, 213, 190, 213, 229, 126, 10, 10, 138, 232, 71, 182, 185, 240, 170, 90, 211, 200, 227]),
        BaseField::from_bytes([166, 58, 130, 229, 142, 136, 181, 36, 48, 128, 227, 199, 37, 71, 12, 47, 204, 33, 34, 38, 78, 210, 169, 86, 47, 241, 27, 24, 182, 238, 70, 132])
    );
    
    let result = hash_to_curve(
        [
            97,
            53,
            49,
            50,
            95,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
            97,
        ], 
        [
            81,
            85,
            85,
            88,
            45,
            86,
            48,
            49,
            45,
            67,
            83,
            48,
            50,
            45,
            119,
            105,
            116,
            104,
            45,
            115,
            101,
            99,
            112,
            50,
            53,
            54,
            107,
            49,
            95,
            88,
            77,
            68,
            58,
            83,
            72,
            65,
            45,
            50,
            53,
            54,
            95,
            83,
            83,
            87,
            85,
            95,
            82,
            79,
            95,
        ]
    );
    
    assert(result.eq(P));
}

// #[test]
// fn dependency_bytes_ordering() {
//     let sec256k1 = secp256k1();
//     println(sec256k1.curve.gen.x);
//     let dep_curves_bytes = [
//         // reversed
//         152,  23, 248,  22,  91, 129, 242,  89,
//         217,  40, 206,  45, 219, 252, 155,   2,
//         7,  11, 135, 206, 149,  98, 160,  85,
//         172, 187, 220, 249, 126, 102, 190, 121
//     ];
//     assert(
//         sec256k1.curve.gen.x.eq(
//             BaseField::from_bytes(dep_curves_bytes)
//         )
//     );
// }

// #[test]
// fn get_constants() {
//     // global remainder_35bytes = 
//     // println(BaseField::from_bytes([0, 0, 0, 209, 3, 0, 0, 1]));
//     // global remainder_32bytes = 
//     // println(BaseField::from_bytes([209, 3, 0, 0, 1]));
//    
//     // isog
//
//     /* x_num: vec![
//             f.from("0x8e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38daaaaa8c7"),
//             f.from("0x07d3d4c80bc321d5b9f315cea7fd44c5d595d2fc0bf63b92dfff1044f17c6581"),
//             f.from("0x534c328d23f234e6e2a413deca25caece4506144037c40314ecbd0b53d9dd262"),
//             f.from("0x8e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38daaaaa88c"),
//         ],
//     # constants printing
//     (Plus, [199, 168, 170, 170, 141, 227, 56, 142, 227, 56, 142, 227, 56, 142, 227, 56, 142, 227, 56, 142, 227, 56, 142, 227, 56, 142, 227, 56, 142, 227, 56, 142])
//     (Plus, [129, 101, 124, 241, 68, 16, 255, 223, 146, 59, 246, 11, 252, 210, 149, 213, 197, 68, 253, 167, 206, 21, 243, 185, 213, 33, 195, 11, 200, 212, 211, 7])
//     (Plus, [98, 210, 157, 61, 181, 208, 203, 78, 49, 64, 124, 3, 68, 97, 80, 228, 236, 202, 37, 202, 222, 19, 164, 226, 230, 52, 242, 35, 141, 50, 76, 83])
//     (Plus, [140, 168, 170, 170, 141, 227, 56, 142, 227, 56, 142, 227, 56, 142, 227, 56, 142, 227, 56, 142, 227, 56, 142, 227, 56, 142, 227, 56, 142, 227, 56, 142])
//     ____________________ */
//     // println(BaseField::from_bytes([199, 168, 170, 170, 141, 227, 56, 142, 227, 56, 142, 227, 56, 142, 227, 56, 142, 227, 56, 142, 227, 56, 142, 227, 56, 142, 227, 56, 142, 227, 56, 142]));
//     // println(BaseField::from_bytes([129, 101, 124, 241, 68, 16, 255, 223, 146, 59, 246, 11, 252, 210, 149, 213, 197, 68, 253, 167, 206, 21, 243, 185, 213, 33, 195, 11, 200, 212, 211, 7]));
//     // println(BaseField::from_bytes([98, 210, 157, 61, 181, 208, 203, 78, 49, 64, 124, 3, 68, 97, 80, 228, 236, 202, 37, 202, 222, 19, 164, 226, 230, 52, 242, 35, 141, 50, 76, 83]));
//     // println(BaseField::from_bytes([140, 168, 170, 170, 141, 227, 56, 142, 227, 56, 142, 227, 56, 142, 227, 56, 142, 227, 56, 142, 227, 56, 142, 227, 56, 142, 227, 56, 142, 227, 56, 142]));
//
//     /* x_den: vec![
//             f.from("0xd35771193d94918a9ca34ccbb7b640dd86cd409542f8487d9fe6b745781eb49b"),
//             f.from("0xedadc6f64383dc1df7c4b2d51b54225406d36b641f5e41bbc52a56612a8c6d14"),
//             f.one(),
//             f.zero(),
//         ]
//     # constants printing
//     (Plus, [155, 180, 30, 120, 69, 183, 230, 159, 125, 72, 248, 66, 149, 64, 205, 134, 221, 64, 182, 183, 203, 76, 163, 156, 138, 145, 148, 61, 25, 113, 87, 211])
//     (Plus, [20, 109, 140, 42, 97, 86, 42, 197, 187, 65, 94, 31, 100, 107, 211, 6, 84, 34, 84, 27, 213, 178, 196, 247, 29, 220, 131, 67, 246, 198, 173, 237])
//     (Plus, [1])
//     (NoSign, [0])
//     ____________________ */
//     // println(BaseField::from_bytes([155, 180, 30, 120, 69, 183, 230, 159, 125, 72, 248, 66, 149, 64, 205, 134, 221, 64, 182, 183, 203, 76, 163, 156, 138, 145, 148, 61, 25, 113, 87, 211]));
//     // println(BaseField::from_bytes([20, 109, 140, 42, 97, 86, 42, 197, 187, 65, 94, 31, 100, 107, 211, 6, 84, 34, 84, 27, 213, 178, 196, 247, 29, 220, 131, 67, 246, 198, 173, 237]));
//     // println(BaseField::one());
//     // println(BaseField::zero());
//
//     /* y_num: vec![
//             f.from("0x4bda12f684bda12f684bda12f684bda12f684bda12f684bda12f684b8e38e23c"),
//             f.from("0xc75e0c32d5cb7c0fa9d0a54b12a0a6d5647ab046d686da6fdffc90fc201d71a3"),
//             f.from("0x29a6194691f91a73715209ef6512e576722830a201be2018a765e85a9ecee931"),
//             f.from("0x2f684bda12f684bda12f684bda12f684bda12f684bda12f684bda12f38e38d84"),
//         ]
//     # constants printing
//     (Plus, [60, 226, 56, 142, 75, 104, 47, 161, 189, 132, 246, 18, 218, 75, 104, 47, 161, 189, 132, 246, 18, 218, 75, 104, 47, 161, 189, 132, 246, 18, 218, 75])
//     (Plus, [163, 113, 29, 32, 252, 144, 252, 223, 111, 218, 134, 214, 70, 176, 122, 100, 213, 166, 160, 18, 75, 165, 208, 169, 15, 124, 203, 213, 50, 12, 94, 199])
//     (Plus, [49, 233, 206, 158, 90, 232, 101, 167, 24, 32, 190, 1, 162, 48, 40, 114, 118, 229, 18, 101, 239, 9, 82, 113, 115, 26, 249, 145, 70, 25, 166, 41])
//     (Plus, [132, 141, 227, 56, 47, 161, 189, 132, 246, 18, 218, 75, 104, 47, 161, 189, 132, 246, 18, 218, 75, 104, 47, 161, 189, 132, 246, 18, 218, 75, 104, 47])
//     ____________________ */
//     // println(BaseField::from_bytes([60, 226, 56, 142, 75, 104, 47, 161, 189, 132, 246, 18, 218, 75, 104, 47, 161, 189, 132, 246, 18, 218, 75, 104, 47, 161, 189, 132, 246, 18, 218, 75]));
//     // println(BaseField::from_bytes([163, 113, 29, 32, 252, 144, 252, 223, 111, 218, 134, 214, 70, 176, 122, 100, 213, 166, 160, 18, 75, 165, 208, 169, 15, 124, 203, 213, 50, 12, 94, 199]));
//     // println(BaseField::from_bytes([49, 233, 206, 158, 90, 232, 101, 167, 24, 32, 190, 1, 162, 48, 40, 114, 118, 229, 18, 101, 239, 9, 82, 113, 115, 26, 249, 145, 70, 25, 166, 41]));
//     // println(BaseField::from_bytes([132, 141, 227, 56, 47, 161, 189, 132, 246, 18, 218, 75, 104, 47, 161, 189, 132, 246, 18, 218, 75, 104, 47, 161, 189, 132, 246, 18, 218, 75, 104, 47]));
//
//     /* y_den: vec![
//             f.from("0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffff93b"),
//             f.from("0x7a06534bb8bdb49fd5e9e6632722c2989467c1bfc8e8d978dfb425d2685c2573"),
//             f.from("0x6484aa716545ca2cf3a70c3fa8fe337e0a3d21162f0d6299a7bf8192bfd2a76f"),
//             f.one(),
//         ]
//     # constants printing
//     (Plus, [59, 249, 255, 255, 254, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255])
//     (Plus, [115, 37, 92, 104, 210, 37, 180, 223, 120, 217, 232, 200, 191, 193, 103, 148, 152, 194, 34, 39, 99, 230, 233, 213, 159, 180, 189, 184, 75, 83, 6, 122])
//     (Plus, [111, 167, 210, 191, 146, 129, 191, 167, 153, 98, 13, 47, 22, 33, 61, 10, 126, 51, 254, 168, 63, 12, 167, 243, 44, 202, 69, 101, 113, 170, 132, 100])
//     (Plus, [1])
//     ____________________ */
//     // println(BaseField::from_bytes([59, 249, 255, 255, 254, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255]));
//     // println(BaseField::from_bytes([115, 37, 92, 104, 210, 37, 180, 223, 120, 217, 232, 200, 191, 193, 103, 148, 152, 194, 34, 39, 99, 230, 233, 213, 159, 180, 189, 184, 75, 83, 6, 122]));
//     // println(BaseField::from_bytes([111, 167, 210, 191, 146, 129, 191, 167, 153, 98, 13, 47, 22, 33, 61, 10, 126, 51, 254, 168, 63, 12, 167, 243, 44, 202, 69, 101, 113, 170, 132, 100]));
//     // println(BaseField::one());
// }

// #[test]
// fn hash_to_field_debugging() {
//     let u = [
//         BaseField::from_bytes([179, 47, 0, 171, 60, 87, 30, 234, 171, 1, 167, 115, 199, 127, 95, 76, 95, 59, 215, 4, 159, 238, 242, 120, 28, 167, 43, 221, 16, 153, 15, 107]),
//         BaseField::from_bytes([22, 158, 240, 216, 159, 121, 213, 176, 104, 219, 130, 151, 91, 238, 244, 142, 204, 162, 41, 249, 2, 98, 127, 147, 165, 225, 143, 224, 18, 194, 230, 26])
//     ];
//    
//     let result = hash_to_field(
//         [], 
//         /* Seems like slices aren't there yet. Watch documentation for the _experimental_ notice disappearance.
//         "QUUX-V01-CS02-with-secp256k1_XMD:SHA-256_SSWU_RO_".as_bytes().as_slice() */
//         [
//             81,
//             85,
//             85,
//             88,
//             45,
//             86,
//             48,
//             49,
//             45,
//             67,
//             83,
//             48,
//             50,
//             45,
//             119,
//             105,
//             116,
//             104,
//             45,
//             115,
//             101,
//             99,
//             112,
//             50,
//             53,
//             54,
//             107,
//             49,
//             95,
//             88,
//             77,
//             68,
//             58,
//             83,
//             72,
//             65,
//             45,
//             50,
//             53,
//             54,
//             95,
//             83,
//             83,
//             87,
//             85,
//             95,
//             82,
//             79,
//             95,
//         ]
//     );
// }
// #[test]
// fn isomap_debugging() {
//     // println(iso_map(
//     //     BaseField { val: BigUint56 { limbs: [0x1055503cba2ffc, 0x2265923d3cd114, 0xb53658c38b5aa6, 0xcacdfefbbad204, 0x3e68f9af] } },
//     //     BaseField { val: BigUint56 { limbs: [0xe321c9a66dbf51, 0xd15780d656a38e, 0xfe2659931e0790, 0x639292bb3a8a38, 0x6b1d5b16] } }
//     // ));
//     // Point { x: PrimeField { val: BigUint56 { limbs: [0x2da0f836fed746, 0x74d7ecb619d875, 0xa34e87eda89375, 0x85a8938002ebe6, 0xb0dd1768] } }, y: PrimeField { val: BigUint56 { limbs: [0x1cd49d3c2d558b, 0x5f44b04065cdee, 0x98d305a181db14, 0x4bf72255b07105, 0x07e8610a] } }, z: PrimeField { val: BigUint56 { limbs: [0x03d1000000, 0x01, 0x00, 0x00, 0x00] } } }
//
//     println(iso_map(
//         BaseField { val: BigUint56 { limbs: [0x6297010d4bb2bb, 0xb9adb42e8953cd, 0x52f995c57f384d, 0x5aae21aa31f25f, 0x49dcc6e7] } },
//         BaseField { val: BigUint56 { limbs: [0x8626e53e690900, 0x4febbc040c54f6, 0x162153c4f875ec, 0x8f17e3c2d670, 0x8481a53a] } }
//     ));
//     // Point { x: PrimeField { val: BigUint56 { limbs: [0x7959d94005f780, 0xa6b7fcc1cfcb71, 0xe8482a06d05089, 0x2ab94ac0a4a258, 0x96c58b00] } }, y: PrimeField { val: BigUint56 { limbs: [0xb2e794c6263237, 0xf1c2cce7b49a99, 0x97a3b8c9b6363a, 0xf7ec967fc71a3a, 0x63e55e78] } }, z: PrimeField { val: BigUint56 { limbs: [0x03d1000000, 0x01, 0x00, 0x00, 0x00] } } }
// }
// #[test]
// fn pointadd_debugging() {
//     println(secp256k1().curve.add(
//         Point { x: BaseField { val: BigUint56 { limbs: [0x2da0f836fed746, 0x74d7ecb619d875, 0xa34e87eda89375, 0x85a8938002ebe6, 0xb0dd1768] } }, y: BaseField { val: BigUint56 { limbs: [0x1cd49d3c2d558b, 0x5f44b04065cdee, 0x98d305a181db14, 0x4bf72255b07105, 0x07e8610a] } }, z: BaseField { val: BigUint56 { limbs: [0x03d1000000, 0x01, 0x00, 0x00, 0x00] } } }, 
//         Point { x: BaseField { val: BigUint56 { limbs: [0x7959d94005f780, 0xa6b7fcc1cfcb71, 0xe8482a06d05089, 0x2ab94ac0a4a258, 0x96c58b00] } }, y: BaseField { val: BigUint56 { limbs: [0xb2e794c6263237, 0xf1c2cce7b49a99, 0x97a3b8c9b6363a, 0xf7ec967fc71a3a, 0x63e55e78] } }, z: BaseField { val: BigUint56 { limbs: [0x03d1000000, 0x01, 0x00, 0x00, 0x00] } } }
//     ));
// }