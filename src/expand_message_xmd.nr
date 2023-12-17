use dep::std::hash::sha256;
use dep::std::println;

// TODO `expand_message_xmd(msg, DST, len_in_bytes)`
/* It makes sense to me to create separate function(s)/API for longer DST and for now go with "regular" lengthed to cut costs for more popular way; 
anyway ZK-case where DST isn't known upfront is to be found in the wild. */
/* For `secp256` `len_in_bytes` is $96$, so it's hard-coded. */
//      as `len_in_bytes` is $96$ hence `ell` is $3$

// output length is `len_in_bytes` which is $96$
pub fn expand_message_xmd_dst_conventional_len(msg: [u8], dst: [u8]) -> [u8; 96] {
    // `dst` possible length is limited by the RFC
    assert(dst.len() as u16 < 256);
    // TODO check what to do with empty `dst`
    //      it seems not to be a special case
    let dst_prime = dst.push_back(dst.len() as u8);
    
    // "for SHA-256, s_in_bytes = 64" hence `Z_pad = [0; 64]`
    // `l_i_b_str` is hardcoded here to `[0, 96]` too, since `len_in_bytes` is $96$
    // `msg_prime` = [0; 64] || msg || [0, 96] || [0] || dst_prime
    let b_0 = sha256(
        [0; 64].append(msg).append([0, 96]).push_back(0).append(dst_prime)
    );
    let b_1 = sha256(b_0.as_slice().push_back(1).append(dst_prime));

    /* TODO analyze if it's possible/feasible to replace `sha256` output with a biguint number;
    especially for XOR */
    /*      while limbs aren't `Field` outcome could be diminishing =(
    https://noir-lang.org/dev/language_concepts/ops#bitwise-operations-example
     */
    
    // hardcoded `for` loop; do you remember that `ell` is $3$
    
    // `i` is $2$
    let b_2 = sha256(xor(b_0, b_1).as_slice().push_back(2).append(dst_prime));
    // `i` is $3$
    let b_3 = sha256(xor(b_0, b_2).as_slice().push_back(3).append(dst_prime));

    let mut result = [0; 96];
    let b = [b_1, b_2, b_3];
    for i in 0..3 {
        for j in 0..32 {
            result[32*i + j] = b[i][j];
        }
    }
    result
}

/* TODO 
create "good first issue" for this variant
use "4.1.  I2OSP" from <https://www.rfc-editor.org/rfc/inline-errata/rfc8017.html>
 */
//      maybe longer `dst` function can be universal API for both cases
// fn construct_dst_prime_long_len(dst: Vec<u8>) -> Vec<u8> {
//     assert(dst.len() >= 256);
// }
// fn expand_message_xmd_dst_long_len(msg: Vec<u8>, dst: Vec<u8>) -> [u8; /*  */] {}

// TODO find/adapt this feature from a maintained crate
fn xor(x: [u8; 32], y: [u8; 32]) -> [u8; 32] {
    let mut result = [0; 32];
    for i in 0..32 {
        result[i] = x[i] ^ y[i];
    }
    result
}

/* test vectors
* <https://www.rfc-editor.org/rfc/rfc9380.html#name-expand_message_xmdsha-256>
* <https://www.rfc-editor.org/rfc/rfc9380.html#name-expand_message_xmdsha-256-l>
 */

#[test]
fn j81_smoke() {
    let result = expand_message_xmd_dst_conventional_len(
        // "".as_bytes(), 
        [0],
        [1]
    );
    assert(result.len() == 96);
}

#[test]
fn sha256_slice_input() {
    println(sha256(
        [0].push_back(0)
    ));
}

#[test]
fn j81_emptyMsg() {
    let result = expand_message_xmd_dst_conventional_len(
        // "".as_bytes().as_slice(), 
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
    assert(result.len() == 96);
    let uniform_bytes = [
        124,
        37,
        156,
        11,
        217,
        104,
        251,
        54,
        101,
        171,
        75,
        7,
        123,
        224,
        64,
        92,
        107,
        15,
        153,
        16,
        221,
        43,
        167,
        28,
        120,
        242,
        238,
        158,
        136,
        177,
        157,
        121,
        167,
        109,
        251,
        88,
        84,
        84,
        252,
        10,
        107,
        132,
        191,
        80,
        232,
        42,
        144,
        151,
        226,
        53,
        111,
        200,
        116,
        174,
        68,
        77,
        45,
        83,
        43,
        236,
        66,
        10,
        112,
        209,
        26,
        230,
        194,
        18,
        224,
        143,
        225,
        165,
        147,
        127,
        98,
        2,
        22,
        244,
        47,
        164,
        204,
        87,
        14,
        9,
        29,
        29,
        4,
        242,
        116,
        96,
        104,
        38,
        207,
        24,
        16,
        117,
    ];
    assert(uniform_bytes.len() == 96);
    for i in 0..96 {assert_eq(result[i], uniform_bytes[i]);}
    println(result);
    // for i in 0..96 {println(result[i]);}
}

// #[test]
// fn expand_message_xmd_debugging() {
//     let msg = "".as_bytes().as_slice();
//     let dst = [];
    
//     assert(dst.len() as u16 < 256);
//     let dst_prime/* : [u8] */ = dst.push_back(dst.len() as u8);
    
//     // "for SHA-256, s_in_bytes = 64" hence `Z_pad = [0; 64]`
//     // `l_i_b_str` is hardcoded here to `[0, 96]` too, since `len_in_bytes` is $96$
//     // `msg_prime` = [0; 64] || msg || [0, 96] || [0] || dst_prime
//     let b_0 = sha256(
//         [0; 64].append(msg).append([0, 96]).push_back(0).append(dst_prime)
//     );
//     println(b_0);
//     let b_1 = sha256(b_0.as_slice().push_back(1).append(dst_prime));

//     // `i` is $2$
//     println(
//         sha256(xor(b_0, b_1).as_slice().push_back(2).append(dst_prime))
//     );
// }