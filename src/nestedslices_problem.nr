/* [Nested slices](https://github.com/noir-lang/noir/issues/3363) are yet too experimental to work here, 
so instead just two (dirty) boilerplates `fn` are added yet, 
which eventually can be ditched for slice input back. #nestedslices */

use dep::curves::ecdsa_secp256k1::fp::PrimeField as BaseField;
use dep::biguint::BigUint56;

global R2/* : BaseField */ = BaseField { val: BigUint56 { limbs: [0xa1000000000000, 0x07a2000e90, 0x01, 0, 0] } };

// > / Constructs a BigUint56 from a byte array in little-endian format.
pub(crate) fn nestedslices_problem_bu_32(bytes: [u8; 32]) -> BigUint56 {
    let mut res = BigUint56::zero();
    for i in 0..32 {
        let limb_index = (i as u56) / (7 as u56);
        let byte_index = (i as u56) % (7 as u56);

        res.limbs[limb_index as Field] |= (bytes[i] as u56) << (byte_index * 8);
    }

    res
}

pub(crate) fn nestedslices_problem_bu_16(bytes: [u8; 16]) -> BigUint56 {
    let mut res = BigUint56::zero();
    for i in 0..16 {
        let limb_index = (i as u56) / (7 as u56);
        let byte_index = (i as u56) % (7 as u56);

        res.limbs[limb_index as Field] |= (bytes[i] as u56) << (byte_index * 8);
    }

    res
}

pub(crate) fn nestedslices_problem_bf_32(bytes: [u8; 32]) -> BaseField {
    let tmp = BaseField { val: nestedslices_problem_bu_32(bytes) };

    let modulus = BaseField::modulus();
    assert(tmp.val.lt(modulus.val));

    tmp.mul(R2)
}

pub(crate) fn nestedslices_problem_bf_16(bytes: [u8; 16]) -> BaseField {
    let tmp = BaseField { val: nestedslices_problem_bu_16(bytes) };

    let modulus = BaseField::modulus();
    assert(tmp.val.lt(modulus.val));

    tmp.mul(R2)
}