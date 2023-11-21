use dep::std::println;
use dep::curves::ecdsa_secp256k1::fp::PrimeField as BaseField;
use dep::biguint::BigUint56;
// use dep::curves::ecdsa_secp256k1::fq::PrimeField as ScalarField;
use crate::inv0;

// https://www.rfc-editor.org/rfc/rfc9380.html#name-suites-for-secp256k1
/* static SECP256K1_3ISO_PARAMS: &Params = &Params {
       name: "secp256k1_3iso",
       p: "115792089237316195423570985008687907853269984665640564039457584007908834671663",
       a: "28734576633528757162648956269730739219262246272443394170905244663053633733939",
       b: "1771",
       r: "115792089237316195423570985008687907852837564279074904382605163141518161494337",
       h: "1",
       gx: "75295888890003590383366995344834012177557063699577440394299653383124903397514",
       gy: "82553647407850972504999846303729620951309077682374043495922869307182479212755",
   }; */
/* *these constants are put here in Montgomery form as used in following computations;* 
to check them use `to_biguint56` method */
global Z = BaseField{
    val: BigUint56 { limbs: [0xffffd504fffc2f, 0xfffffffffffff4, 0xffffffffffffff, 0xffffffffffffff, 0xffffffff] }
};
global B = BaseField{ val: BigUint56 { limbs: [0x1a66db000000, 0x06eb, 0x00, 0x00, 0x00] } };
global A = BaseField{
    val: BigUint56 { limbs: [0x01def0d3aa069b, 0x2a19a2db714ce8, 0xfbf04458ce38a3, 0x59a0e58ae2837b, 0xc49336d9] }
};

global c1 = BigUint56 { limbs: [0xffffffbfffff0b, 0xffffffffffffff, 0xffffffffffffff, 0xffffffffffffff, 0x3fffffff] };
global c2 = BaseField{ val: BigUint56 { limbs: [0x1cb382209a1480, 0x6c4ecf93f0b3d9, 0x65e3b00d0b5b90, 0x7d48184745a380, 0x3b815d2e] } };

// Naturally it's just a simple `if`, but having it dramatically improves readability along the RFC.
fn cmov(a: BaseField, b: BaseField, c: bool) -> BaseField {
    if c {b}
    else {a}
}

/* ~~TODO~~ analyze what's better: to return coordinates tuple since `E'` is defined over the same `BaseField`,
or to define a whole other curve to enjoy `contains` method which would `assert` the `Point` is 
actually on the curve */
/*      With currently available `swcurve::Point` returning tuple is *much cleaner interface* which prevents
confusion between isogen curve and `secp256k1` itself. Defining another type for point on isogen curve 
would be ok, but using one for both will be source of mistakes. #isocurvedefine */
pub fn map_to_curve(u: BaseField) -> (BaseField, BaseField) {
    let tv1 = Z.mul(u.square());
    let tv2 = tv1.square().add(tv1);
    let tv3 = tv2.add(BaseField::one()).mul(B);
    let tv4 = A.mul(cmov(Z, tv2.neg(), !tv2.is_zero()));
    // let tv2 = tv3.square();
    let tv6 = tv4.square();
    let tv5 = A.mul(tv6);
    let tv2 = tv3.square().add(tv5).mul(tv3);
    let tv6 = tv6.mul(tv4);
    let tv5 = B.mul(tv6);
    let tv2 = tv2.add(tv5);
    // let x = tv1.mul(tv3);
    let (is_gx1_square, y1) = sqrt_ratio(tv2, tv6);
    // let y = tv1.mul(u).mul(y1);
    let x = cmov(tv1.mul(tv3), tv3, is_gx1_square);
    let y = cmov(tv1.mul(u).mul(y1), y1, is_gx1_square);
    /* https://www.rfc-editor.org/rfc/rfc9380.html#section-4.1-4
    so it seems to boil down to `to_biguint56()[0] % 2` in most optimal of simple solutions */
    /*      maybe `to_biguint56()` is excessive too, but I'm not sure if 
    Montgomery representation preserves parity; TODO _good first issue_ */
    let e1 = u.to_biguint56().limbs[0] % 2 == y.to_biguint56().limbs[0] % 2;
    let y = cmov(y.neg(), y, e1);
    let x = x.mul(inv0(tv4));

    (x, y)
}
// TODO analyse how reference implementation is better and why it's a mix of specs approaches
/*      I guess it's just a general variant which better accounts for curve parameters being 
passed along to it. As we yet want a specialized implementation, probability of taking something
useful from that approach is quite low. Though it deserves mention here and a further look. */

// <F.2.1.2.>
fn sqrt_ratio(u: BaseField, v: BaseField) -> (bool, BaseField)  {
    /* actually `v` can't be zero since it's `tv4` cubed, which in turn `A` multiplied by a value which falls back to `Z`
    when zero, and `A` can't be zero due to isogeny approach \
    nevertheless I tend to keep the `assert`, at least for some time, at least as a comment then */
    assert(!v.is_zero());

    // let tv1 = v.square();
    let tv2 = u.mul(v);
    // let tv1 = v.square().mul(tv2);
    let y1 = v.square().mul(tv2).pow(c1).mul(tv2);
    // let y2 = y1.mul(c2);
    let isQR = y1.square().mul(v).eq(u);
    let y = cmov(y1.mul(c2), y1, isQR);

    (isQR, y)
}

// #[test]
// fn sqrtratio_debugging() {
//     // https://discord.com/channels/1113924620781883405/1113924622031798313/1172921488916103259
//     let v = BaseField::zero();
//     // println(v);
//     assert(!v.is_zero());
//     sqrt_ratio(
//         BaseField::zero(), v
//     );
// }
// #[test]
// fn map_debugging() {
//     // let Q0 = map_to_curve(
//     //     BaseField{ val: BigUint56 { limbs: [0xa5f61ad58d6bd0, 0x7bb85593daba7d, 0x1679ec1da9dc4a, 0x489bf7e840c5c9, 0x788c8bb2] } }
//     // );
//     let Q1 = map_to_curve(
//         BaseField{ val: BigUint56 { limbs: [0x24320ed25a6c7b, 0x3cd42ad28c8c01, 0x3d092c4486f5eb, 0xeae24eb02576db, 0xb0989b8a] } }
//     );
//     // println(Q0.0);
//     // println(Q0.1);
//     println(Q1.0);
//     println(Q1.1);
//     /* 
//     PrimeField { val: BigUint56 { limbs: [0x1055503cba2ffc, 0x2265923d3cd114, 0xb53658c38b5aa6, 0xcacdfefbbad204, 0x3e68f9af] } }
//     PrimeField { val: BigUint56 { limbs: [0xe321c9a66dbf51, 0xd15780d656a38e, 0xfe2659931e0790, 0x639292bb3a8a38, 0x6b1d5b16] } }
//     PrimeField { val: BigUint56 { limbs: [0x6297010d4bb2bb, 0xb9adb42e8953cd, 0x52f995c57f384d, 0x5aae21aa31f25f, 0x49dcc6e7] } }
//     PrimeField { val: BigUint56 { limbs: [0x8626e53e690900, 0x4febbc040c54f6, 0x162153c4f875ec, 0x8f17e3c2d670, 0x8481a53a] } }
//      */
// }

// #[test]
// fn get_constant() {
//     // let a = BigUint56::from_bytes([
//     //     51,
//     //     69,
//     //     68,
//     //     26,
//     //     192,
//     //     71,
//     //     84,
//     //     64,
//     //     93,
//     //     14,
//     //     111,
//     //     203,
//     //     99,
//     //     211,
//     //     83,
//     //     233,
//     //     114,
//     //     210,
//     //     245,
//     //     240,
//     //     88,
//     //     85,
//     //     138,
//     //     160,
//     //     220,
//     //     26,
//     //     102,
//     //     221,
//     //     171,
//     //     49,
//     //     135,
//     //     63,
//     // ]);
//     // let a_check = BaseField::from_bytes([
//     //     51,
//     //     69,
//     //     68,
//     //     26,
//     //     192,
//     //     71,
//     //     84,
//     //     64,
//     //     93,
//     //     14,
//     //     111,
//     //     203,
//     //     99,
//     //     211,
//     //     83,
//     //     233,
//     //     114,
//     //     210,
//     //     245,
//     //     240,
//     //     88,
//     //     85,
//     //     138,
//     //     160,
//     //     220,
//     //     26,
//     //     102,
//     //     221,
//     //     171,
//     //     49,
//     //     135,
//     //     63,
//     // ]);
//     // assert(a.lt(BaseField::modulus().val));
//     // assert(a.eq(a_check.val));
//     // println(a_check);
//     // println(BaseField::from_u56(1771 as u56));
//     // println(BaseField::modulus().sub(BaseField::from_u56(11 as u56)).val);

//     // c2
//     println(BigUint56::from_bytes(
//         [5, 217, 64, 51, 122, 73, 255, 238, 128, 34, 189, 154, 115, 187, 234, 250, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 3]
//     ));
// }
// [
//         51,
//         69,
//         68,
//         26,
//         192,
//         71,
//         84,
//         64,
//         93,
//         14,
//         111,
//         203,
//         99,
//         211,
//         83,
//         233,
//         114,
//         210,
//         245,
//         240,
//         88,
//         85,
//         138,
//         160,
//         220,
//         26,
//         102,
//         221,
//         171,
//         49,
//         135,
//         63,
//     ]