This Noir `lib` is for hashing to a curve bigger than your backend field (currently default seems to be Grumkin). If you want to hash to a smaller curve it would be more reasonable to leverage `std` library facilities.

Exposes standard interface, consisting of: **`hash_to_curve`, `map_to_curve`, and `hash_to_field`**.

Currently limited to `secp256k1_XMD:SHA-256_SSWU_RO_` with _DST shorter than 256_. \
Other suites and features will be added upon demand.

If [the hasher] in your app is used for other purposes or shared -- pay attention to [Domain Separation Variants](https://www.rfc-editor.org/rfc/rfc9380.html#name-domain-separation-for-expan).
[the hasher]: w.r.t. current limitations it's <https://noir-lang.org/dev/standard_library/cryptographic_primitives/hashes#sha256>
