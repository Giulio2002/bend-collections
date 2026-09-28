import Base
import ../../../src/crypto/blake/blake2b/types.bend as T
import ../../../src/crypto/blake/blake2b/sized.bend as IH
import ../../../src/crypto/argon2/types.bend as A
import ../../../src/crypto/argon2/blamka.bend as G
import ../../../src/crypto/argon2/argon2.bend as I
import ../../../src/crypto/argon2/phc.bend as PH
import ../../../src/crypto/password.bend as PW
import ../../../spec/crypto/argon2/blamka.bend as SG
import ../../../spec/crypto/argon2/argon2.bend as SA
import ./phc.bend as PP
import ./password.bend as PWP

# The contract of src/crypto/argon2 and src/crypto/password.bend (proved in
# proof.bend): the implementation equals the RFC 9106 specification of
# spec/crypto/argon2/ for every input, and the password facade round-trips.

# GB, the multiplication-hardened BLAKE2b mixing (RFC 9106 section 3.6).
law gb_correct:
  for +a: T.Lane
  for +b: T.Lane
  for +c: T.Lane
  for +d: T.Lane
  {G.gb(a, b, c, d) == SG.GB(a, b, c, d) : T.Quad}

# The permutation P.
law p_correct:
  for +v: T.State
  {G.p(v) == SG.P(v) : T.State}

# The compression function G (section 3.5), and its XOR form of later passes.
law compress_correct:
  for +x: A.Block
  for +y: A.Block
  {G.compress(x, y) == SG.G(x, y) : A.Block}

law compress_xor_correct:
  for +x: A.Block
  for +y: A.Block
  for +old: A.Block
  {G.compress_xor(x, y, old) == SG.xor(SG.G(x, y), old) : A.Block}

# BLAKE2b with an nn-byte digest, H' and H0 (sections 3.2, 3.3).
law hash_correct:
  for +nn: Nat
  for +bs: List<&2, U32>
  {IH.hash(nn, bs) == SA.hash(nn, bs) : List<&2, U32>}

law hprime_correct:
  for +tl: Nat
  for +x: List<&2, U32>
  {I.hprime(tl, x) == SA.hprime(tl, x) : List<&2, U32>}

law h0_correct:
  for +p: Nat
  for +tl: Nat
  for +m: Nat
  for +t: Nat
  for +pw: List<&2, U32>
  for +salt: List<&2, U32>
  for +key: List<&2, U32>
  for +ad: List<&2, U32>
  {I.h0(p, tl, m, t, pw, salt, key, ad) == SA.h0(p, tl, m, t, pw, salt, key, ad) : List<&2, U32>}

# The reference index computation of section 3.4.1.2, for |W| < 2^32.
law rel_correct:
  for +w: Nat
  for +j1: U32
  for +k: Nat
  for +hk: {Nat.is_le(k, 32n) == True{} : Bool}
  for +hw: {Nat.is_lt(w, Nat.pow(2n, k)) == True{} : Bool}
  {I.rel(w, j1) == SA.rel(w, j1) : Nat}

# The address blocks of the data-independent segments.
law addresses_correct:
  for +r: Nat
  for +l: Nat
  for +s: Nat
  for +mm: Nat
  for +t: Nat
  for +ctr: Nat
  {I.addresses(r, l, s, mm, t, ctr) == SA.addresses(r, l, s, mm, t, ctr) : A.Block}

# Argon2id: for every password, salt, secret, associated data and
# parameters whose memory fits this implementation (m' <= 2^23 blocks), the
# tag (or None) is the specification's.
law argon2id_correct:
  for +pw: List<&2, U32>
  for +salt: List<&2, U32>
  for +key: List<&2, U32>
  for +ad: List<&2, U32>
  for +t: Nat
  for +m: Nat
  for +p: Nat
  for +tl: Nat
  for +hf: {I.fits(m, p) == True{} : Bool}
  {I.argon2id(pw, salt, key, ad, t, m, p, tl) == SA.argon2id(pw, salt, key, ad, t, m, p, tl) : Maybe<&2, List<&2, U32>>}

# The PHC string parses back to its fields (bytes below 256).
law parse_format:
  for +m: Nat
  for +t: Nat
  for +p: Nat
  for +salt: List<&2, U32>
  for +hash: List<&2, U32>
  for +hs: {PP.ok(salt) == True{} : Bool}
  for +hh: {PP.ok(hash) == True{} : Bool}
  {PH.parse(PH.format(PH.Phc{m, t, p, salt, hash})) == Some{PH.Phc{m, t, p, salt, hash}} : Maybe<&2, PH.Phc>}

# A hash verifies with its password.
law verify_hash:
  for +pw: List<&2, U32>
  for +salt: List<&2, U32>
  for +params: PW.Params
  for +hs: {PP.ok(salt) == True{} : Bool}
  {PWP.verified(pw, PW.hash_password(pw, salt, params)) == True{} : Bool}

# A hash needs no rehash with its own parameters.
law rehash_hash:
  for +pw: List<&2, U32>
  for +salt: List<&2, U32>
  for +params: PW.Params
  for +hs: {PP.ok(salt) == True{} : Bool}
  for +hl: {PWP.len(salt) == PW.salt_len(params) : Nat}
  {PWP.fresh(PW.hash_password(pw, salt, params), params) == False{} : Bool}

# The tag has T bytes, each below 256.
law tag_length:
  for +tl: Nat
  for +x: List<&2, U32>
  {PWP.len(I.hprime(tl, x)) == tl : Nat}

law tag_bytes:
  for +tl: Nat
  for +x: List<&2, U32>
  {PP.ok(I.hprime(tl, x)) == True{} : Bool}
