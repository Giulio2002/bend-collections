import Base
import ../sha/sha256.bend as SHA
import ./limbs.bend as L
import ./field.bend as F
import ./scalar.bend as S
import ./point.bend as P
import ./bytes.bend as B

# BIP-340 Schnorr signatures over secp256k1: x-only public keys (the point
# with even y), tagged SHA-256 hashes, the default signing algorithm (with
# its final verification) and verification. Messages may have any length
# (BIP-340 as revised in 2022). The contract is
# spec/crypto/secp256k1/schnorr.bend.

def cat(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, xs, ys)

# "BIP0340/aux", "BIP0340/nonce", "BIP0340/challenge" in ASCII
def tag_prefix(rest: List<&2, U32>) -> List<&2, U32>:
  66 <> 73 <> 80 <> 48 <> 51 <> 52 <> 48 <> 47 <> rest

def tag_aux() -> List<&2, U32>:
  tag_prefix([97, 117, 120])

def tag_nonce() -> List<&2, U32>:
  tag_prefix([110, 111, 110, 99, 101])

def tag_challenge() -> List<&2, U32>:
  tag_prefix([99, 104, 97, 108, 108, 101, 110, 103, 101])

# SHA256(tag). An argument the proofs keep unknown is looked at first
# (probe), so that the proof checker never evaluates the hash of a tag; both
# cases are the same hash.
def tagh(probe: List<&2, U32>, tag: List<&2, U32>) -> List<&2, U32>:
  match probe:
    case Nil{}: SHA.sha256_bytes(tag)
    case b <> t: SHA.sha256_bytes(tag)

# hash_tag(x) = SHA256(SHA256(tag) || SHA256(tag) || x)
def tagged_h(+th: List<&2, U32>, x: List<&2, U32>) -> List<&2, U32>:
  SHA.sha256_bytes(cat(th, cat(th, x)))

def tagged(tag: List<&2, U32>, x: List<&2, U32>) -> List<&2, U32>:
  tagged_h(SHA.sha256_bytes(tag), x)

def xor_bytes(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  match xs ys:
    case x <> xt y <> yt: U32.xor(x, y) <> xor_bytes(xt, yt)
    case _ _: Nil{}

def is_odd(+y: List<&2, Nat>) -> Nat:
  F.parity(y)

def verify_aff(+r: List<&2, Nat>, inf: Bool, a: P.Affine) -> Bool:
  match a:
    case P.Affine{x, +y}: Bool.and(Bool.not(inf), Bool.and(Nat.is_eq(is_odd(y), 0n), F.eq(x, r)))

# ---- verification ----

# R = [s] G - [e] P must be finite, with even y and x(R) = r
def verify_r(+r: List<&2, Nat>, +rr: P.Point) -> Bool:
  verify_aff(r, P.is_inf(rr), P.to_affine(rr))

def verify_ok(+r: List<&2, Nat>, +s: List<&2, Nat>, +e: List<&2, Nat>, +pp: P.Point, ok: Bool) -> Bool:
  match ok:
    case True{}: verify_r(r, P.mul2(s, S.neg(e), pp))
    case False{}: False{}

def verify_p(+hc: List<&2, U32>, +pk: List<&2, U32>, +m: List<&2, U32>, +sig: List<&2, U32>, mp: Maybe<&2, P.Point>) -> Bool:
  match mp:
    case None{}: False{}
    case Some{+pp}:
      +rb = B.prefix(32n, sig)
      +r = B.of_be(rb)
      +s = B.of_be(B.suffix(32n, sig))
      +e = S.reduce(B.of_be(tagged_h(hc, cat(rb, cat(pk, m)))))
      verify_ok(r, s, e, pp, Bool.and(F.lt_p(r), S.lt_n(s)))

def lift_if(+x: List<&2, Nat>, ok: Bool) -> Maybe<&2, P.Point>:
  match ok:
    case True{}: P.decompress(x, 0n)
    case False{}: None{}

# lift_x: the point with x-coordinate x and even y, if any
def lift_x(+x: List<&2, Nat>) -> Maybe<&2, P.Point>:
  lift_if(x, F.lt_p(x))

def verify_len(+hc: List<&2, U32>, +pk: List<&2, U32>, +m: List<&2, U32>, +sig: List<&2, U32>, ok: Bool) -> Bool:
  match ok:
    case True{}: verify_p(hc, pk, m, sig, lift_x(B.of_be(pk)))
    case False{}: False{}

# Verify with hc = SHA256("BIP0340/challenge")
def verify_h(+hc: List<&2, U32>, +pk: List<&2, U32>, +m: List<&2, U32>, +sig: List<&2, U32>) -> Bool:
  verify_len(hc, pk, m, sig, Bool.and(B.has_len(32n, pk), B.has_len(64n, sig)))

# BIP-340 Verify(pk, m, sig) for a 32-byte x-only key and a 64-byte signature
def verify(+pk: List<&2, U32>, +m: List<&2, U32>, +sig: List<&2, U32>) -> Bool:
  verify_h(tagh(pk, tag_challenge()), pk, m, sig)

# ---- signing ----

# the secret key d', when 1 <= d' < n
def secret_if(+d: List<&2, Nat>, ok: Bool) -> Maybe<&2, List<&2, Nat>>:
  match ok:
    case True{}: Some{d}
    case False{}: None{}

def secret(+sk: List<&2, U32>) -> Maybe<&2, List<&2, Nat>>:
  +d = B.of_be(sk)
  secret_if(d, Bool.and(B.has_len(32n, sk), Bool.and(Bool.not(S.is_zero(d)), S.lt_n(d))))

def pubkey_aff(a: P.Affine) -> List<&2, U32>:
  match a:
    case P.Affine{x, y}: B.to_be(x)

def pubkey_d(m: Maybe<&2, List<&2, Nat>>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}: None{}
    case Some{d}: Some{pubkey_aff(P.to_affine(P.mul(d, P.g())))}

# PubKey(sk) = bytes(d' G), the 32-byte x-only public key
def pubkey(+sk: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  pubkey_d(secret(sk))

# sig = bytes(R) || bytes((k + e d) mod n), then Verify(bytes(P), m, sig)
def sign_ok(+sig: List<&2, U32>, ok: Bool) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}: Some{sig}
    case False{}: None{}

def sign_fin(+hc: List<&2, U32>, +pb: List<&2, U32>, +m: List<&2, U32>, +sig: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  sign_ok(sig, verify_h(hc, pb, m, sig))

def sign_k(+hc: List<&2, U32>, +d: List<&2, Nat>, +pb: List<&2, U32>, +m: List<&2, U32>, +k0: List<&2, Nat>, ra: P.Affine) -> Maybe<&2, List<&2, U32>>:
  match ra:
    case P.Affine{rx, +ry}:
      +k = S.select(is_odd(ry), S.neg(k0), k0)
      +rb = B.to_be(rx)
      +e = S.reduce(B.of_be(tagged_h(hc, cat(rb, cat(pb, m)))))
      sign_fin(hc, pb, m, cat(rb, B.to_be(S.add(k, S.mul(e, d)))))

def sign_nz(+hc: List<&2, U32>, +d: List<&2, Nat>, +pb: List<&2, U32>, +m: List<&2, U32>, +k0: List<&2, Nat>, ok: Bool) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}: sign_k(hc, d, pb, m, k0, P.to_affine(P.mul(k0, P.g())))
    case False{}: None{}

# the signature from d' and P = d' G, with the tag hashes ha, hn, hc of
# "BIP0340/aux", "BIP0340/nonce", "BIP0340/challenge"
def sign_ph(+ha: List<&2, U32>, +hn: List<&2, U32>, +hc: List<&2, U32>, +d0: List<&2, Nat>, +m: List<&2, U32>, +aux: List<&2, U32>, pa: P.Affine) -> Maybe<&2, List<&2, U32>>:
  match pa:
    case P.Affine{px, +py}:
      +d = S.select(is_odd(py), S.neg(d0), d0)
      +pb = B.to_be(px)
      +t = xor_bytes(B.to_be(d), tagged_h(ha, aux))
      +k0 = S.reduce(B.of_be(tagged_h(hn, cat(t, cat(pb, m)))))
      sign_nz(hc, d, pb, m, k0, Bool.not(S.is_zero(k0)))

def sign_p(+d0: List<&2, Nat>, +m: List<&2, U32>, +aux: List<&2, U32>, pa: P.Affine) -> Maybe<&2, List<&2, U32>>:
  sign_ph(tagh(m, tag_aux()), tagh(m, tag_nonce()), tagh(m, tag_challenge()), d0, m, aux, pa)

def sign_d(+m: List<&2, U32>, +aux: List<&2, U32>, md: Maybe<&2, List<&2, Nat>>) -> Maybe<&2, List<&2, U32>>:
  match md:
    case None{}: None{}
    case Some{+d0}: sign_p(d0, m, aux, P.to_affine(P.mul(d0, P.g())))

def sign_len(+sk: List<&2, U32>, +m: List<&2, U32>, +aux: List<&2, U32>, ok: Bool) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}: sign_d(m, aux, secret(sk))
    case False{}: None{}

# BIP-340 Sign(sk, m, a) for a 32-byte secret key and 32 bytes of auxiliary
# randomness; None for an invalid key (or, with negligible probability, a
# zero nonce or a failed self-check)
def sign(+sk: List<&2, U32>, +m: List<&2, U32>, +aux: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  sign_len(sk, m, aux, B.has_len(32n, aux))

# ---- key pairs ----

# A BIP-340 key pair: the secret scalar d' and the affine public point P =
# d' G, computed once (libsecp256k1's secp256k1_keypair), so that signing
# does not multiply by G twice.
type Keypair is Data:
  Keypair{d: List<&2, Nat>, pa: P.Affine}

def keypair_d(md: Maybe<&2, List<&2, Nat>>) -> Maybe<&2, Keypair>:
  match md:
    case None{}: None{}
    case Some{+d0}: Some{Keypair{d0, P.to_affine(P.mul(d0, P.g()))}}

# the key pair of a 32-byte secret key (None when 1 <= d' < n fails)
def keypair(+sk: List<&2, U32>) -> Maybe<&2, Keypair>:
  keypair_d(secret(sk))

def kp_pub1(kp: Keypair) -> List<&2, U32>:
  match kp:
    case Keypair{d, pa}: pubkey_aff(pa)

def kp_pub(mkp: Maybe<&2, Keypair>) -> Maybe<&2, List<&2, U32>>:
  match mkp:
    case None{}: None{}
    case Some{kp}: Some{kp_pub1(kp)}

def sign_kp1(+m: List<&2, U32>, +aux: List<&2, U32>, kp: Keypair) -> Maybe<&2, List<&2, U32>>:
  match kp:
    case Keypair{+d0, pa}: sign_p(d0, m, aux, pa)

def sign_kp_m(+m: List<&2, U32>, +aux: List<&2, U32>, mkp: Maybe<&2, Keypair>) -> Maybe<&2, List<&2, U32>>:
  match mkp:
    case None{}: None{}
    case Some{kp}: sign_kp1(m, aux, kp)

def sign_kp_len(+m: List<&2, U32>, +aux: List<&2, U32>, mkp: Maybe<&2, Keypair>, ok: Bool) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}: sign_kp_m(m, aux, mkp)
    case False{}: None{}

# Sign(sk, m, a) from the key pair of sk (None for no key pair)
def sign_kp(mkp: Maybe<&2, Keypair>, +m: List<&2, U32>, +aux: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  sign_kp_len(m, aux, mkp, B.has_len(32n, aux))
