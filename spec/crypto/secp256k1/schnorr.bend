import Base
import ../sha.bend as FIPS
import ./field.bend as FS
import ./curve.bend as CV

# BIP-340 Schnorr signatures, transcribed from the BIP's "Default Signing"
# and "Verification" sections (and its reference.py), over the natural
# numbers and the FIPS 180-4 SHA-256 specification spec/crypto/sha.bend.
# Nothing of the implementation is used. Every function takes `one`
# (one == 1 in every clause, see field.bend) to write p, n and G.

def p(+one: Nat) -> Nat:
  FS.prime(one)

def n(+one: Nat) -> Nat:
  FS.order(one)

def cat(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, xs, ys)

def bytes32(+x: Nat) -> List<&2, U32>:
  CV.i2osp(32n, x)

def tagged_h(+th: List<&2, U32>, x: List<&2, U32>) -> List<&2, U32>:
  FIPS.sha256_bytes(cat(th, cat(th, x)))

# hash_name(x) = SHA256(SHA256(name) || SHA256(name) || x), name in ASCII
def tagged(tag: List<&2, U32>, x: List<&2, U32>) -> List<&2, U32>:
  tagged_h(FIPS.sha256_bytes(tag), x)

# "BIP0340/aux", "BIP0340/nonce", "BIP0340/challenge"
def tag_aux() -> List<&2, U32>:
  [66, 73, 80, 48, 51, 52, 48, 47, 97, 117, 120]

def tag_nonce() -> List<&2, U32>:
  [66, 73, 80, 48, 51, 52, 48, 47, 110, 111, 110, 99, 101]

def tag_challenge() -> List<&2, U32>:
  [66, 73, 80, 48, 51, 52, 48, 47, 99, 104, 97, 108, 108, 101, 110, 103, 101]

def xor_bytes(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  match xs ys:
    case x <> xt y <> yt: U32.xor(x, y) <> xor_bytes(xt, yt)
    case _ _: Nil{}

# n - x when y is odd (the key or nonce whose point has even y)
def even_b(+m: Nat, b: Nat, +x: Nat) -> Nat:
  match b:
    case 0n: x
    case 1n+k: FS.mneg(m, x)

def even(+m: Nat, +y: Nat, +x: Nat) -> Nat:
  even_b(m, Nat.mod(y, 2n), x)

# ---- verification ----

# lift_x(x): the point with x-coordinate x and even y, if x < p and
# x^3 + 7 is a square
def lift_if(+one: Nat, +x: Nat, ok: Bool) -> Maybe<&2, CV.SPoint>:
  match ok:
    case True{}: CV.decompress(p(one), x, 0n)
    case False{}: None{}

def lift_x(+one: Nat, +x: Nat) -> Maybe<&2, CV.SPoint>:
  lift_if(one, x, Nat.is_lt(x, p(one)))

# fail if is_infinite(R) or not has_even_y(R) or x(R) != r
def check_r(+r: Nat, inf: Bool, a: CV.SAffine) -> Bool:
  match a:
    case CV.SAffine{x, y}: Bool.and(Bool.not(inf), Bool.and(Nat.is_eq(Nat.mod(y, 2n), 0n), Nat.is_eq(x, r)))

# R = s G - e P with e = int(hash_challenge(r || pk || m)) mod n
def verify_rs(+one: Nat, +r: Nat, +s: Nat, +e: Nat, +pp: CV.SPoint) -> Bool:
  +rr = CV.padd(p(one), CV.pmul(p(one), s, CV.g(one)), CV.pmul(p(one), FS.mneg(n(one), e), pp))
  check_r(r, CV.is_inf(rr), CV.to_affine(p(one), rr))

def verify_ok(+one: Nat, +r: Nat, +s: Nat, +e: Nat, +pp: CV.SPoint, ok: Bool) -> Bool:
  match ok:
    case True{}: verify_rs(one, r, s, e, pp)
    case False{}: False{}

# fail if r >= p or s >= n; hc = SHA256("BIP0340/challenge")
def verify_p(+one: Nat, +hc: List<&2, U32>, +pk: List<&2, U32>, +m: List<&2, U32>, +sig: List<&2, U32>, mp: Maybe<&2, CV.SPoint>) -> Bool:
  match mp:
    case None{}: False{}
    case Some{+pp}:
      +r = CV.os2ip(CV.first(32n, sig))
      +s = CV.os2ip(CV.after(32n, sig))
      +e = Nat.mod(CV.os2ip(tagged_h(hc, cat(CV.first(32n, sig), cat(pk, m)))), n(one))
      verify_ok(one, r, s, e, pp, Bool.and(Nat.is_lt(r, p(one)), Nat.is_lt(s, n(one))))

def verify_len(+one: Nat, +hc: List<&2, U32>, +pk: List<&2, U32>, +m: List<&2, U32>, +sig: List<&2, U32>, ok: Bool) -> Bool:
  match ok:
    case True{}: verify_p(one, hc, pk, m, sig, lift_x(one, CV.os2ip(pk)))
    case False{}: False{}

# Verify with the challenge tag's hash hc (named once, in verify)
def verify_h(+one: Nat, +hc: List<&2, U32>, +pk: List<&2, U32>, +m: List<&2, U32>, +sig: List<&2, U32>) -> Bool:
  verify_len(one, hc, pk, m, sig, Bool.and(CV.length_is(32n, pk), CV.length_is(64n, sig)))

# Verify(pk, m, sig): pk 32 bytes, sig 64 bytes, m any length
def verify(+one: Nat, +pk: List<&2, U32>, +m: List<&2, U32>, +sig: List<&2, U32>) -> Bool:
  verify_h(one, FIPS.sha256_bytes(tag_challenge()), pk, m, sig)

# ---- signing ----

# d' = int(sk), 1 <= d' <= n - 1
def secret_ok(+one: Nat, +sk: List<&2, U32>) -> Bool:
  Bool.and(CV.length_is(32n, sk), Bool.and(Bool.not(Nat.is_eq(CV.os2ip(sk), 0n)), Nat.is_lt(CV.os2ip(sk), n(one))))

def pub_of(a: CV.SAffine) -> List<&2, U32>:
  match a:
    case CV.SAffine{x, y}: bytes32(x)

def pubkey_ok(+one: Nat, +sk: List<&2, U32>, ok: Bool) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}: Some{pub_of(CV.to_affine(p(one), CV.pmul(p(one), CV.os2ip(sk), CV.g(one))))}
    case False{}: None{}

# PubKey(sk) = bytes(d' G)
def pubkey(+one: Nat, +sk: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  pubkey_ok(one, sk, secret_ok(one, sk))

# sig = bytes(R) || bytes((k + e d) mod n); if Verify(bytes(P), m, sig)
# fails, abort
def sign_if(+sig: List<&2, U32>, ok: Bool) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}: Some{sig}
    case False{}: None{}

def sign_fin(+one: Nat, +hc: List<&2, U32>, +pb: List<&2, U32>, +m: List<&2, U32>, +sig: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  sign_if(sig, verify_h(one, hc, pb, m, sig))

# R = k' G; k = k' if has_even_y(R), otherwise n - k';
# e = int(hash_challenge(bytes(R) || bytes(P) || m)) mod n
def sign_r(+one: Nat, +hc: List<&2, U32>, +d: Nat, +pb: List<&2, U32>, +m: List<&2, U32>, +k0: Nat, ra: CV.SAffine) -> Maybe<&2, List<&2, U32>>:
  match ra:
    case CV.SAffine{rx, +ry}:
      +k = even(n(one), ry, k0)
      +rb = bytes32(rx)
      +e = Nat.mod(CV.os2ip(tagged_h(hc, cat(rb, cat(pb, m)))), n(one))
      sign_fin(one, hc, pb, m, cat(rb, bytes32(FS.madd(n(one), k, FS.mmul(n(one), e, d)))))

# k' = int(rand) mod n; fail if k' = 0
def sign_kz(+one: Nat, +hc: List<&2, U32>, +d: Nat, +pb: List<&2, U32>, +m: List<&2, U32>, +k0: Nat, zero: Bool) -> Maybe<&2, List<&2, U32>>:
  match zero:
    case True{}: None{}
    case False{}: sign_r(one, hc, d, pb, m, k0, CV.to_affine(p(one), CV.pmul(p(one), k0, CV.g(one))))

def sign_k(+one: Nat, +hc: List<&2, U32>, +d: Nat, +pb: List<&2, U32>, +m: List<&2, U32>, +k0: Nat) -> Maybe<&2, List<&2, U32>>:
  sign_kz(one, hc, d, pb, m, k0, Nat.is_eq(k0, 0n))

# P = d' G; d = d' if has_even_y(P), otherwise n - d';
# t = bytes(d) xor hash_aux(a); rand = hash_nonce(t || bytes(P) || m);
# ha, hn, hc the hashes of the aux, nonce and challenge tags
def sign_ph(+one: Nat, +ha: List<&2, U32>, +hn: List<&2, U32>, +hc: List<&2, U32>, +d0: Nat, +m: List<&2, U32>, +aux: List<&2, U32>, pa: CV.SAffine) -> Maybe<&2, List<&2, U32>>:
  match pa:
    case CV.SAffine{px, +py}:
      +d = even(n(one), py, d0)
      +pb = bytes32(px)
      +t = xor_bytes(bytes32(d), tagged_h(ha, aux))
      sign_k(one, hc, d, pb, m, Nat.mod(CV.os2ip(tagged_h(hn, cat(t, cat(pb, m)))), n(one)))

def sign_p(+one: Nat, +d0: Nat, +m: List<&2, U32>, +aux: List<&2, U32>, pa: CV.SAffine) -> Maybe<&2, List<&2, U32>>:
  sign_ph(one, FIPS.sha256_bytes(tag_aux()), FIPS.sha256_bytes(tag_nonce()), FIPS.sha256_bytes(tag_challenge()), d0, m, aux, pa)

def sign_ok(+one: Nat, +sk: List<&2, U32>, +m: List<&2, U32>, +aux: List<&2, U32>, ok: Bool) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}:
      +d0 = CV.os2ip(sk)
      sign_p(one, d0, m, aux, CV.to_affine(p(one), CV.pmul(p(one), d0, CV.g(one))))
    case False{}: None{}

# Sign(sk, m, a): sk and a 32 bytes, m any length
def sign(+one: Nat, +sk: List<&2, U32>, +m: List<&2, U32>, +aux: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  sign_ok(one, sk, m, aux, Bool.and(CV.length_is(32n, aux), secret_ok(one, sk)))
