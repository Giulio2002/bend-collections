import Base
import ../mac.bend as MAC
import ../keccak/keccak.bend as K
import ./limbs.bend as L
import ./field.bend as F
import ./scalar.bend as S
import ./point.bend as P
import ./bytes.bend as B

# ECDSA over secp256k1 (SEC 1 v2 section 4.1) with deterministic nonces
# (RFC 6979 section 3.2, HMAC-SHA256) and low-S signatures (BIP 62 /
# Ethereum's homestead rule, libsecp256k1's secp256k1_ecdsa_sign), public
# key recovery (SEC 1 section 4.1.6, Ethereum's ecrecover) and the Ethereum
# address of a public key. The contract is spec/crypto/secp256k1/ecdsa.bend.
#
# Messages are 32-byte hashes (the caller hashes); keys and signatures are
# byte lists of their SEC 1 lengths, malformed ones are rejected as values.

type Signature is Data:
  Signature{r: List<&2, U32>, s: List<&2, U32>, v: U32}

# ---- scalars from bytes ----

# 1 <= x < n
def scalar_ok(+x: List<&2, Nat>) -> Bool:
  Bool.and(Bool.not(S.is_zero(x)), S.lt_n(x))

# a 32-byte string as a scalar mod n (bits2int with qlen = hlen = 256,
# reduced: SEC 1 section 4.1.3 step 5, RFC 6979 section 2.3.2)
def hash_scalar(+h: List<&2, U32>) -> List<&2, Nat>:
  S.reduce(B.of_be(h))

# ---- RFC 6979 section 3.2, HMAC_DRBG with SHA-256 ----

type Drbg is Data:
  Drbg{k: List<&2, U32>, v: List<&2, U32>}

# HMAC-SHA256 (src/crypto/mac.bend). The key is looked at first (probe),
# so that the proof checker keeps the HMAC of an unknown key folded; both
# cases are MAC.sign(key, msg).
def hmac_go(probe: List<&2, U32>, key: List<&2, U32>, msg: List<&2, U32>) -> List<&2, U32>:
  match probe:
    case Nil{}: MAC.sign(key, msg)
    case b <> t: MAC.sign(key, msg)

def hmac(+key: List<&2, U32>, msg: List<&2, U32>) -> List<&2, U32>:
  hmac_go(key, key, msg)

def cat(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, xs, ys)

def fill(n: Nat, +b: U32) -> List<&2, U32>:
  List.replicate(U32, n, b)

def drbg_v(+k: List<&2, U32>, +v: List<&2, U32>) -> Drbg:
  Drbg{k, hmac(k, v)}

# steps b-g: V = 0x01..., K = 0x00..., then two HMAC rounds over
# V || 0x00 || int2octets(x) || bits2octets(h1) and V || 0x01 || ...
def drbg_step(+k: List<&2, U32>, +v: List<&2, U32>, +tag: U32, +seed: List<&2, U32>) -> Drbg:
  drbg_v(hmac(k, cat(v, tag <> seed)), v)

def drbg_second(d: Drbg, +seed: List<&2, U32>) -> Drbg:
  match d:
    case Drbg{k, v}: drbg_step(k, v, 1, seed)

def drbg_init(+k0: List<&2, U32>, +v0: List<&2, U32>, +seed: List<&2, U32>) -> Drbg:
  drbg_second(drbg_step(k0, v0, 0, seed), seed)

# step h.3: K = HMAC_K(V || 0x00), V = HMAC_K(V)
def drbg_next(+k: List<&2, U32>, +v: List<&2, U32>) -> Drbg:
  drbg_v(hmac(k, cat(v, [0])), v)

# ---- signing ----

def b2n(b: Bool) -> Nat:
  L.b2n(b)

type Attempt is Data:
  ARetry{}
  ADone{sig: Signature}

def finish_if(bad: Bool, +sig: Signature) -> Attempt:
  match bad:
    case True{}: ARetry{}
    case False{}: ADone{sig}

# r = x(R) mod n, s = k^-1 (z + r d) mod n, made low (s > n / 2 is replaced
# by n - s, which flips the parity bit of the recovery id); the recovery
# id is the parity of y(R), plus 2 when x(R) >= n
def finish(+z: List<&2, Nat>, +d: List<&2, Nat>, +k: List<&2, Nat>, +x: List<&2, Nat>, +y: List<&2, Nat>) -> Attempt:
  +r = S.reduce(x)
  +s0 = S.mul(S.inv(k), S.add(z, S.mul(r, d)))
  +high = b2n(S.is_high(s0))
  +par = F.parity(y)
  +id = Nat.add(Nat.mul(b2n(Bool.not(S.lt_n(x))), 2n), Nat.sub(Nat.add(par, high), Nat.mul(Nat.mul(par, high), 2n)))
  finish_if(Bool.or(S.is_zero(r), S.is_zero(s0)), Signature{B.to_be(r), B.to_be(S.select(high, S.neg(s0), s0)), U32.from_nat(id)})

def attempt_aff(+z: List<&2, Nat>, +d: List<&2, Nat>, +k: List<&2, Nat>, a: P.Affine) -> Attempt:
  match a:
    case P.Affine{x, y}: finish(z, d, k, x, y)

def attempt_ok(+z: List<&2, Nat>, +d: List<&2, Nat>, +k: List<&2, Nat>, ok: Bool) -> Attempt:
  match ok:
    case True{}: attempt_aff(z, d, k, P.to_affine(P.mul(k, P.g())))
    case False{}: ARetry{}

# the candidate k = bits2int(V) (RFC 6979 step h.3): used when 1 <= k < n
def attempt(+z: List<&2, Nat>, +d: List<&2, Nat>, +v: List<&2, U32>) -> Attempt:
  +k = B.of_be(v)
  attempt_ok(z, d, k, scalar_ok(k))

# step h: the candidate V; a k outside [1, n - 1], or one giving r = 0 or
# s = 0 (SEC 1 section 4.1.3 steps 3 and 6), is replaced by the next
# candidate: K = HMAC_K(V || 0x00), V = HMAC_K(V), V = HMAC_K(V). The loop
# stops after `fuel` candidates (the chance that even 2 are needed is below
# 2^-127).
def sign_loop(fuel: Nat, +z: List<&2, Nat>, +d: List<&2, Nat>, +k: List<&2, U32>, +v: List<&2, U32>, att: Attempt) -> Maybe<&2, Signature>:
  match fuel att:
    case 0n ARetry{}: None{}
    case 0n ADone{sig}: Some{sig}
    case 1n+f ARetry{}:
      +k2 = hmac(k, cat(v, [0]))
      +v3 = hmac(k2, hmac(k2, v))
      sign_loop(f, z, d, k2, v3, attempt(z, d, v3))
    case 1n+f ADone{sig}: Some{sig}

def sign_drbg(+z: List<&2, Nat>, +d: List<&2, Nat>, g: Drbg) -> Maybe<&2, Signature>:
  match g:
    case Drbg{+k, +v}:
      +v1 = hmac(k, v)
      sign_loop(16n, z, d, k, v1, attempt(z, d, v1))

def secret_if(+d: List<&2, Nat>, ok: Bool) -> Maybe<&2, List<&2, Nat>>:
  match ok:
    case True{}: Some{d}
    case False{}: None{}

# the secret key d, when 1 <= d < n
def secret(+sk: List<&2, U32>) -> Maybe<&2, List<&2, Nat>>:
  +d = B.of_be(sk)
  secret_if(d, Bool.and(B.has_len(32n, sk), scalar_ok(d)))

# sign with a valid secret scalar d: x = int2octets(d),
# h1' = bits2octets(h) = int2octets(bits2int(h) mod n)
# (k0 = 0x00...00 and v0 = 0x01...01, the DRBG's initial K and V)
def sign_d(+k0: List<&2, U32>, +v0: List<&2, U32>, +h: List<&2, U32>, m: Maybe<&2, List<&2, Nat>>) -> Maybe<&2, Signature>:
  match m:
    case None{}: None{}
    case Some{+d}:
      +z = hash_scalar(h)
      sign_drbg(z, d, drbg_init(k0, v0, cat(B.to_be(d), B.to_be(z))))

def sign_h(+sk: List<&2, U32>, +h: List<&2, U32>, ok: Bool) -> Maybe<&2, Signature>:
  match ok:
    case True{}: sign_d(fill(32n, 0), fill(32n, 1), h, secret(sk))
    case False{}: None{}

# the low-S signature of a 32-byte hash under a 32-byte secret key
def sign(+sk: List<&2, U32>, +h: List<&2, U32>) -> Maybe<&2, Signature>:
  sign_h(sk, h, B.has_len(32n, h))

# ---- public keys ----

def public_point(+d: List<&2, Nat>) -> P.Point:
  P.mul(d, P.g())

def pk_of(compressed: Bool, +q: P.Point) -> List<&2, U32>:
  match compressed:
    case True{}: P.encode_compressed(q)
    case False{}: P.encode_uncompressed(q)

def public_key_d(compressed: Bool, m: Maybe<&2, List<&2, Nat>>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}: None{}
    case Some{d}: Some{pk_of(compressed, public_point(d))}

# the SEC 1 encoding of [d] G (33 bytes compressed, 65 uncompressed)
def public_key(+sk: List<&2, U32>, compressed: Bool) -> Maybe<&2, List<&2, U32>>:
  public_key_d(compressed, secret(sk))

# ---- verification (SEC 1 section 4.1.4) ----

# u1 = z w, u2 = r w with w = s^-1; R = [u1] G + [u2] Q must not be the
# point at infinity and x(R) mod n must be r
def verify_rs(+q: P.Point, +z: List<&2, Nat>, +r: List<&2, Nat>, +s: List<&2, Nat>) -> Bool:
  +w = S.inv(s)
  +rr = P.add(P.mul_pub(S.mul(z, w), P.g()), P.mul_pub(S.mul(r, w), q))
  Bool.and(Bool.not(P.is_inf(rr)), S.eq(S.reduce(P.aff_x(P.to_affine(rr))), r))

def verify_ok(+q: P.Point, +z: List<&2, Nat>, +r: List<&2, Nat>, +s: List<&2, Nat>, ok: Bool) -> Bool:
  match ok:
    case True{}: verify_rs(q, z, r, s)
    case False{}: False{}

def verify_q(+h: List<&2, U32>, +sig: List<&2, U32>, strict: Bool, m: Maybe<&2, P.Point>) -> Bool:
  match m:
    case None{}: False{}
    case Some{+q}:
      +r = B.of_be(B.prefix(32n, sig))
      +s = B.of_be(B.suffix(32n, sig))
      verify_ok(q, hash_scalar(h), r, s, Bool.and(Bool.and(scalar_ok(r), scalar_ok(s)), Bool.or(Bool.not(strict), Bool.not(S.is_high(s)))))

def verify_len(+pk: List<&2, U32>, +h: List<&2, U32>, +sig: List<&2, U32>, strict: Bool, ok: Bool) -> Bool:
  match ok:
    case True{}: verify_q(h, sig, strict, P.decode(pk))
    case False{}: False{}

def verify_with(+pk: List<&2, U32>, +h: List<&2, U32>, +sig: List<&2, U32>, strict: Bool) -> Bool:
  verify_len(pk, h, sig, strict, Bool.and(B.has_len(32n, h), B.has_len(64n, sig)))

# SEC 1 verification of a 64-byte r || s against a SEC 1 public key (33 or
# 65 bytes); high s is accepted, as SEC 1 and OpenSSL do
def verify(+pk: List<&2, U32>, +h: List<&2, U32>, +sig: List<&2, U32>) -> Bool:
  verify_with(pk, h, sig, False{})

# the same, rejecting s > n / 2 (Bitcoin's BIP 62/146 LOW_S rule,
# Ethereum's homestead rule for transactions)
def verify_strict(+pk: List<&2, U32>, +h: List<&2, U32>, +sig: List<&2, U32>) -> Bool:
  verify_with(pk, h, sig, True{})

# ---- recovery (SEC 1 section 4.1.6, Ethereum ecrecover) ----

def recover_q(+q: P.Point, inf: Bool) -> Maybe<&2, List<&2, U32>>:
  match inf:
    case True{}: None{}
    case False{}: Some{P.encode_uncompressed(q)}

# Q = r^-1 (s R - z G), with R the point of x-coordinate r + n j (j = id / 2)
# and y parity id mod 2
def recover_r(+z: List<&2, Nat>, +r: List<&2, Nat>, +s: List<&2, Nat>, m: Maybe<&2, P.Point>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}: None{}
    case Some{+pr}:
      +ri = S.inv(r)
      +q = P.add(P.mul_pub(S.mul(S.neg(z), ri), P.g()), P.mul_pub(S.mul(s, ri), pr))
      recover_q(q, P.is_inf(q))

def recover_x(+z: List<&2, Nat>, +r: List<&2, Nat>, +s: List<&2, Nat>, +id: Nat, +x: List<&2, Nat>, ok: Bool) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}: recover_r(z, r, s, P.decompress(x, Nat.mod(id, 2n)))
    case False{}: None{}

# c_n = 2^256 - n and c_p = 2^256 - p as 16-limb field elements
def cn_fe() -> List<&2, Nat>:
  [48831n, 12233n, 41331n, 16429n, 24516n, 20663n, 8985n, 17745n, 1n, 0n, 0n, 0n, 0n, 0n, 0n, 0n]

def cp_fe() -> List<&2, Nat>:
  [977n, 0n, 1n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n]

# (r + n) mod p = (r - c_n + 2^256) mod p = (r - c_n + c_p) mod p
def rn_fe(+r: List<&2, Nat>) -> List<&2, Nat>:
  F.add(F.sub(r, cn_fe()), cp_fe())

# x = r + j n with j = id / 2. For j = 1, r + n must be below p: then
# (r + n) mod p = r + n >= n, while a wrapped r + n - p is below r < n
def recover_ok(+z: List<&2, Nat>, +r: List<&2, Nat>, +s: List<&2, Nat>, +id: Nat, ok: Bool) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}:
      +j = Nat.div(id, 2n)
      +x1 = rn_fe(r)
      recover_x(z, r, s, id, F.select(j, x1, r), Bool.or(Nat.is_eq(j, 0n), Bool.not(S.lt_n(x1))))
    case False{}: None{}

def recover_sig(+h: List<&2, U32>, +sig: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  +r = B.of_be(B.prefix(32n, sig))
  +s = B.of_be(B.prefix(32n, B.suffix(32n, sig)))
  +id = U32.to_nat(B.head(B.suffix(64n, sig)))
  recover_ok(hash_scalar(h), r, s, id, Bool.and(Bool.and(scalar_ok(r), scalar_ok(s)), Nat.is_lt(id, 4n)))

def recover_len(+h: List<&2, U32>, +sig: List<&2, U32>, ok: Bool) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}: recover_sig(h, sig)
    case False{}: None{}

# the 65-byte uncompressed public key that signed the 32-byte hash, from a
# 65-byte r || s || id with id in 0..3 (go-ethereum's crypto.Ecrecover;
# Ethereum's precompile passes id = v - 27); None when r or s is not in
# [1, n - 1], x(R) is not a field element on the curve, or Q is infinity.
# High s is accepted, as the precompile does.
def recover(+h: List<&2, U32>, +sig: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  recover_len(h, sig, Bool.and(B.has_len(32n, h), B.has_len(65n, sig)))

# ---- Ethereum addresses ----

# little-endian U32 words of bytes (a missing byte reads as 0)
def word(+b0: U32, +b1: U32, +b2: U32, +b3: U32) -> U32:
  U32.or(U32.or(b0, U32.shln(b1, 8n)), U32.or(U32.shln(b2, 16n), U32.shln(b3, 24n)))

def words(n: Nat, +bs: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n: Nil{}
    case 1n+k: word(B.head(bs), B.head(B.tail(bs)), B.head(B.suffix(2n, bs)), B.head(B.suffix(3n, bs))) <> words(k, B.suffix(4n, bs))

def pack(ws: List<&2, U32>, +i: U32, a: Array<U32>) -> Array<U32>:
  match ws:
    case Nil{}: a
    case w <> t: pack(t, U32.inc(i), Array.set(U32, a, i, w))

def unpack(ws: List<&1, U32>) -> List<&2, U32>:
  match ws:
    case Nil{}: Nil{}
    case +w <> t: U32.and(w, 255) <> U32.and(U32.shrn(w, 8n), 255) <> U32.and(U32.shrn(w, 16n), 255) <> U32.shrn(w, 24n) <> unpack(t)

def digest_bytes(m: Maybe<&1, Array<U32>>) -> List<&2, U32>:
  match m:
    case None{}: Nil{}
    case Some{a}: unpack(Array.to_list(~U32, a))

# The hash of addresses, as a value (only Keccak-256 exists), so that the
# proofs can keep it folded
type Hash is Data:
  Keccak256{}

def hash(+h: Hash, a: Array<U32>, length: Nat) -> Maybe<&1, Array<U32>>:
  match h:
    case Keccak256{}: K.keccak256(a, length)

# the hash of 64 bytes
def keccak64(+h: Hash, +bs: List<&2, U32>) -> List<&2, U32>:
  digest_bytes(hash(h, pack(words(16n, bs), 0, Array.new(U32, 4n, 0)), 64n))

def eth_if(ok: Bool, +dg: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}: Some{B.suffix(12n, dg)}
    case False{}: None{}

def eth_go(+h: Hash, +pk: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  eth_if(Bool.and(B.has_len(65n, pk), U32.is_eq(B.head(pk), 4)), keccak64(h, B.tail(pk)))

# (the key is looked at first, so that the proof checker keeps an unknown
# address folded)
def eth_with(+h: Hash, pk: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match pk:
    case Nil{}: eth_go(h, Nil{})
    case b <> t: eth_go(h, b <> t)

# the 20-byte Ethereum address of a 65-byte uncompressed public key:
# the last 20 bytes of Keccak-256 of its 64 coordinate bytes
def eth_address(+pk: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  eth_with(Keccak256{}, pk)

# ---- Ethereum's ECRECOVER precompile (address 0x01) ----

def zeros_ok(bs: List<&2, U32>) -> Bool:
  match bs:
    case Nil{}: True{}
    case b <> t: Bool.and(U32.is_eq(b, 0), zeros_ok(t))

def eth_word(m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}: None{}
    case Some{a}: Some{cat(fill(12n, 0), a)}

def addr_word(m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}: None{}
    case Some{pk}: eth_word(eth_address(pk))

def ecrecover_v(+h: List<&2, U32>, +rs: List<&2, U32>, +v: U32, ok: Bool) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}: addr_word(recover(h, cat(rs, [U32.sub(v, 27)])))
    case False{}: None{}

def ecrecover_in(+x: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  +vw = B.prefix(32n, B.suffix(32n, x))
  +v = B.head(B.suffix(31n, vw))
  ecrecover_v(B.prefix(32n, x), B.suffix(64n, x), v, Bool.and(zeros_ok(B.prefix(31n, vw)), Bool.or(U32.is_eq(v, 27), U32.is_eq(v, 28))))

# The precompile's semantics (Ethereum yellow paper appendix E): the input,
# zero-padded or cut to 128 bytes, is hash || v || r || s (32 bytes each,
# big-endian); v must be 27 or 28. The output is the 32-byte word holding
# the signer's address, or None (the precompile's empty output) when v, r
# or s is invalid or no key is recovered.
def ecrecover(input: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  ecrecover_in(B.prefix(128n, cat(input, fill(128n, 0))))
