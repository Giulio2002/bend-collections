import Base
import ../hmac.bend as HM
import ../keccak/main.bend as KS
import ./field.bend as FS
import ./curve.bend as CV

# ECDSA over secp256k1, transcribed from SEC 1 v2 section 4.1 (signing
# 4.1.3, verification 4.1.4, public key recovery 4.1.6) with the nonce of
# RFC 6979 section 3.2 (HMAC_DRBG over HMAC-SHA256, spec/crypto/hmac.bend,
# with qlen = hlen = 256, so bits2int is OS2IP and int2octets is I2OSP(32)),
# the low-S rule of BIP 62 / libsecp256k1 (s > n / 2 is replaced by n - s,
# flipping the recovery id's parity) and Ethereum's address and ECRECOVER
# precompile. Over the natural numbers; nothing of the implementation is
# used. Messages are 32-byte hashes. Every function takes `one` (with
# one == 1 in every clause, see field.bend) to write p, n and G.
#
# Signatures are r || s || v (32 + 32 + 1 bytes, v the recovery id 0..3).

def p(+one: Nat) -> Nat:
  FS.prime(one)

def n(+one: Nat) -> Nat:
  FS.order(one)

def cat(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, xs, ys)

def fill(k: Nat, +b: U32) -> List<&2, U32>:
  List.replicate(U32, k, b)

def i2osp32(+x: Nat) -> List<&2, U32>:
  CV.i2osp(32n, x)

# 1 <= x < n
def scalar_ok(+one: Nat, +x: Nat) -> Bool:
  Bool.and(Bool.not(Nat.is_eq(x, 0n)), Nat.is_lt(x, n(one)))

# e = bits2int(H) mod n (SEC 1 4.1.3 step 5; RFC 6979 2.3.2)
def hash_scalar(+one: Nat, +h: List<&2, U32>) -> Nat:
  Nat.mod(CV.os2ip(h), n(one))

# ---- RFC 6979 section 3.2 ----

type Drbg is Data:
  Drbg{k: List<&2, U32>, v: List<&2, U32>}

def hmac(+key: List<&2, U32>, msg: List<&2, U32>) -> List<&2, U32>:
  HM.hmac(key, msg)

def update_v(+k: List<&2, U32>, +v: List<&2, U32>) -> Drbg:
  Drbg{k, hmac(k, v)}

# K = HMAC_K(V || tag || seed), V = HMAC_K(V)
def update(+k: List<&2, U32>, +v: List<&2, U32>, +tag: U32, +seed: List<&2, U32>) -> Drbg:
  update_v(hmac(k, cat(v, tag <> seed)), v)

def update2(d: Drbg, +seed: List<&2, U32>) -> Drbg:
  match d:
    case Drbg{k, v}: update(k, v, 1, seed)

# steps b-g, with seed = int2octets(x) || bits2octets(h1)
def drbg_init(+seed: List<&2, U32>) -> Drbg:
  update2(update(fill(32n, 0), fill(32n, 1), 0, seed), seed)

# ---- signing (SEC 1 4.1.3) ----

type Attempt is Data:
  Retry{}
  Sig{sig: List<&2, U32>}

# 0 or 1 when b is
def flip(b: Bool, +par: Nat) -> Nat:
  match b:
    case True{}: Nat.sub(1n, par)
    case False{}: par

def low(high: Bool, +m: Nat, +s: Nat) -> Nat:
  match high:
    case True{}: FS.mneg(m, s)
    case False{}: s

def ge2(b: Bool) -> Nat:
  match b:
    case True{}: 0n
    case False{}: 2n

def finish_if(bad: Bool, +sig: List<&2, U32>) -> Attempt:
  match bad:
    case True{}: Retry{}
    case False{}: Sig{sig}

# R = (x, y) = [k] G, r = x mod n, s = k^-1 (e + r d) mod n; r = 0 or
# s = 0 means another k. s > n / 2 (n is odd: n < 2 s) becomes n - s. The
# recovery id is (y mod 2) + 2 (x >= n), with its low bit flipped when s was
# replaced.
def finish(+one: Nat, +e: Nat, +d: Nat, +k: Nat, a: CV.SAffine) -> Attempt:
  match a:
    case CV.SAffine{+x, +y}:
      +m = n(one)
      +r = Nat.mod(x, m)
      +s = FS.mmul(m, FS.minv(m, k), FS.madd(m, e, FS.mmul(m, r, d)))
      +high = Nat.is_lt(m, Nat.double(s))
      finish_if(Bool.or(Nat.is_eq(r, 0n), Nat.is_eq(s, 0n)), cat(i2osp32(r), cat(i2osp32(low(high, m, s)), [U32.from_nat(Nat.add(ge2(Nat.is_lt(x, m)), flip(high, Nat.mod(y, 2n))))])))

def attempt_ok(+one: Nat, +e: Nat, +d: Nat, +k: Nat, ok: Bool) -> Attempt:
  match ok:
    case True{}: finish(one, e, d, k, CV.to_affine(p(one), CV.pmul(p(one), k, CV.g(one))))
    case False{}: Retry{}

# step h.3: k = bits2int(T) with T = V, used when 1 <= k < n
def attempt(+one: Nat, +e: Nat, +d: Nat, +v: List<&2, U32>) -> Attempt:
  +k = CV.os2ip(v)
  attempt_ok(one, e, d, k, scalar_ok(one, k))

# step h, with the retry of step h.3 (K = HMAC_K(V || 0x00),
# V = HMAC_K(V)) before the next V = HMAC_K(V); at most `fuel` candidates
def sign_loop(fuel: Nat, +one: Nat, +e: Nat, +d: Nat, +k: List<&2, U32>, +v: List<&2, U32>, att: Attempt) -> Maybe<&2, List<&2, U32>>:
  match fuel att:
    case 0n Retry{}: None{}
    case 0n Sig{sig}: Some{sig}
    case 1n+f Retry{}:
      +k2 = hmac(k, cat(v, [0]))
      +v3 = hmac(k2, hmac(k2, v))
      sign_loop(f, one, e, d, k2, v3, attempt(one, e, d, v3))
    case 1n+f Sig{sig}: Some{sig}

def sign_drbg(+one: Nat, +e: Nat, +d: Nat, g: Drbg) -> Maybe<&2, List<&2, U32>>:
  match g:
    case Drbg{+k, +v}:
      +v1 = hmac(k, v)
      sign_loop(16n, one, e, d, k, v1, attempt(one, e, d, v1))

def sign_d(+one: Nat, +h: List<&2, U32>, +d: Nat, ok: Bool) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}:
      +e = hash_scalar(one, h)
      sign_drbg(one, e, d, drbg_init(cat(i2osp32(d), i2osp32(e))))
    case False{}: None{}

# sign(sk, H): d = OS2IP(sk) must be a 32-byte key with 1 <= d < n, H 32 bytes
def sign(+one: Nat, +sk: List<&2, U32>, +h: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  sign_d(one, h, CV.os2ip(sk), Bool.and(CV.length_is(32n, h), Bool.and(CV.length_is(32n, sk), scalar_ok(one, CV.os2ip(sk)))))

# ---- public keys ----

def pk_of(+one: Nat, compressed: Bool, +q: CV.SPoint) -> List<&2, U32>:
  match compressed:
    case True{}: CV.encode_compressed(p(one), q)
    case False{}: CV.encode_uncompressed(p(one), q)

def public_d(+one: Nat, compressed: Bool, +d: Nat, ok: Bool) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}: Some{pk_of(one, compressed, CV.pmul(p(one), d, CV.g(one)))}
    case False{}: None{}

# the SEC 1 encoding of Q = [d] G
def public_key(+one: Nat, +sk: List<&2, U32>, compressed: Bool) -> Maybe<&2, List<&2, U32>>:
  public_d(one, compressed, CV.os2ip(sk), Bool.and(CV.length_is(32n, sk), scalar_ok(one, CV.os2ip(sk))))

# ---- verification (SEC 1 4.1.4) ----

# u1 = e s^-1, u2 = r s^-1, R = [u1] G + [u2] Q; valid when R is not the
# point at infinity and x(R) mod n = r
def verify_rs(+one: Nat, +q: CV.SPoint, +e: Nat, +r: Nat, +s: Nat) -> Bool:
  +m = n(one)
  +w = FS.minv(m, s)
  +rr = CV.padd(p(one), CV.pmul(p(one), FS.mmul(m, e, w), CV.g(one)), CV.pmul(p(one), FS.mmul(m, r, w), q))
  Bool.and(Bool.not(CV.is_inf(rr)), Nat.is_eq(Nat.mod(CV.aff_x(CV.to_affine(p(one), rr)), m), r))

def verify_ok(+one: Nat, +q: CV.SPoint, +e: Nat, +r: Nat, +s: Nat, ok: Bool) -> Bool:
  match ok:
    case True{}: verify_rs(one, q, e, r, s)
    case False{}: False{}

# r and s in [1, n - 1]; strict verification also rejects s > n / 2
def verify_q(+one: Nat, +h: List<&2, U32>, +sig: List<&2, U32>, strict: Bool, mq: Maybe<&2, CV.SPoint>) -> Bool:
  match mq:
    case None{}: False{}
    case Some{+q}:
      +r = CV.os2ip(CV.first(32n, sig))
      +s = CV.os2ip(CV.after(32n, sig))
      verify_ok(one, q, hash_scalar(one, h), r, s, Bool.and(Bool.and(scalar_ok(one, r), scalar_ok(one, s)), Bool.or(Bool.not(strict), Bool.not(Nat.is_lt(n(one), Nat.double(s))))))

def verify_len(+one: Nat, +pk: List<&2, U32>, +h: List<&2, U32>, +sig: List<&2, U32>, strict: Bool, ok: Bool) -> Bool:
  match ok:
    case True{}: verify_q(one, h, sig, strict, CV.decode(p(one), pk))
    case False{}: False{}

# verify(Q, H, r || s): Q a SEC 1 public key, H 32 bytes, r || s 64 bytes
def verify(+one: Nat, +pk: List<&2, U32>, +h: List<&2, U32>, +sig: List<&2, U32>, strict: Bool) -> Bool:
  verify_len(one, pk, h, sig, strict, Bool.and(CV.length_is(32n, h), CV.length_is(64n, sig)))

# ---- public key recovery (SEC 1 4.1.6) ----

def recover_q_if(+one: Nat, +q: CV.SPoint, inf: Bool) -> Maybe<&2, List<&2, U32>>:
  match inf:
    case True{}: None{}
    case False{}: Some{CV.encode_uncompressed(p(one), q)}

def recover_q(+one: Nat, +q: CV.SPoint) -> Maybe<&2, List<&2, U32>>:
  recover_q_if(one, q, CV.is_inf(q))

# Q = r^-1 (s R - e G) = [-e r^-1] G + [s r^-1] R
def recover_r(+one: Nat, +e: Nat, +r: Nat, +s: Nat, mr: Maybe<&2, CV.SPoint>) -> Maybe<&2, List<&2, U32>>:
  match mr:
    case None{}: None{}
    case Some{+pr}:
      +m = n(one)
      +ri = FS.minv(m, r)
      recover_q(one, CV.padd(p(one), CV.pmul(p(one), FS.mmul(m, FS.mneg(m, e), ri), CV.g(one)), CV.pmul(p(one), FS.mmul(m, s, ri), pr)))

# R: the point of x-coordinate x = r + j n (j = id / 2, x < p) whose y has
# parity id mod 2
def recover_x_if(+one: Nat, +e: Nat, +r: Nat, +s: Nat, +id: Nat, +x: Nat, ok: Bool) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}: recover_r(one, e, r, s, CV.decompress(p(one), x, Nat.mod(id, 2n)))
    case False{}: None{}

def recover_x(+one: Nat, +e: Nat, +r: Nat, +s: Nat, +id: Nat) -> Maybe<&2, List<&2, U32>>:
  +x = Nat.add(r, Nat.mul(Nat.div(id, 2n), n(one)))
  recover_x_if(one, e, r, s, id, x, Nat.is_lt(x, p(one)))

def recover_ok(+one: Nat, +e: Nat, +r: Nat, +s: Nat, +id: Nat, ok: Bool) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}: recover_x(one, e, r, s, id)
    case False{}: None{}

def recover_len(+one: Nat, +h: List<&2, U32>, +sig: List<&2, U32>, ok: Bool) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}:
      +r = CV.os2ip(CV.first(32n, sig))
      +s = CV.os2ip(CV.first(32n, CV.after(32n, sig)))
      +id = U32.to_nat(CV.head(CV.after(64n, sig)))
      recover_ok(one, hash_scalar(one, h), r, s, id, Bool.and(Bool.and(scalar_ok(one, r), scalar_ok(one, s)), Nat.is_lt(id, 4n)))
    case False{}: None{}

# the 65-byte uncompressed key recovered from H (32 bytes) and
# r || s || id (65 bytes, id in 0..3)
def recover(+one: Nat, +h: List<&2, U32>, +sig: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  recover_len(one, h, sig, Bool.and(CV.length_is(32n, h), CV.length_is(65n, sig)))

# ---- Ethereum ----

# Keccak-256 (spec/crypto/keccak/main.bend) of bytes packed into
# little-endian U32 words, as its interface takes them
def word(+b0: U32, +b1: U32, +b2: U32, +b3: U32) -> U32:
  U32.or(U32.or(b0, U32.shln(b1, 8n)), U32.or(U32.shln(b2, 16n), U32.shln(b3, 24n)))

def words(k: Nat, +bs: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n: Nil{}
    case 1n+j: word(CV.head(bs), CV.head(CV.after(1n, bs)), CV.head(CV.after(2n, bs)), CV.head(CV.after(3n, bs))) <> words(j, CV.after(4n, bs))

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

def keccak64(+bs: List<&2, U32>) -> List<&2, U32>:
  digest_bytes(KS.keccak256_rounds(24n, pack(words(16n, bs), 0, Array.new(U32, 4n, 0)), 64n))

# address = the last 20 bytes of Keccak-256(x || y) of an uncompressed key
def eth_if(+pk: List<&2, U32>, ok: Bool) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}: Some{CV.after(12n, keccak64(CV.after(1n, pk)))}
    case False{}: None{}

def eth_address(+pk: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  eth_if(pk, Bool.and(CV.length_is(65n, pk), U32.is_eq(CV.head(pk), 4)))

def word_of(m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}: None{}
    case Some{a}: Some{cat(fill(12n, 0), a)}

def addr_word(m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}: None{}
    case Some{pk}: word_of(eth_address(pk))

def all_zero(bs: List<&2, U32>) -> Bool:
  match bs:
    case Nil{}: True{}
    case b <> t: Bool.and(U32.is_eq(b, 0), all_zero(t))

def ecrecover_v(+one: Nat, +h: List<&2, U32>, +rs: List<&2, U32>, +v: U32, ok: Bool) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}: addr_word(recover(one, h, cat(rs, [U32.sub(v, 27)])))
    case False{}: None{}

def ecrecover_in(+one: Nat, +x: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  +vw = CV.first(32n, CV.after(32n, x))
  +v = CV.head(CV.after(31n, vw))
  ecrecover_v(one, CV.first(32n, x), CV.after(64n, x), v, Bool.and(all_zero(CV.first(31n, vw)), Bool.or(U32.is_eq(v, 27), U32.is_eq(v, 28))))

# ECRECOVER (precompile 0x01): the input zero-padded or cut to 128 bytes is
# H || v || r || s, v a 32-byte big-endian word that must be 27 or 28;
# the output is the address word (12 zero bytes, then the address) of the
# key recovered with id v - 27, or nothing
def ecrecover(+one: Nat, input: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  ecrecover_in(one, CV.first(128n, cat(input, fill(128n, 0))))
