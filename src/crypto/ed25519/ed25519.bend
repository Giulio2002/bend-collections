import Base
import ../hash.bend as H
import ../curve25519/field.bend as F
import ../curve25519/x25519.bend as X
import ./scalar.bend as SC
import ./point.bend as PT

# Ed25519 (RFC 8032 section 5.1): key generation (5.1.5), signing (5.1.6)
# and cofactorless verification (5.1.7: [S]B == R + [k]A', S < L checked)
# on byte strings (U32 values below 256); SHA-512 is ../hash.bend's (proved
# equal to FIPS 180-4).
#
# expand(seed) computes once what every signature under the seed needs:
# the curve constants and the base point, the secret scalar s (and s mod
# L), the prefix and the public key A = [s]B; sign_key(key, msg) then does
# one base-point multiplication per signature, as a C signer given the
# expanded secret key does. sign_raw(seed, msg) is sign_key(expand(seed),
# msg).

def cat(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      ys
    case Con{x, xt}:
      Con{x, cat(xt, ys)}

# k = SHA-512(R || A || M) mod L
def hram(rb: List<&2, U32>, +a: List<&2, U32>, +msg: List<&2, U32>) -> List<&2, U32>:
  match rb:
    case Nil{}:
      SC.reduce(H.sha512(cat(Nil{}, cat(a, msg))))
    case Con{x, xt}:
      SC.reduce(H.sha512(cat(Con{x, xt}, cat(a, msg))))

# the secret scalar s (pruned lower half of SHA-512(seed)) and the prefix
def secret(+h: List<&2, U32>) -> List<&2, U32>:
  X.clamp(F.take(32n, h))

def prefix(+h: List<&2, U32>) -> List<&2, U32>:
  F.drop(32n, h)

# A = [s]B, encoded, for the constants c and the base point b
def public_of(+c: PT.Cs, +b: PT.Pt, +h: List<&2, U32>) -> List<&2, U32>:
  PT.encode(PT.cs_r(c), PT.mul(c, secret(h), b))

# the expanded secret key
type Key is Data:
  EdKey{c: PT.Cs, b: PT.Pt, sr: List<&2, U32>, pre: List<&2, U32>, a: List<&2, U32>}

def key_of(+c: PT.Cs, +b: PT.Pt, +h: List<&2, U32>) -> Key:
  EdKey{c, b, SC.reduce(secret(h)), prefix(h), public_of(c, b, h)}

def expand(+seed: List<&2, U32>) -> Key:
  +c = PT.consts(seed)
  key_of(c, PT.base(c), H.sha512(seed))

def key_public(k: Key) -> List<&2, U32>:
  match k:
    case EdKey{c, b, sr, pre, a}:
      a

# A = [s]B, encoded
def public_key(+seed: List<&2, U32>) -> List<&2, U32>:
  +c = PT.consts(seed)
  public_of(c, PT.base(c), H.sha512(seed))

# RFC 8032 5.1.6 with the expanded key: r = SHA-512(prefix || M) mod L,
# R = [r]B, k = SHA-512(R || A || M) mod L, S = (r + k s) mod L
def sign_parts(+c: PT.Cs, +b: PT.Pt, +sr: List<&2, U32>, +pre: List<&2, U32>, +a: List<&2, U32>, +msg: List<&2, U32>) -> List<&2, U32>:
  +r = SC.reduce(H.sha512(cat(pre, msg)))
  +rb = PT.encode(PT.cs_r(c), PT.mul(c, r, b))
  +k = hram(rb, a, msg)
  cat(rb, SC.mul_add(k, sr, r))

def sign_key(k: Key, +msg: List<&2, U32>) -> List<&2, U32>:
  match k:
    case EdKey{+c, +b, +sr, +pre, +a}:
      sign_parts(c, b, sr, pre, a, msg)

def sign_raw(+seed: List<&2, U32>, +msg: List<&2, U32>) -> List<&2, U32>:
  sign_key(expand(seed), msg)

# verification: the scalars S and k are public, so the multiplications
# add only on one bits (PT.mul_vt, the same results as PT.mul)
def check(+c: PT.Cs, +sb: List<&2, U32>, +rb: List<&2, U32>, +pk: List<&2, U32>, +msg: List<&2, U32>, ra: Maybe<&2, PT.Pt>, aa: Maybe<&2, PT.Pt>) -> Bool:
  match ra aa:
    case Some{r} Some{+a}:
      +k = hram(rb, pk, msg)
      PT.equal(PT.cs_r(c), PT.mul_vt(c, sb, PT.base(c)), PT.add(c, r, PT.mul_vt(c, k, a)))
    case _ _:
      False{}

def verify_with(+c: PT.Cs, +pk: List<&2, U32>, +msg: List<&2, U32>, +rb: List<&2, U32>, +sb: List<&2, U32>, s_ok: Bool) -> Bool:
  match s_ok:
    case True{}:
      check(c, sb, rb, pk, msg, PT.decode(c, rb), PT.decode(c, pk))
    case False{}:
      False{}

def verify_raw(+pk: List<&2, U32>, +msg: List<&2, U32>, +sig: List<&2, U32>) -> Bool:
  +sb = F.drop(32n, sig)
  verify_with(PT.consts(pk), pk, msg, F.take(32n, sig), sb, SC.lt_l(sb))
