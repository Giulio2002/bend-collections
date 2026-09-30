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

# xs: an input (the seed or the public key), which keeps the proof checker
# from computing the curve constants (see PT.lit)
def public_of(+c: PT.Cs, +xs: List<&2, U32>, +h: List<&2, U32>) -> List<&2, U32>:
  PT.encode(PT.mul(c, secret(h), PT.base(c, xs)))

# A = [s]B, encoded
def public_key(+seed: List<&2, U32>) -> List<&2, U32>:
  public_of(PT.consts(seed), seed, H.sha512(seed))

def sign_with(+c: PT.Cs, +xs: List<&2, U32>, +h: List<&2, U32>, +msg: List<&2, U32>) -> List<&2, U32>:
  +b = PT.base(c, xs)
  +a = public_of(c, xs, h)
  +r = SC.reduce(H.sha512(cat(prefix(h), msg)))
  +rb = PT.encode(PT.mul(c, r, b))
  +k = hram(rb, a, msg)
  cat(rb, SC.mul_add(k, SC.reduce(secret(h)), r))

def sign_raw(+seed: List<&2, U32>, +msg: List<&2, U32>) -> List<&2, U32>:
  sign_with(PT.consts(seed), seed, H.sha512(seed), msg)

def check(+c: PT.Cs, +sb: List<&2, U32>, +rb: List<&2, U32>, +pk: List<&2, U32>, +msg: List<&2, U32>, ra: Maybe<&2, PT.Pt>, aa: Maybe<&2, PT.Pt>) -> Bool:
  match ra aa:
    case Some{r} Some{+a}:
      +k = hram(rb, pk, msg)
      +b = PT.base(c, pk)
      PT.equal(PT.mul(c, sb, b), PT.add(c, r, PT.mul(c, k, a)))
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
