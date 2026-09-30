import Base
import ../sha512/stream.bend as HS
import ../curve25519/field.bend as F
import ../curve25519/x25519.bend as X
import ./scalar.bend as SC
import ./point.bend as PT

# Ed25519 (RFC 8032 section 5.1): key generation (5.1.5), signing (5.1.6)
# and cofactorless verification (5.1.7: [S]B == R + [k]A', S < L checked)
# on byte strings (U32 values below 256); SHA-512 is ../hash.bend's (proved
# equal to FIPS 180-4).
#
# context(xs) computes the curve constants, the base point and the table
# of its multiples (PT.base_table: 64 rows of 16 points), which a C
# implementation keeps as static tables (xs is any list: it only keeps the
# proof checker from running the computation). The _ctx functions take the
# context, and with it a base-point multiplication is 64 additions
# (PT.mul_base). expand(seed) computes once what every signature under the
# seed needs: the constants and the table, the secret scalar s (and s mod
# L), the prefix and the public key A = [s]B; sign_key(key, msg) then does
# one base-point multiplication per signature, as a C signer given the
# expanded secret key does.
#
# public_key(seed), sign_raw(seed, msg) and verify_raw(pk, msg, sig) take
# no context and make no table (lite: the constants and the base point
# only): their scalar multiplications are the double-and-add of PT.mul and
# PT.mul_vt.

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
      SC.reduce(HS.hash(cat(Nil{}, cat(a, msg))))
    case Con{x, xt}:
      SC.reduce(HS.hash(cat(Con{x, xt}, cat(a, msg))))

# the secret scalar s (pruned lower half of SHA-512(seed)) and the prefix
def secret(+h: List<&2, U32>) -> List<&2, U32>:
  X.clamp(F.take(32n, h))

def prefix(+h: List<&2, U32>) -> List<&2, U32>:
  F.drop(32n, h)

# A = [s]B, encoded, for the constants c and the base point b
# (double-and-add)
def public_of(+c: PT.Cs, +b: PT.Pt, +h: List<&2, U32>) -> List<&2, U32>:
  PT.encode(PT.cs_r(c), PT.mul(c, secret(h), b))

# the same with the table of the base point
def public_of_t(+c: PT.Cs, tab: List<&2, List<&2, PT.Cp>>, +h: List<&2, U32>) -> List<&2, U32>:
  PT.encode(PT.cs_r(c), PT.mul_base(PT.cs_r(c), tab, secret(h)))

# the expanded secret key
type Key is Data:
  EdKey{c: PT.Cs, tab: List<&2, List<&2, PT.Cp>>, sr: List<&2, U32>, pre: List<&2, U32>, a: List<&2, U32>}

def key_of(+c: PT.Cs, +tab: List<&2, List<&2, PT.Cp>>, +h: List<&2, U32>) -> Key:
  EdKey{c, tab, SC.reduce(secret(h)), prefix(h), public_of_t(c, tab, h)}

# the curve constants, the base point and its table
type Ctx is Data:
  Ctx{c: PT.Cs, b: PT.Pt, tab: List<&2, List<&2, PT.Cp>>}

def ctx_of(+c: PT.Cs, +b: PT.Pt) -> Ctx:
  Ctx{c, b, PT.base_table(c, b)}

def context(+xs: List<&2, U32>) -> Ctx:
  +c = PT.consts(xs)
  ctx_of(c, PT.base(c))

def expand_go(ctx: Ctx, +seed: List<&2, U32>) -> Key:
  match ctx:
    case Ctx{+c, b, +tab}:
      key_of(c, tab, HS.hash(seed))

# The entry points inspect a byte-string argument (seed, message) first:
# on an unknown one the proof checker keeps the call as it is instead of
# running the computation whenever it compares two terms containing it.
def expand_ctx(ctx: Ctx, +seed: List<&2, U32>) -> Key:
  match seed:
    case Nil{}:
      expand_go(ctx, Nil{})
    case Con{+h, +t}:
      expand_go(ctx, Con{h, t})

def expand(+seed: List<&2, U32>) -> Key:
  expand_ctx(context(seed), seed)

def key_public(k: Key) -> List<&2, U32>:
  match k:
    case EdKey{c, tab, sr, pre, a}:
      a

# A = [s]B, encoded
def public_go(ctx: Ctx, +seed: List<&2, U32>) -> List<&2, U32>:
  match ctx:
    case Ctx{+c, b, tab}:
      public_of_t(c, tab, HS.hash(seed))

def public_key_ctx(ctx: Ctx, +seed: List<&2, U32>) -> List<&2, U32>:
  match seed:
    case Nil{}:
      public_go(ctx, Nil{})
    case Con{+h, +t}:
      public_go(ctx, Con{h, t})

# Without a context the constants and the base point are computed in the
# call (Lc), with no table. The functions take them as an argument and
# inspect the byte string first, like the entry points above.
type Lc is Data:
  Lc{c: PT.Cs, b: PT.Pt}

def lite(+xs: List<&2, U32>) -> Lc:
  +c = PT.consts(xs)
  Lc{c, PT.base(c)}

def public_lgo(lc: Lc, +seed: List<&2, U32>) -> List<&2, U32>:
  match lc:
    case Lc{+c, +b}:
      public_of(c, b, HS.hash(seed))

def public_lite(lc: Lc, +seed: List<&2, U32>) -> List<&2, U32>:
  match seed:
    case Nil{}:
      public_lgo(lc, Nil{})
    case Con{+h, +t}:
      public_lgo(lc, Con{h, t})

def public_key(+seed: List<&2, U32>) -> List<&2, U32>:
  public_lite(lite(seed), seed)

# RFC 8032 5.1.6 from R = [r]B encoded: k = SHA-512(R || A || M) mod L,
# S = (r + k s) mod L
def sign_fin(+rb: List<&2, U32>, +sr: List<&2, U32>, +r: List<&2, U32>, +a: List<&2, U32>, +msg: List<&2, U32>) -> List<&2, U32>:
  cat(rb, SC.mul_add(hram(rb, a, msg), sr, r))

# with the expanded key: r = SHA-512(prefix || M) mod L, R = [r]B by the
# table
def sign_parts_t(+c: PT.Cs, tab: List<&2, List<&2, PT.Cp>>, +sr: List<&2, U32>, +pre: List<&2, U32>, +a: List<&2, U32>, +msg: List<&2, U32>) -> List<&2, U32>:
  +r = SC.reduce(HS.hash(cat(pre, msg)))
  sign_fin(PT.encode(PT.cs_r(c), PT.mul_base(PT.cs_r(c), tab, r)), sr, r, a, msg)

def sign_go(k: Key, +msg: List<&2, U32>) -> List<&2, U32>:
  match k:
    case EdKey{+c, tab, +sr, +pre, +a}:
      sign_parts_t(c, tab, sr, pre, a, msg)

def sign_key(k: Key, +msg: List<&2, U32>) -> List<&2, U32>:
  match msg:
    case Nil{}:
      sign_go(k, Nil{})
    case Con{+h, +t}:
      sign_go(k, Con{h, t})

# without a context: R = [r]B by double-and-add
def sign_parts(+c: PT.Cs, +b: PT.Pt, +sr: List<&2, U32>, +pre: List<&2, U32>, +a: List<&2, U32>, +msg: List<&2, U32>) -> List<&2, U32>:
  +r = SC.reduce(HS.hash(cat(pre, msg)))
  sign_fin(PT.encode(PT.cs_r(c), PT.mul(c, r, b)), sr, r, a, msg)

def sign_one(+c: PT.Cs, +b: PT.Pt, +h: List<&2, U32>, +msg: List<&2, U32>) -> List<&2, U32>:
  sign_parts(c, b, SC.reduce(secret(h)), prefix(h), public_of(c, b, h), msg)

def sign_lgo(lc: Lc, +seed: List<&2, U32>, +msg: List<&2, U32>) -> List<&2, U32>:
  match lc:
    case Lc{+c, +b}:
      sign_one(c, b, HS.hash(seed), msg)

def sign_lite(lc: Lc, +seed: List<&2, U32>, +msg: List<&2, U32>) -> List<&2, U32>:
  match msg:
    case Nil{}:
      sign_lgo(lc, seed, Nil{})
    case Con{+h, +t}:
      sign_lgo(lc, seed, Con{h, t})

def sign_raw(+seed: List<&2, U32>, +msg: List<&2, U32>) -> List<&2, U32>:
  sign_lite(lite(seed), seed, msg)

# verification: the scalars S and k are public. [k]A' adds only on one
# bits (PT.mul_vt, the same results as PT.mul); [S]B is by the table with a
# context (PT.mul_base_vt: entries by index), by PT.mul_vt without.
def check_t(+c: PT.Cs, tab: List<&2, List<&2, PT.Cp>>, +sb: List<&2, U32>, +rb: List<&2, U32>, +pk: List<&2, U32>, +msg: List<&2, U32>, ra: Maybe<&2, PT.Pt>, aa: Maybe<&2, PT.Pt>) -> Bool:
  match ra aa:
    case Some{r} Some{+a}:
      +k = hram(rb, pk, msg)
      PT.equal(PT.cs_r(c), PT.mul_base_vt(PT.cs_r(c), tab, sb), PT.add(c, r, PT.mul_vt(c, k, a)))
    case _ _:
      False{}

def verify_with_t(+c: PT.Cs, tab: List<&2, List<&2, PT.Cp>>, +pk: List<&2, U32>, +msg: List<&2, U32>, +rb: List<&2, U32>, +sb: List<&2, U32>, s_ok: Bool) -> Bool:
  match s_ok:
    case True{}:
      check_t(c, tab, sb, rb, pk, msg, PT.decode(c, rb), PT.decode(c, pk))
    case False{}:
      False{}

def verify_go(ctx: Ctx, +pk: List<&2, U32>, +msg: List<&2, U32>, +sig: List<&2, U32>) -> Bool:
  match ctx:
    case Ctx{+c, b, tab}:
      +sb = F.drop(32n, sig)
      verify_with_t(c, tab, pk, msg, F.take(32n, sig), sb, SC.lt_l(sb))

def verify_ctx(ctx: Ctx, +pk: List<&2, U32>, +msg: List<&2, U32>, +sig: List<&2, U32>) -> Bool:
  match msg:
    case Nil{}:
      verify_go(ctx, pk, Nil{}, sig)
    case Con{+h, +t}:
      verify_go(ctx, pk, Con{h, t}, sig)

def check(+c: PT.Cs, +b: PT.Pt, +sb: List<&2, U32>, +rb: List<&2, U32>, +pk: List<&2, U32>, +msg: List<&2, U32>, ra: Maybe<&2, PT.Pt>, aa: Maybe<&2, PT.Pt>) -> Bool:
  match ra aa:
    case Some{r} Some{+a}:
      +k = hram(rb, pk, msg)
      PT.equal(PT.cs_r(c), PT.mul_vt(c, sb, b), PT.add(c, r, PT.mul_vt(c, k, a)))
    case _ _:
      False{}

def verify_with(+c: PT.Cs, +b: PT.Pt, +pk: List<&2, U32>, +msg: List<&2, U32>, +rb: List<&2, U32>, +sb: List<&2, U32>, s_ok: Bool) -> Bool:
  match s_ok:
    case True{}:
      check(c, b, sb, rb, pk, msg, PT.decode(c, rb), PT.decode(c, pk))
    case False{}:
      False{}

def verify_lgo(lc: Lc, +pk: List<&2, U32>, +msg: List<&2, U32>, +sig: List<&2, U32>) -> Bool:
  match lc:
    case Lc{+c, +b}:
      +sb = F.drop(32n, sig)
      verify_with(c, b, pk, msg, F.take(32n, sig), sb, SC.lt_l(sb))

def verify_lite(lc: Lc, +pk: List<&2, U32>, +msg: List<&2, U32>, +sig: List<&2, U32>) -> Bool:
  match msg:
    case Nil{}:
      verify_lgo(lc, pk, Nil{}, sig)
    case Con{+h, +t}:
      verify_lgo(lc, pk, Con{h, t}, sig)

def verify_raw(+pk: List<&2, U32>, +msg: List<&2, U32>, +sig: List<&2, U32>) -> Bool:
  verify_lite(lite(pk), pk, msg, sig)
