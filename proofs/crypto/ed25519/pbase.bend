import Base
import ../../../src/crypto/ed25519/ed25519.bend as E
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../src/crypto/curve25519/x25519.bend as X
import ../curve25519/limbs.bend as LM
import ../../lib/u32.bend as U
import ../curve25519/prime.bend as PRM

# Helpers of the Ed25519 proof roots: p - 1, byte bounds, L, the facade's
# optional results.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

def pp1(+one: Nat) -> Nat:
  PRM.pp_of(one)

def ok(+n: Nat, +a: List<&2, U32>, +h: {FS.bytes_ok(n, a) == True{} : Bool}) -> {LM.okb(n, a, 255n) == True{} : Bool}:
  LM.bytes_okb(n, a, h)

def valid_eq(+n: Nat, +xs: List<&2, U32>) -> {X.valid_bytes(n, xs) == FS.bytes_ok(n, xs) : Bool}:
  match n xs:
    case 0n Nil{}:
      {==}
    case 0n Con{y, yt}:
      {==}
    case 1n+m Nil{}:
      {==}
    case 1n+ +m Con{+y, +yt}:
      +e1 = U.is_lt_nat(y, 256)
      +e2 = valid_eq(m, yt)
      Equal.trans(Bool, Bool.and(U32.is_lt(y, 256), X.valid_bytes(m, yt)), Bool.and(Nat.is_lt(v(y), 256n), X.valid_bytes(m, yt)), Bool.and(Nat.is_lt(v(y), 256n), FS.bytes_ok(m, yt)), Equal.cong(Bool, Bool, z => Bool.and(z, X.valid_bytes(m, yt)), U32.is_lt(y, 256), Nat.is_lt(v(y), 256n), e1), Equal.cong(Bool, Bool, z => Bool.and(Nat.is_lt(v(y), 256n), z), X.valid_bytes(m, yt), FS.bytes_ok(m, yt), e2))

def valid_ok(+n: Nat, +xs: List<&2, U32>, +h: {FS.bytes_ok(n, xs) == True{} : Bool}) -> {X.valid_bytes(n, xs) == True{} : Bool}:
  Equal.trans(Bool, X.valid_bytes(n, xs), FS.bytes_ok(n, xs), True{}, valid_eq(n, xs), h)

# the guarded entry points unfold to their bodies
def expand_eq(+ctx: E.Ctx, +seed: List<&2, U32>) -> {E.expand_ctx(ctx, seed) == E.expand_go(ctx, seed) : E.Key}:
  match seed:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

def public_eq(+ctx: E.Ctx, +seed: List<&2, U32>) -> {E.public_key_ctx(ctx, seed) == E.public_go(ctx, seed) : List<&2, U32>}:
  match seed:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

def sign_eq(+k: E.Key, +msg: List<&2, U32>) -> {E.sign_key(k, msg) == E.sign_go(k, msg) : List<&2, U32>}:
  match msg:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

def verify_eq(+ctx: E.Ctx, +pk: List<&2, U32>, +msg: List<&2, U32>, +sig: List<&2, U32>) -> {E.verify_ctx(ctx, pk, msg, sig) == E.verify_go(ctx, pk, msg, sig) : Bool}:
  match msg:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

def kp_go(+ctx: E.Ctx, +seed: List<&2, U32>) -> {E.key_public(E.expand_go(ctx, seed)) == E.public_go(ctx, seed) : List<&2, U32>}:
  match ctx:
    case E.Ctx{c, b}:
      {==}

# the expanded key carries the public key
def kp_eq(+ctx: E.Ctx, +seed: List<&2, U32>) -> {E.key_public(E.expand_ctx(ctx, seed)) == E.public_key_ctx(ctx, seed) : List<&2, U32>}:
  +e1 = Equal.cong(E.Key, List<&2, U32>, k => E.key_public(k), E.expand_ctx(ctx, seed), E.expand_go(ctx, seed), expand_eq(ctx, seed))
  Equal.trans(List<&2, U32>, E.key_public(E.expand_ctx(ctx, seed)), E.key_public(E.expand_go(ctx, seed)), E.public_key_ctx(ctx, seed), e1, Equal.trans(List<&2, U32>, E.key_public(E.expand_go(ctx, seed)), E.public_go(ctx, seed), E.public_key_ctx(ctx, seed), kp_go(ctx, seed), Equal.sym(List<&2, U32>, E.public_key_ctx(ctx, seed), E.public_go(ctx, seed), public_eq(ctx, seed))))
