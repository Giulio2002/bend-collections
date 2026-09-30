import Base
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/ed25519.bend as SE
import ../../../spec/crypto/sha512.bend as SHA
import ../../../src/crypto/hash.bend as H
import ../../../src/crypto/ed25519/scalar.bend as ESC
import ../../../src/crypto/ed25519/ed25519.bend as E
import ../../lib/logic.bend as L
import ../curve25519/limbs.bend as LM
import ./scalar3.bend as S3
import ./sclause.bend as SL
import ./bytes.bend as BY

# The scalars of Ed25519 from SHA-512 digests (k = H(R || A || M) mod L,
# r = H(prefix || M) mod L) against spec/crypto/ed25519.bend.

def rh_val(+one: Nat, +h1: {one == 1n : Nat}, +bs: List<&2, U32>) -> {FS.value(ESC.reduce(H.sha512(bs))) == Nat.mod(FS.value(SHA.sha512_bytes(bs)), SE.ell(one)) : Nat}:
  +M = {1n+S3.mmL(one) : Nat}
  +hb = H.sha512(bs)
  +sb = SHA.sha512_bytes(bs)
  +e1 = SL.reduce_m(one, h1, hb, BY.sha_lea(bs))
  +e2 = Equal.cong(List<&2, U32>, Nat, z => Nat.mod(FS.value(z), M), hb, sb, BY.sha_eq(bs))
  +e3 = Equal.cong(Nat, Nat, z => Nat.mod(FS.value(sb), z), M, SE.ell(one), S3.ell_eq(one, h1))
  Equal.trans(Nat, FS.value(ESC.reduce(hb)), Nat.mod(FS.value(hb), M), Nat.mod(FS.value(sb), SE.ell(one)), e1, Equal.trans(Nat, Nat.mod(FS.value(hb), M), Nat.mod(FS.value(sb), M), Nat.mod(FS.value(sb), SE.ell(one)), e2, e3))

def rh_eq(+one: Nat, +h1: {one == 1n : Nat}, +bs: List<&2, U32>, +sbs: List<&2, U32>, +e: {bs == sbs : List<&2, U32>}) -> {FS.value(ESC.reduce(H.sha512(bs))) == Nat.mod(FS.value(SHA.sha512_bytes(sbs)), SE.ell(one)) : Nat}:
  Equal.trans(Nat, FS.value(ESC.reduce(H.sha512(bs))), Nat.mod(FS.value(SHA.sha512_bytes(bs)), SE.ell(one)), Nat.mod(FS.value(SHA.sha512_bytes(sbs)), SE.ell(one)), rh_val(one, h1, bs), Equal.cong(List<&2, U32>, Nat, z => Nat.mod(FS.value(SHA.sha512_bytes(z)), SE.ell(one)), bs, sbs, e))

def hram_s(+one: Nat, +rb: List<&2, U32>, +a: List<&2, U32>, +msg: List<&2, U32>) -> {SE.hram(one, rb, a, msg) == Nat.mod(FS.value(SHA.sha512_bytes(SE.cat(rb, SE.cat(a, msg)))), SE.ell(one)) : Nat}:
  match rb:
    case Nil{}:
      {==}
    case Con{x, xt}:
      {==}

def hram_i(+rb: List<&2, U32>, +a: List<&2, U32>, +msg: List<&2, U32>) -> {E.hram(rb, a, msg) == ESC.reduce(H.sha512(E.cat(rb, E.cat(a, msg)))) : List<&2, U32>}:
  match rb:
    case Nil{}:
      {==}
    case Con{x, xt}:
      {==}

def cat2_eq(+x: List<&2, U32>, +sx: List<&2, U32>, +y: List<&2, U32>, +sy: List<&2, U32>, +m: List<&2, U32>, +ex: {x == sx : List<&2, U32>}, +ey: {y == sy : List<&2, U32>}) -> {E.cat(x, E.cat(y, m)) == SE.cat(sx, SE.cat(sy, m)) : List<&2, U32>}:
  +e1 = BY.cat_eq(x, E.cat(y, m))
  +e2 = Equal.cong(List<&2, U32>, List<&2, U32>, z => SE.cat(x, z), E.cat(y, m), SE.cat(y, m), BY.cat_eq(y, m))
  +e3 = Equal.cong(List<&2, U32>, List<&2, U32>, z => SE.cat(z, SE.cat(y, m)), x, sx, ex)
  +e4 = Equal.cong(List<&2, U32>, List<&2, U32>, z => SE.cat(sx, SE.cat(z, m)), y, sy, ey)
  Equal.trans(List<&2, U32>, E.cat(x, E.cat(y, m)), SE.cat(x, E.cat(y, m)), SE.cat(sx, SE.cat(sy, m)), e1, Equal.trans(List<&2, U32>, SE.cat(x, E.cat(y, m)), SE.cat(x, SE.cat(y, m)), SE.cat(sx, SE.cat(sy, m)), e2, Equal.trans(List<&2, U32>, SE.cat(x, SE.cat(y, m)), SE.cat(sx, SE.cat(y, m)), SE.cat(sx, SE.cat(sy, m)), e3, e4)))

def hk_okb(+one: Nat, +h1: {one == 1n : Nat}, +rb: List<&2, U32>, +a: List<&2, U32>, +msg: List<&2, U32>) -> {LM.okb(32n, E.hram(rb, a, msg), 255n) == True{} : Bool}:
  +kh = H.sha512(E.cat(rb, E.cat(a, msg)))
  L.subst(List<&2, U32>, z => {LM.okb(32n, z, 255n) == True{} : Bool}, ESC.reduce(kh), E.hram(rb, a, msg), Equal.sym(List<&2, U32>, E.hram(rb, a, msg), ESC.reduce(kh), hram_i(rb, a, msg)), SL.reduce_okb(one, h1, kh))

def hk_val(+one: Nat, +h1: {one == 1n : Nat}, +rb: List<&2, U32>, +srb: List<&2, U32>, +erb: {rb == srb : List<&2, U32>}, +a: List<&2, U32>, +sa: List<&2, U32>, +ea: {a == sa : List<&2, U32>}, +msg: List<&2, U32>) -> {FS.value(E.hram(rb, a, msg)) == SE.hram(one, srb, sa, msg) : Nat}:
  +KH = E.cat(rb, E.cat(a, msg))
  +SKH = SE.cat(srb, SE.cat(sa, msg))
  +M = Nat.mod(FS.value(SHA.sha512_bytes(SKH)), SE.ell(one))
  +e1 = Equal.cong(List<&2, U32>, Nat, z => FS.value(z), E.hram(rb, a, msg), ESC.reduce(H.sha512(KH)), hram_i(rb, a, msg))
  +e2 = rh_eq(one, h1, KH, SKH, cat2_eq(rb, srb, a, sa, msg, erb, ea))
  Equal.trans(Nat, FS.value(E.hram(rb, a, msg)), FS.value(ESC.reduce(H.sha512(KH))), SE.hram(one, srb, sa, msg), e1, Equal.trans(Nat, FS.value(ESC.reduce(H.sha512(KH))), M, SE.hram(one, srb, sa, msg), e2, Equal.sym(Nat, SE.hram(one, srb, sa, msg), M, hram_s(one, srb, sa, msg))))

# S = (r + k s) mod L, as 32 bytes: s reduced first (the implementation's
# reduce(secret)), the same residue

def ell_m(+one: Nat, +h1: {one == 1n : Nat}) -> {1n+S3.mmL(one) == SE.ell(one) : Nat}:
  S3.ell_eq(one, h1)

# ---- scalars ----

def below(+one: Nat, +h1: {one == 1n : Nat}, +x: Nat, +h: {Nat.is_lt(x, SE.ell(one)) == True{} : Bool}) -> {Nat.is_lt(x, 1n+S3.mmL(one)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(x, z) == True{} : Bool}, SE.ell(one), 1n+S3.mmL(one), Equal.sym(Nat, 1n+S3.mmL(one), SE.ell(one), ell_m(one, h1)), h)
