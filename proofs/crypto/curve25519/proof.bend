import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/curve25519/x25519.bend as S
import ../../../spec/crypto/kex.bend as SK
import ../../../src/crypto/curve25519/field.bend as F
import ../../../src/crypto/curve25519/x25519.bend as X
import ../../../src/crypto/kex.bend as K
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/u32.bend as U
import ../../math/natural/arith.bend as NR
import ./limbs.bend as LM
import ./fieldops.bend as FO
import ./mulw.bend as MW
import ./pow.bend as PW
import ./canon.bend as CN
import ./eqf.bend as EQ
import ./xbits.bend as XB
import ./ladder.bend as LD
import ./prime.bend as PR
import ./cong.bend as G

# Gate for GF(2^255 - 19), X25519 and the key-exchange facade:
# `bend proofs/crypto/curve25519/proof.bend` checks every clause of
# spec/crypto/curve25519/field.bend, spec/crypto/curve25519/x25519.bend and
# spec/crypto/kex.bend, for every input.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

def pp1(+one: Nat) -> Nat:
  PR.pp_of(one)

def ok(+a: List<&2, U32>, +h: {FS.tight(a) == True{} : Bool}) -> {LM.okb(32n, a, 255n) == True{} : Bool}:
  LM.bytes_okb(32n, a, h)

def tight_of(+a: List<&2, U32>, +h: {LM.okb(32n, a, 255n) == True{} : Bool}) -> {FS.tight(a) == True{} : Bool}:
  LM.okb_bytes(32n, a, h)

# a statement about p = 1 + pp, restated about FS.prime(one)
def at_p(+one: Nat, +h1: {one == 1n : Nat}, -M: Nat -> Type, pf: M(1n+pp1(one))) -> M(FS.prime(one)):
  L.subst(Nat, M, 1n+pp1(one), FS.prime(one), Equal.sym(Nat, FS.prime(one), 1n+pp1(one), PR.prime_eq(one, h1)), pf)

# ---- field clauses ----

def add_value(+one: Nat, +h1: {one == 1n : Nat}, +a: List<&2, U32>, +b: List<&2, U32>, +ha: {FS.tight(a) == True{} : Bool}, +hb: {FS.tight(b) == True{} : Bool}) -> FS.Add.value(one, h1, a, b, ha, hb):
  at_p(one, h1, z => {Nat.mod(FS.value(F.add(a, b)), z) == FS.fadd(z, FS.value(a), FS.value(b)) : Nat}, FO.add_mod(one, h1, pp1(one), PR.hP(one, h1), a, b, ok(a, ha), ok(b, hb)))

def add_tight(+one: Nat, +h1: {one == 1n : Nat}, +a: List<&2, U32>, +b: List<&2, U32>, +ha: {FS.tight(a) == True{} : Bool}, +hb: {FS.tight(b) == True{} : Bool}) -> FS.Add.tight(one, h1, a, b, ha, hb):
  tight_of(F.add(a, b), FO.add_okb(one, h1, a, b, ok(a, ha), ok(b, hb)))

def sub_value(+one: Nat, +h1: {one == 1n : Nat}, +a: List<&2, U32>, +b: List<&2, U32>, +ha: {FS.tight(a) == True{} : Bool}, +hb: {FS.tight(b) == True{} : Bool}) -> FS.Sub.value(one, h1, a, b, ha, hb):
  at_p(one, h1, z => {Nat.mod(FS.value(F.sub(a, b)), z) == FS.fsub(z, FS.value(a), FS.value(b)) : Nat}, FO.sub_mod(one, h1, pp1(one), PR.hP(one, h1), a, b, ok(a, ha), ok(b, hb)))

def sub_tight(+one: Nat, +h1: {one == 1n : Nat}, +a: List<&2, U32>, +b: List<&2, U32>, +ha: {FS.tight(a) == True{} : Bool}, +hb: {FS.tight(b) == True{} : Bool}) -> FS.Sub.tight(one, h1, a, b, ha, hb):
  tight_of(F.sub(a, b), FO.sub_okb(one, h1, a, b, ok(a, ha), ok(b, hb)))

def mul_value(+one: Nat, +h1: {one == 1n : Nat}, +a: List<&2, U32>, +b: List<&2, U32>, +ha: {FS.tight(a) == True{} : Bool}, +hb: {FS.tight(b) == True{} : Bool}) -> FS.Mul.value(one, h1, a, b, ha, hb):
  at_p(one, h1, z => {Nat.mod(FS.value(F.mul(a, b)), z) == FS.fmul(z, FS.value(a), FS.value(b)) : Nat}, MW.mul_mod(one, h1, pp1(one), PR.hP(one, h1), a, b, ok(a, ha), ok(b, hb)))

def mul_tight(+one: Nat, +h1: {one == 1n : Nat}, +a: List<&2, U32>, +b: List<&2, U32>, +ha: {FS.tight(a) == True{} : Bool}, +hb: {FS.tight(b) == True{} : Bool}) -> FS.Mul.tight(one, h1, a, b, ha, hb):
  tight_of(F.mul(a, b), MW.mul_okb(one, h1, a, b, ok(a, ha), ok(b, hb)))

def sq_value(+one: Nat, +h1: {one == 1n : Nat}, +a: List<&2, U32>, +ha: {FS.tight(a) == True{} : Bool}) -> FS.Sq.value(one, h1, a, ha):
  at_p(one, h1, z => {Nat.mod(FS.value(F.sq(a)), z) == FS.fmul(z, FS.value(a), FS.value(a)) : Nat}, MW.sq_mod(one, h1, pp1(one), PR.hP(one, h1), a, ok(a, ha)))

def sq_tight(+one: Nat, +h1: {one == 1n : Nat}, +a: List<&2, U32>, +ha: {FS.tight(a) == True{} : Bool}) -> FS.Sq.tight(one, h1, a, ha):
  tight_of(F.sq(a), MW.sq_okb(one, h1, a, ok(a, ha)))

def mul_small_value(+one: Nat, +h1: {one == 1n : Nat}, +a: List<&2, U32>, +k: U32, +ha: {FS.tight(a) == True{} : Bool}, +hk: {Nat.is_lt(U32.to_nat(k), C.shift(17n, one)) == True{} : Bool}) -> FS.MulSmall.value(one, h1, a, k, ha, hk):
  at_p(one, h1, z => {Nat.mod(FS.value(F.mul_small(a, k)), z) == FS.fmul(z, FS.value(a), U32.to_nat(k)) : Nat}, MW.mul_small_mod(one, h1, pp1(one), PR.hP(one, h1), a, k, ok(a, ha), N.lt_le(v(k), WD.sc(17n, one), hk)))

def mul_small_tight(+one: Nat, +h1: {one == 1n : Nat}, +a: List<&2, U32>, +k: U32, +ha: {FS.tight(a) == True{} : Bool}, +hk: {Nat.is_lt(U32.to_nat(k), C.shift(17n, one)) == True{} : Bool}) -> FS.MulSmall.tight(one, h1, a, k, ha, hk):
  tight_of(F.mul_small(a, k), MW.mul_small_okb(one, h1, a, k, ok(a, ha), N.lt_le(v(k), WD.sc(17n, one), hk)))

def select_zero(+one: Nat, +h1: {one == 1n : Nat}, +a: List<&2, U32>, +b: List<&2, U32>, +ha: {FS.tight(a) == True{} : Bool}, +hb: {FS.tight(b) == True{} : Bool}) -> FS.Select.zero(one, h1, a, b, ha, hb):
  FO.select0(one, h1, 32n, a, b, ok(a, ha), ok(b, hb))

def select_one(+one: Nat, +h1: {one == 1n : Nat}, +a: List<&2, U32>, +b: List<&2, U32>, +ha: {FS.tight(a) == True{} : Bool}, +hb: {FS.tight(b) == True{} : Bool}) -> FS.Select.one(one, h1, a, b, ha, hb):
  FO.select1(one, h1, 32n, a, b, ok(a, ha), ok(b, hb))

def inv_value(+one: Nat, +h1: {one == 1n : Nat}, +a: List<&2, U32>, +ha: {FS.tight(a) == True{} : Bool}) -> FS.Inv.value(one, h1, a, ha):
  +pp = pp1(one)
  +e = G.c_trans(pp, FS.value(F.inv(a)), Nat.pow(FS.value(a), Nat.sub(1n+pp, 2n)), FS.finv(1n+pp, FS.value(a)), PW.inv_val(one, h1, pp, PR.hP(one, h1), a, ok(a, ha)), G.c_sym(pp, FS.finv(1n+pp, FS.value(a)), Nat.pow(FS.value(a), Nat.sub(1n+pp, 2n)), G.c_mod(pp, Nat.pow(FS.value(a), Nat.sub(1n+pp, 2n)))))
  at_p(one, h1, z => {Nat.mod(FS.value(F.inv(a)), z) == FS.finv(z, FS.value(a)) : Nat}, Equal.trans(Nat, Nat.mod(FS.value(F.inv(a)), 1n+pp), Nat.mod(FS.finv(1n+pp, FS.value(a)), 1n+pp), FS.finv(1n+pp, FS.value(a)), e, NR.mod_mod(pp, Nat.pow(FS.value(a), Nat.sub(1n+pp, 2n)))))

def inv_tight(+one: Nat, +h1: {one == 1n : Nat}, +a: List<&2, U32>, +ha: {FS.tight(a) == True{} : Bool}) -> FS.Inv.tight(one, h1, a, ha):
  tight_of(F.inv(a), PW.inv_okb(one, h1, a, ok(a, ha)))

def p58_value(+one: Nat, +h1: {one == 1n : Nat}, +a: List<&2, U32>, +ha: {FS.tight(a) == True{} : Bool}) -> FS.PowP58.value(one, h1, a, ha):
  +pp = pp1(one)
  +k = Nat.div(Nat.sub(1n+pp, 5n), 8n)
  +e = G.c_trans(pp, FS.value(F.pow_p58(a)), Nat.pow(FS.value(a), k), FS.fpow(1n+pp, FS.value(a), k), PW.p58_val(one, h1, pp, PR.hP(one, h1), a, ok(a, ha)), G.c_sym(pp, FS.fpow(1n+pp, FS.value(a), k), Nat.pow(FS.value(a), k), G.c_mod(pp, Nat.pow(FS.value(a), k))))
  at_p(one, h1, z => {Nat.mod(FS.value(F.pow_p58(a)), z) == FS.fpow(z, FS.value(a), Nat.div(Nat.sub(z, 5n), 8n)) : Nat}, Equal.trans(Nat, Nat.mod(FS.value(F.pow_p58(a)), 1n+pp), Nat.mod(FS.fpow(1n+pp, FS.value(a), k), 1n+pp), FS.fpow(1n+pp, FS.value(a), k), e, NR.mod_mod(pp, Nat.pow(FS.value(a), k))))

def p58_tight(+one: Nat, +h1: {one == 1n : Nat}, +a: List<&2, U32>, +ha: {FS.tight(a) == True{} : Bool}) -> FS.PowP58.tight(one, h1, a, ha):
  tight_of(F.pow_p58(a), PW.p58_okb(one, h1, a, ok(a, ha)))

def freeze_value(+one: Nat, +h1: {one == 1n : Nat}, +a: List<&2, U32>, +ha: {FS.tight(a) == True{} : Bool}) -> FS.Freeze.value(one, h1, a, ha):
  at_p(one, h1, z => {FS.value(F.freeze(a)) == Nat.mod(FS.value(a), z) : Nat}, CN.freeze_val(one, h1, pp1(one), PR.hP(one, h1), a, ok(a, ha)))

def freeze_tight(+one: Nat, +h1: {one == 1n : Nat}, +a: List<&2, U32>, +ha: {FS.tight(a) == True{} : Bool}) -> FS.Freeze.tight(one, h1, a, ha):
  tight_of(F.freeze(a), CN.freeze_okb(one, h1, pp1(one), PR.hP(one, h1), a, ok(a, ha)))

def of_bytes_tight(+one: Nat, +h1: {one == 1n : Nat}, +bs: List<&2, U32>, +hb: {FS.tight(bs) == True{} : Bool}) -> FS.OfBytes.tight(one, h1, bs, hb):
  tight_of(F.of_bytes(bs), XB.mask_okb(31n, bs, ok(bs, hb)))

def eq_value(+one: Nat, +h1: {one == 1n : Nat}, +a: List<&2, U32>, +b: List<&2, U32>, +ha: {FS.tight(a) == True{} : Bool}, +hb: {FS.tight(b) == True{} : Bool}) -> FS.Eq.value(one, h1, a, b, ha, hb):
  at_p(one, h1, z => {F.eq(a, b) == Nat.is_eq(Nat.mod(FS.value(a), z), Nat.mod(FS.value(b), z)) : Bool}, EQ.eq_val(one, h1, pp1(one), PR.hP(one, h1), a, b, ok(a, ha), ok(b, hb)))

def is_zero_value(+one: Nat, +h1: {one == 1n : Nat}, +a: List<&2, U32>, +ha: {FS.tight(a) == True{} : Bool}) -> FS.IsZero.value(one, h1, a, ha):
  at_p(one, h1, z => {F.is_zero(a) == Nat.is_eq(Nat.mod(FS.value(a), z), 0n) : Bool}, CN.is_zero_val(one, h1, pp1(one), PR.hP(one, h1), a, ok(a, ha)))

def parity_value(+one: Nat, +h1: {one == 1n : Nat}, +a: List<&2, U32>, +ha: {FS.tight(a) == True{} : Bool}) -> FS.Parity.value(one, h1, a, ha):
  at_p(one, h1, z => {U32.to_nat(F.parity(a)) == Nat.mod(Nat.mod(FS.value(a), z), 2n) : Nat}, CN.parity_val(one, h1, pp1(one), PR.hP(one, h1), a, ok(a, ha)))

# ---- X25519 ----

def x25519_value(+one: Nat, +h1: {one == 1n : Nat}, +k: List<&2, U32>, +u: List<&2, U32>, +hk: {FS.tight(k) == True{} : Bool}, +hu: {FS.tight(u) == True{} : Bool}) -> S.X25519.value(one, h1, k, u, hk, hu):
  LD.x25519_value(one, h1, k, u, hk, hu)

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

def checked_by(+one: Nat, +h1: {one == 1n : Nat}, +k: List<&2, U32>, +u: List<&2, U32>, +b1: Bool, +e1: {FS.tight(k) == b1 : Bool}, +b2: Bool, +e2: {FS.tight(u) == b2 : Bool}) -> {X.x25519_if(Bool.and(b1, b2), k, u) == Bool.pick(Maybe<&2, List<&2, U32>>, Bool.and(b1, b2), Some{S.x25519(one, k, u)}, None{}) : Maybe<&2, List<&2, U32>>}:
  match b1 b2:
    case True{} True{}:
      Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, z => Some{z}, X.x25519_raw(k, u), S.x25519(one, k, u), x25519_value(one, h1, k, u, e1, e2))
    case True{} False{}:
      {==}
    case False{} _:
      {==}

def x25519_checked(+one: Nat, +h1: {one == 1n : Nat}, +k: List<&2, U32>, +u: List<&2, U32>) -> S.X25519.checked(one, h1, k, u):
  %Equal.sym(Bool, X.valid_bytes(32n, k), FS.tight(k), valid_eq(32n, k)) : {X.x25519_if(Bool.and(_, X.valid_bytes(32n, u)), k, u) == Bool.pick(Maybe<&2, List<&2, U32>>, Bool.and(FS.tight(k), FS.tight(u)), Some{S.x25519(one, k, u)}, None{}) : Maybe<&2, List<&2, U32>>}
  %Equal.sym(Bool, X.valid_bytes(32n, u), FS.tight(u), valid_eq(32n, u)) : {X.x25519_if(Bool.and(FS.tight(k), _), k, u) == Bool.pick(Maybe<&2, List<&2, U32>>, Bool.and(FS.tight(k), FS.tight(u)), Some{S.x25519(one, k, u)}, None{}) : Maybe<&2, List<&2, U32>>}
  checked_by(one, h1, k, u, FS.tight(k), {==}, FS.tight(u), {==})

# ---- the key-exchange facade ----

def le_bytes_ok(+n: Nat, +x: Nat) -> {FS.bytes_ok(n, S.le_bytes(n, x)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+ +m:
      +r = Nat.mod(x, 256n)
      +hr = NR.dm_lt(255n, x)
      +e = U.to_nat_from_nat(r, 8n, {==}, hr)
      +h = L.subst(Nat, z => {Nat.is_lt(z, 256n) == True{} : Bool}, r, v(U32.from_nat(r)), Equal.sym(Nat, v(U32.from_nat(r)), r, e), hr)
      L.and_intro(Nat.is_lt(v(U32.from_nat(r)), 256n), FS.bytes_ok(m, S.le_bytes(m, Nat.div(x, 256n))), h, le_bytes_ok(m, Nat.div(x, 256n)))

def finish_tight(+p: Nat, +st: S.LSt) -> {FS.tight(S.finish(p, st)) == True{} : Bool}:
  match st:
    case S.LSt{+x2, +z2, +x3, +z3, +sw}:
      le_bytes_ok(32n, Nat.mod(FS.fmul(p, S.cs_fst(sw, x2, x3), FS.finv(p, S.cs_fst(sw, z2, z3))), p))

def spec_tight(+one: Nat, +k: List<&2, U32>, +u: List<&2, U32>) -> {FS.tight(S.x25519(one, k, u)) == True{} : Bool}:
  +p = FS.prime(one)
  +x1 = Nat.mod(S.decode_u(u), p)
  finish_tight(p, S.ladder(one, p, S.bits(k), S.decode_scalar(k), x1, S.LSt{1n, 0n, x1, 1n, 0n}))

def zero_eq(+one: Nat, +h1: {one == 1n : Nat}, +ss: List<&2, U32>, +hs: {LM.okb(32n, ss, 255n) == True{} : Bool}) -> {U32.is_eq(F.sum_all(ss, 0), 0) == Nat.is_eq(FS.value(ss), 0n) : Bool}:
  +e1 = CN.u32_iz(F.sum_all(ss, 0))
  +e2 = Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), v(F.sum_all(ss, 0)), CN.sumv(ss), CN.sum_v(one, h1, 32n, ss, 0, hs, CN.cb32_lt(one, h1)))
  Equal.trans(Bool, U32.is_eq(F.sum_all(ss, 0), 0), Nat.is_eq(v(F.sum_all(ss, 0)), 0n), Nat.is_eq(FS.value(ss), 0n), e1, Equal.trans(Bool, Nat.is_eq(v(F.sum_all(ss, 0)), 0n), Nat.is_eq(CN.sumv(ss), 0n), Nat.is_eq(FS.value(ss), 0n), e2, CN.iz_sum(ss)))

def base_eq() -> {X.base() == SK.base() : List<&2, U32>}:
  {==}

def base_tight() -> {FS.tight(X.base()) == True{} : Bool}:
  {==}

def kex_public(+one: Nat, +h1: {one == 1n : Nat}, +seed: List<&2, U32>, +hs: {FS.tight(seed) == True{} : Bool}) -> SK.Kex.public(one, h1, seed, hs):
  e = x25519_checked(one, h1, seed, X.base())
  %Equal.sym(Maybe<&2, List<&2, U32>>, X.x25519(seed, X.base()), Bool.pick(Maybe<&2, List<&2, U32>>, Bool.and(FS.tight(seed), FS.tight(X.base())), Some{S.x25519(one, seed, X.base())}, None{}), e) : {K.keypair_of(seed, _) == Some{K.Keypair{seed, S.x25519(one, seed, SK.base())}} : Maybe<&2, K.Keypair>}
  %Equal.sym(Bool, FS.tight(seed), True{}, hs) : {K.keypair_of(seed, Bool.pick(Maybe<&2, List<&2, U32>>, Bool.and(_, FS.tight(X.base())), Some{S.x25519(one, seed, X.base())}, None{})) == Some{K.Keypair{seed, S.x25519(one, seed, SK.base())}} : Maybe<&2, K.Keypair>}
  {==}

def nz_eq(+ss: List<&2, U32>, +z: Bool) -> {K.nonzero(ss, z) == SK.unless_zero(ss, z) : Maybe<&2, List<&2, U32>>}:
  match z:
    case True{}:
      {==}
    case False{}:
      {==}

def shared_by(+one: Nat, +h1: {one == 1n : Nat}, +ss: List<&2, U32>, +hs: {FS.tight(ss) == True{} : Bool}) -> {K.shared_of(Some{ss}) == SK.unless_zero(ss, Nat.is_eq(FS.value(ss), 0n)) : Maybe<&2, List<&2, U32>>}:
  +e1 = zero_eq(one, h1, ss, ok(ss, hs))
  %Equal.sym(Bool, U32.is_eq(F.sum_all(ss, 0), 0), Nat.is_eq(FS.value(ss), 0n), e1) : {K.nonzero(ss, _) == SK.unless_zero(ss, Nat.is_eq(FS.value(ss), 0n)) : Maybe<&2, List<&2, U32>>}
  nz_eq(ss, Nat.is_eq(FS.value(ss), 0n))

def kex_shared(+one: Nat, +h1: {one == 1n : Nat}, +sk: List<&2, U32>, +pk: List<&2, U32>, +hs: {FS.tight(sk) == True{} : Bool}, +hp: {FS.tight(pk) == True{} : Bool}) -> SK.Kex.shared(one, h1, sk, pk, hs, hp):
  e = x25519_checked(one, h1, sk, pk)
  %Equal.sym(Maybe<&2, List<&2, U32>>, X.x25519(sk, pk), Bool.pick(Maybe<&2, List<&2, U32>>, Bool.and(FS.tight(sk), FS.tight(pk)), Some{S.x25519(one, sk, pk)}, None{}), e) : {K.shared_of(_) == SK.unless_zero(S.x25519(one, sk, pk), Nat.is_eq(FS.value(S.x25519(one, sk, pk)), 0n)) : Maybe<&2, List<&2, U32>>}
  %Equal.sym(Bool, FS.tight(sk), True{}, hs) : {K.shared_of(Bool.pick(Maybe<&2, List<&2, U32>>, Bool.and(_, FS.tight(pk)), Some{S.x25519(one, sk, pk)}, None{})) == SK.unless_zero(S.x25519(one, sk, pk), Nat.is_eq(FS.value(S.x25519(one, sk, pk)), 0n)) : Maybe<&2, List<&2, U32>>}
  %Equal.sym(Bool, FS.tight(pk), True{}, hp) : {K.shared_of(Bool.pick(Maybe<&2, List<&2, U32>>, Bool.and(True{}, _), Some{S.x25519(one, sk, pk)}, None{})) == SK.unless_zero(S.x25519(one, sk, pk), Nat.is_eq(FS.value(S.x25519(one, sk, pk)), 0n)) : Maybe<&2, List<&2, U32>>}
  shared_by(one, h1, S.x25519(one, sk, pk), spec_tight(one, sk, pk))

def kex_reject(+sk: List<&2, U32>, +pk: List<&2, U32>, +h: {Bool.and(FS.tight(sk), FS.tight(pk)) == False{} : Bool}) -> SK.Kex.reject(sk, pk, h):
  %Equal.sym(Bool, X.valid_bytes(32n, sk), FS.tight(sk), valid_eq(32n, sk)) : {K.shared_of(X.x25519_if(Bool.and(_, X.valid_bytes(32n, pk)), sk, pk)) == None{} : Maybe<&2, List<&2, U32>>}
  %Equal.sym(Bool, X.valid_bytes(32n, pk), FS.tight(pk), valid_eq(32n, pk)) : {K.shared_of(X.x25519_if(Bool.and(FS.tight(sk), _), sk, pk)) == None{} : Maybe<&2, List<&2, U32>>}
  %Equal.sym(Bool, Bool.and(FS.tight(sk), FS.tight(pk)), False{}, h) : {K.shared_of(X.x25519_if(_, sk, pk)) == None{} : Maybe<&2, List<&2, U32>>}
  {==}
