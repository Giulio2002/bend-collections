import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/u32alg.bend as A
import ../spec/hash_table.bend as S
import ../math/u32div.bend as UD
import ../../src/math/hash.bend as HS
import ./keys.bend as K
import ./buckets.bend as B
import ./modn.bend as M
import ./cyc.bend as CY
import ../spec/common.bend as SC
import ../../src/containers/hash_table.bend as H

# Facts derived from the table invariants for a probed key.

def hb_bf(+sd: Nat, +mask: U32, +key: String, +x: U32, +l: U32, +k: String, +hw: {B.wb(sd, B.BF{x, l, k}) == True{} : Bool}, +e: Bool, +he: {S.str_eq(k, key) == e : Bool}) -> {B.implies(e, Nat.is_eq(UD.v(HS.bucket(x, mask)), UD.v(HS.bucket(K.kword(key), mask)))) == True{} : Bool}:
  match e:
    case False{}:
      {==}
    case True{}:
      +xw = Equal.trans(U32, x, K.kword(k), K.kword(key), A.eq_of(x, K.kword(k), L.and_left(U32.is_eq(x, K.kword(k)), Bool.not(U32.is_eq(l, 0)), L.and_right(Nat.is_lt(UD.v(H.slot(l)), SC.pow2(sd)), Bool.and(U32.is_eq(x, K.kword(k)), Bool.not(U32.is_eq(l, 0))), hw))), Equal.cong(String, U32, z => K.kword(z), k, key, K.str_eq_of(k, key, he)))
      L.subst(U32, z => {B.implies(True{}, Nat.is_eq(UD.v(HS.bucket(z, mask)), UD.v(HS.bucket(K.kword(key), mask)))) == True{} : Bool}, K.kword(key), x, Equal.sym(U32, x, K.kword(key), xw), N.is_eq_refl(UD.v(HS.bucket(K.kword(key), mask))))

def hb_hold(+sd: Nat, +mask: U32, +key: String, +b: B.Bk, +hw: {B.wb(sd, b) == True{} : Bool}) -> {B.implies(B.hold(key, b), Nat.is_eq(B.hb(mask, b), UD.v(HS.bucket(K.kword(key), mask)))) == True{} : Bool}:
  match b:
    case B.BE{}:
      {==}
    case B.BF{+x, +l, +k}:
      hb_bf(sd, mask, key, x, l, k, hw, S.str_eq(k, key), {==})


# every bucket holding key has key's home
def home_all(+bs: List<&2, B.Bk>, +sd: Nat, +mask: U32, +key: String, +n: Nat, +hwell: {B.all_lt(B.PWell{bs, sd}, n) == True{} : Bool}, +m: Nat, +hm: {Nat.is_le(m, n) == True{} : Bool}) -> {B.all_lt(B.PHome{bs, mask, key, UD.v(HS.bucket(K.kword(key), mask))}, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+q:
      +hq = N.succ_le_lt(q, n, hm)
      L.and_intro(B.eval(B.PHome{bs, mask, key, UD.v(HS.bucket(K.kword(key), mask))}, q), B.all_lt(B.PHome{bs, mask, key, UD.v(HS.bucket(K.kword(key), mask))}, q), hb_hold(sd, mask, key, B.at(bs, q), B.all_inst(B.PWell{bs, sd}, n, hwell, q, hq)), home_all(bs, sd, mask, key, n, hwell, q, N.lt_le(q, n, hq)))

# ---- occupancy ----

def bitv(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# the number of full buckets among the first m
def occn(+bs: List<&2, B.Bk>, +m: Nat) -> Nat:
  match m:
    case 0n:
      0n
    case 1n+q:
      Nat.add(bitv(B.occ(B.at(bs, q))), occn(bs, q))

def Empty0(+bs: List<&2, B.Bk>, +m: Nat) -> Type:
  Sigma<&1, &1, Nat, j => {Nat.is_lt(j, m) == True{} : Bool} & {B.at(bs, j) == B.BE{} : B.Bk}>

def emp_up(+bs: List<&2, B.Bk>, +q: Nat, e: Empty0(bs, q)) -> Empty0(bs, 1n+q):
  match e:
    case Tuple{+j, Tuple{hj, hz}}:
      (j, (N.lt_trans(j, q, 1n+q, hj, N.lt_succ(q)), hz))

def emp_c(+bs: List<&2, B.Bk>, +q: Nat, +b: B.Bk, +hb: {B.at(bs, q) == b : B.Bk}, +h: {Nat.is_lt(Nat.add(bitv(B.occ(b)), occn(bs, q)), 1n+q) == True{} : Bool}, rec: @hq: {Nat.is_lt(occn(bs, q), q) == True{} : Bool} -> Empty0(bs, q)) -> Empty0(bs, 1n+q):
  match b:
    case B.BE{}:
      (q, (N.lt_succ(q), hb))
    case B.BF{x, l, k}:
      emp_up(bs, q, rec(h))

# fewer full buckets than buckets: some bucket is empty
def find_empty(+bs: List<&2, B.Bk>, +m: Nat, +h: {Nat.is_lt(occn(bs, m), m) == True{} : Bool}) -> Empty0(bs, m):
  match m:
    case 0n:
      Empty.absurd(Empty0(bs, 0n), N.lt_zero_absurd(occn(bs, 0n), h))
    case 1n+q:
      emp_c(bs, q, B.at(bs, q), {==}, h, hq => find_empty(bs, q, hq))

# the probe theorem for a table size n > 0 started at its home h
def pos0(+bp: Nat, +h: Nat, +hh: {Nat.is_lt(h, 1n+bp) == True{} : Bool}) -> {M.pos(1n+bp, h, 0n) == h : Nat}:
  Equal.trans(Nat, Nat.mod(Nat.add(h, 0n), 1n+bp), Nat.mod(h, 1n+bp), h, Equal.cong(Nat, Nat, z => Nat.mod(z, 1n+bp), Nat.add(h, 0n), h, N.add_zero(h)), CY.mod_small(1n+bp, h, hh))

def pf_ok_n(+bs: List<&2, B.Bk>, +n: Nat, +hn: {Nat.is_lt(0n, n) == True{} : Bool}, +mask: U32, +key: String, +h: Nat, +hh: {Nat.is_lt(h, n) == True{} : Bool}, +cl: {B.cluster(bs, n, mask) == True{} : Bool}, +ho: {B.all_lt(B.PHome{bs, mask, key, h}, n) == True{} : Bool}, +e0: Nat, +he0: {Nat.is_lt(e0, n) == True{} : Bool}, +hz0: {B.at(bs, e0) == B.BE{} : B.Bk}) -> B.ResOK(bs, n, h, key, B.pf(key, bs, n, n, B.mstep(key, B.at(bs, h)), h)):
  match n:
    case 0n:
      Empty.absurd(B.ResOK(bs, 0n, h, key, B.pf(key, bs, 0n, 0n, B.mstep(key, B.at(bs, h)), h)), L.false_true(hn))
    case 1n+bp:
      L.subst(Nat, z => B.ResOK(bs, 1n+bp, h, key, B.pf(key, bs, 1n+bp, 1n+bp, B.mstep(key, B.at(bs, z)), z)), M.pos(1n+bp, h, 0n), h, pos0(bp, h, hh), B.pf_ok(bs, bp, mask, key, h, hh, cl, ho, e0, he0, hz0, 1n+bp, 0n, hn, {==}, {==}))
