import Base
import ../../../src/math/u64.bend as W
import ../../../src/math/w64.bend as X
import ../../../src/math/random/rand.bend as R
import ../../../spec/math/random/rand.bend as SR
import ../../../spec/lib/common.bend as SC
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/array.bend as AR
import ../../lib/array_ext.bend as AE
import ../../lib/u32.bend as U
import ./shuffle.bend as SH
import ./ashuffle.bend as AS

# shuffle (src/math/random/rand.bend) returns a permutation of its input list,
# for every source: below 2^31 elements the list is written into a fresh
# array of Maybe slots (fill), shuffled there (shuffle_array,
# ashuffle.bend) and read back (collect); from 2^31 elements on it is the
# list shuffle (shuffle.bend). The count is taken over the Maybe slots with
# the relation lifted to Maybe (None relates to nothing). fill keeps every
# old slot it overwrites (None in a fresh array) and collect every element it
# reads, so no element is lost for any array contents; the index bounds come
# from n <= 2^d.

# rel lifted to Maybe
def mrel(~A: Data, ~V: Data, ~rel: A -> V -> Bool, m: Maybe<&2, A>, +v: V) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      rel(x, v)

def zero_add(+x: Nat) -> {Nat.add(0n, x) == x : Nat}:
  Equal.trans(Nat, Nat.add(0n, x), Nat.add(x, 0n), x, N.add_comm(0n, x), N.add_zero(x))

def succ_add(+a: Nat, +b: Nat) -> {Nat.add(1n+a, b) == 1n+Nat.add(a, b) : Nat}:
  Equal.trans(Nat, Nat.add(1n+a, b), Nat.add(b, 1n+a), 1n+Nat.add(a, b),
    N.add_comm(1n+a, b),
    Equal.trans(Nat, Nat.add(b, 1n+a), 1n+Nat.add(b, a), 1n+Nat.add(a, b), N.add_succ(b, a), N.succ_cong(Nat.add(b, a), Nat.add(a, b), N.add_comm(b, a))))

# (m + x) + (c + r) == m + (c + (x + r))
def rearr(+m: Nat, +x: Nat, +c: Nat, +r: Nat) -> {Nat.add(Nat.add(m, x), Nat.add(c, r)) == Nat.add(m, Nat.add(c, Nat.add(x, r))) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(m, x), Nat.add(c, r)), Nat.add(m, Nat.add(x, Nat.add(c, r))), Nat.add(m, Nat.add(c, Nat.add(x, r))),
    N.add_assoc(m, x, Nat.add(c, r)),
    Equal.cong(Nat, Nat, z => Nat.add(m, z), Nat.add(x, Nat.add(c, r)), Nat.add(c, Nat.add(x, r)),
      Equal.trans(Nat, Nat.add(x, Nat.add(c, r)), Nat.add(Nat.add(x, c), r), Nat.add(c, Nat.add(x, r)),
        Equal.sym(Nat, Nat.add(Nat.add(x, c), r), Nat.add(x, Nat.add(c, r)), N.add_assoc(x, c, r)),
        Equal.trans(Nat, Nat.add(Nat.add(x, c), r), Nat.add(Nat.add(c, x), r), Nat.add(c, Nat.add(x, r)),
          Equal.cong(Nat, Nat, z => Nat.add(z, r), Nat.add(x, c), Nat.add(c, x), N.add_comm(x, c)),
          N.add_assoc(c, x, r)))))

def cons_some_occ(~A: Data, ~V: Data, ~rel: A -> V -> Bool, +v: V, +m: Maybe<&2, A>, +acc: List<&2, A>) -> {AS.occ(~A, ~V, ~rel, v, R.cons_some(A, m, acc)) == Nat.add(SR.b2n(mrel(~A, ~V, ~rel, m, v)), AS.occ(~A, ~V, ~rel, v, acc)) : Nat}:
  match m:
    case None{}:
      Equal.sym(Nat, Nat.add(0n, AS.occ(~A, ~V, ~rel, v, acc)), AS.occ(~A, ~V, ~rel, v, acc), zero_add(AS.occ(~A, ~V, ~rel, v, acc)))
    case Some{+x}:
      {==}

def repl_none(~A: Data, ~V: Data, ~rel: A -> V -> Bool, +v: V, +k: Nat) -> {AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, SC.replicate(Maybe<&2, A>, k, None{})) == 0n : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+q:
      Equal.trans(Nat, Nat.add(0n, AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, SC.replicate(Maybe<&2, A>, q, None{}))), AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, SC.replicate(Maybe<&2, A>, q, None{})), 0n,
        zero_add(AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, SC.replicate(Maybe<&2, A>, q, None{}))),
        repl_none(~A, ~V, ~rel, v, q))

def pow2n_eq(+d: Nat) -> {R.pow2n(d) == SC.pow2(d) : Nat}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => Nat.double(z), R.pow2n(p), SC.pow2(p), pow2n_eq(p))

# ---- fill ----

# the tree and the kept elements after writing xs into slots k, k + 1, ...
def tfill(~A: Data, +d: Nat, xs: List<&2, A>, +k: Nat, +t: AR.Tree<Maybe<&2, A>>, +acc: List<&2, A>, +old: Maybe<&2, A>) -> AR.Tree<Maybe<&2, A>> & List<&2, A>:
  match xs:
    case Nil{}:
      (t, R.cons_some(A, old, acc))
    case Con{+x, rest}:
      tfill(~A, d, rest, 1n+k, AR.upd(Maybe<&2, A>, d, t, U32.to_nat(U32.from_nat(k)), Some{x}), R.cons_some(A, old, acc), AS.at(Maybe<&2, A>, t, U32.to_nat(U32.from_nat(k))))

def fill_bounds(+d: Nat, +k: Nat, +r: Nat, +hk: {Nat.is_le(Nat.add(k, 1n+r), SC.pow2(d)) == True{} : Bool}) -> {Nat.is_lt(k, SC.pow2(d)) == True{} : Bool}:
  +h1 = L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, Nat.add(k, 1n+r), 1n+Nat.add(k, r), N.add_succ(k, r), hk)
  N.le_lt_trans(k, Nat.add(k, r), SC.pow2(d), N.le_add_right(k, r), N.succ_le_lt(Nat.add(k, r), SC.pow2(d), h1))

def fill_next(+d: Nat, +k: Nat, +r: Nat, +hk: {Nat.is_le(Nat.add(k, 1n+r), SC.pow2(d)) == True{} : Bool}) -> {Nat.is_le(Nat.add(1n+k, r), SC.pow2(d)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, Nat.add(k, 1n+r), Nat.add(1n+k, r),
    Equal.trans(Nat, Nat.add(k, 1n+r), 1n+Nat.add(k, r), Nat.add(1n+k, r), N.add_succ(k, r), Equal.sym(Nat, Nat.add(1n+k, r), 1n+Nat.add(k, r), succ_add(k, r))),
    hk)

def tfill_perfect(~A: Data, +d: Nat, +xs: List<&2, A>, +k: Nat, +t: AR.Tree<Maybe<&2, A>>, +acc: List<&2, A>, +old: Maybe<&2, A>, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}) -> {AR.perfect(Maybe<&2, A>, d, R.fst(AR.Tree<Maybe<&2, A>>, List<&2, A>, tfill(~A, d, xs, k, t, acc, old))) == True{} : Bool}:
  match xs:
    case Nil{}:
      pf
    case Con{+x, +rest}:
      tfill_perfect(~A, d, rest, 1n+k, AR.upd(Maybe<&2, A>, d, t, U32.to_nat(U32.from_nat(k)), Some{x}), R.cons_some(A, old, acc), AS.at(Maybe<&2, A>, t, U32.to_nat(U32.from_nat(k))),
        AR.upd_perfect(Maybe<&2, A>, d, t, U32.to_nat(U32.from_nat(k)), Some{x}, pf))

def fill_mirror(~A: Data, +d: Nat, +xs: List<&2, A>, +k: Nat, +acc: List<&2, A>, +t: AR.Tree<Maybe<&2, A>>, +old: Maybe<&2, A>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hk: {Nat.is_le(Nat.add(k, SC.length(A, xs)), SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}) -> {R.fill(~A, xs, k, acc, (AR.thaw(Maybe<&2, A>, t), old)) == AS.tthaw(Maybe<&2, A>, List<&2, A>, tfill(~A, d, xs, k, t, acc, old)) : Array<Maybe<&2, A>> & List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +kk = U32.to_nat(U32.from_nat(k))
      +y = AS.at(Maybe<&2, A>, t, kk)
      +t2 = AR.upd(Maybe<&2, A>, d, t, kk, Some{x})
      +hkk = AS.idx_i(d, k, hd, fill_bounds(d, k, SC.length(A, rest), hk))
      Equal.trans(Array<Maybe<&2, A>> & List<&2, A>, R.fill(~A, Con{x, rest}, k, acc, (AR.thaw(Maybe<&2, A>, t), old)), R.fill(~A, rest, 1n+k, R.cons_some(A, old, acc), (AR.thaw(Maybe<&2, A>, t2), y)), AS.tthaw(Maybe<&2, A>, List<&2, A>, tfill(~A, d, rest, 1n+k, t2, R.cons_some(A, old, acc), y)),
        Equal.cong(Array<Maybe<&2, A>> & Maybe<&2, A>, Array<Maybe<&2, A>> & List<&2, A>, z => R.fill(~A, rest, 1n+k, R.cons_some(A, old, acc), z), Array.swap(Maybe<&2, A>, AR.thaw(Maybe<&2, A>, t), U32.from_nat(k), Some{x}), (AR.thaw(Maybe<&2, A>, t2), y),
          AR.swap(Maybe<&2, A>, d, t, U32.from_nat(k), Some{x}, y, hd, hkk, AS.at_nth(Maybe<&2, A>, d, t, kk, pf, hkk), pf)),
        fill_mirror(~A, d, rest, 1n+k, R.cons_some(A, old, acc), t2, y, hd, fill_next(d, k, SC.length(A, rest), hk), AR.upd_perfect(Maybe<&2, A>, d, t, kk, Some{x}, pf)))

# the count of tfill: slots and kept elements hold the old slots, old, acc
# and xs
def tfill_occ(~A: Data, ~V: Data, ~rel: A -> V -> Bool, +v: V, +d: Nat, +xs: List<&2, A>, +k: Nat, +acc: List<&2, A>, +t: AR.Tree<Maybe<&2, A>>, +old: Maybe<&2, A>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hk: {Nat.is_le(Nat.add(k, SC.length(A, xs)), SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}) -> {Nat.add(AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, AR.slots(Maybe<&2, A>, R.fst(AR.Tree<Maybe<&2, A>>, List<&2, A>, tfill(~A, d, xs, k, t, acc, old)))), AS.occ(~A, ~V, ~rel, v, R.snd(AR.Tree<Maybe<&2, A>>, List<&2, A>, tfill(~A, d, xs, k, t, acc, old)))) == Nat.add(AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, AR.slots(Maybe<&2, A>, t)), Nat.add(SR.b2n(mrel(~A, ~V, ~rel, old, v)), Nat.add(AS.occ(~A, ~V, ~rel, v, acc), AS.occ(~A, ~V, ~rel, v, xs)))) : Nat}:
  match xs:
    case Nil{}:
      +e = Equal.trans(Nat, AS.occ(~A, ~V, ~rel, v, R.cons_some(A, old, acc)), Nat.add(SR.b2n(mrel(~A, ~V, ~rel, old, v)), AS.occ(~A, ~V, ~rel, v, acc)), Nat.add(SR.b2n(mrel(~A, ~V, ~rel, old, v)), Nat.add(AS.occ(~A, ~V, ~rel, v, acc), 0n)),
        cons_some_occ(~A, ~V, ~rel, v, old, acc),
        Equal.cong(Nat, Nat, z => Nat.add(SR.b2n(mrel(~A, ~V, ~rel, old, v)), z), AS.occ(~A, ~V, ~rel, v, acc), Nat.add(AS.occ(~A, ~V, ~rel, v, acc), 0n), Equal.sym(Nat, Nat.add(AS.occ(~A, ~V, ~rel, v, acc), 0n), AS.occ(~A, ~V, ~rel, v, acc), N.add_zero(AS.occ(~A, ~V, ~rel, v, acc)))))
      Equal.cong(Nat, Nat, z => Nat.add(AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, AR.slots(Maybe<&2, A>, t)), z), AS.occ(~A, ~V, ~rel, v, R.cons_some(A, old, acc)), Nat.add(SR.b2n(mrel(~A, ~V, ~rel, old, v)), Nat.add(AS.occ(~A, ~V, ~rel, v, acc), 0n)), e)
    case Con{+x, +rest}:
      +kk = U32.to_nat(U32.from_nat(k))
      +y = AS.at(Maybe<&2, A>, t, kk)
      +t2 = AR.upd(Maybe<&2, A>, d, t, kk, Some{x})
      +hkk = AS.idx_i(d, k, hd, fill_bounds(d, k, SC.length(A, rest), hk))
      +acc2 = R.cons_some(A, old, acc)
      +M = AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, AR.slots(Maybe<&2, A>, t))
      +P = AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, AR.slots(Maybe<&2, A>, t2))
      +X = SR.b2n(rel(x, v))
      +C = AS.occ(~A, ~V, ~rel, v, acc2)
      +Q = AS.occ(~A, ~V, ~rel, v, rest)
      +ih = tfill_occ(~A, ~V, ~rel, v, d, rest, 1n+k, acc2, t2, y, hd, fill_next(d, k, SC.length(A, rest), hk), AR.upd_perfect(Maybe<&2, A>, d, t, kk, Some{x}, pf))
      +hp = Equal.trans(Nat, Nat.add(P, SR.b2n(mrel(~A, ~V, ~rel, y, v))), Nat.add(AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, SC.update(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t), kk, Some{x})), SR.b2n(mrel(~A, ~V, ~rel, y, v))), Nat.add(M, X),
        Equal.cong(List<&2, Maybe<&2, A>>, Nat, z => Nat.add(AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, z), SR.b2n(mrel(~A, ~V, ~rel, y, v))), AR.slots(Maybe<&2, A>, t2), SC.update(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t), kk, Some{x}), AR.upd_slots(Maybe<&2, A>, d, t, kk, Some{x}, hkk, pf)),
        AS.put_occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, AR.slots(Maybe<&2, A>, t), kk, Some{x}, y, AS.at_nth(Maybe<&2, A>, d, t, kk, pf, hkk)))
      +hc = cons_some_occ(~A, ~V, ~rel, v, old, acc)
      Equal.trans(Nat, Nat.add(AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, AR.slots(Maybe<&2, A>, R.fst(AR.Tree<Maybe<&2, A>>, List<&2, A>, tfill(~A, d, rest, 1n+k, t2, acc2, y)))), AS.occ(~A, ~V, ~rel, v, R.snd(AR.Tree<Maybe<&2, A>>, List<&2, A>, tfill(~A, d, rest, 1n+k, t2, acc2, y)))), Nat.add(P, Nat.add(SR.b2n(mrel(~A, ~V, ~rel, y, v)), Nat.add(C, Q))), Nat.add(M, Nat.add(SR.b2n(mrel(~A, ~V, ~rel, old, v)), Nat.add(AS.occ(~A, ~V, ~rel, v, acc), Nat.add(X, Q)))),
        ih,
        Equal.trans(Nat, Nat.add(P, Nat.add(SR.b2n(mrel(~A, ~V, ~rel, y, v)), Nat.add(C, Q))), Nat.add(Nat.add(P, SR.b2n(mrel(~A, ~V, ~rel, y, v))), Nat.add(C, Q)), Nat.add(M, Nat.add(SR.b2n(mrel(~A, ~V, ~rel, old, v)), Nat.add(AS.occ(~A, ~V, ~rel, v, acc), Nat.add(X, Q)))),
          Equal.sym(Nat, Nat.add(Nat.add(P, SR.b2n(mrel(~A, ~V, ~rel, y, v))), Nat.add(C, Q)), Nat.add(P, Nat.add(SR.b2n(mrel(~A, ~V, ~rel, y, v)), Nat.add(C, Q))), N.add_assoc(P, SR.b2n(mrel(~A, ~V, ~rel, y, v)), Nat.add(C, Q))),
          Equal.trans(Nat, Nat.add(Nat.add(P, SR.b2n(mrel(~A, ~V, ~rel, y, v))), Nat.add(C, Q)), Nat.add(Nat.add(M, X), Nat.add(C, Q)), Nat.add(M, Nat.add(SR.b2n(mrel(~A, ~V, ~rel, old, v)), Nat.add(AS.occ(~A, ~V, ~rel, v, acc), Nat.add(X, Q)))),
            Equal.cong(Nat, Nat, z => Nat.add(z, Nat.add(C, Q)), Nat.add(P, SR.b2n(mrel(~A, ~V, ~rel, y, v))), Nat.add(M, X), hp),
            Equal.trans(Nat, Nat.add(Nat.add(M, X), Nat.add(C, Q)), Nat.add(M, Nat.add(C, Nat.add(X, Q))), Nat.add(M, Nat.add(SR.b2n(mrel(~A, ~V, ~rel, old, v)), Nat.add(AS.occ(~A, ~V, ~rel, v, acc), Nat.add(X, Q)))),
              rearr(M, X, C, Q),
              Equal.cong(Nat, Nat, z => Nat.add(M, z), Nat.add(C, Nat.add(X, Q)), Nat.add(SR.b2n(mrel(~A, ~V, ~rel, old, v)), Nat.add(AS.occ(~A, ~V, ~rel, v, acc), Nat.add(X, Q))),
                Equal.trans(Nat, Nat.add(C, Nat.add(X, Q)), Nat.add(Nat.add(SR.b2n(mrel(~A, ~V, ~rel, old, v)), AS.occ(~A, ~V, ~rel, v, acc)), Nat.add(X, Q)), Nat.add(SR.b2n(mrel(~A, ~V, ~rel, old, v)), Nat.add(AS.occ(~A, ~V, ~rel, v, acc), Nat.add(X, Q))),
                  Equal.cong(Nat, Nat, z => Nat.add(z, Nat.add(X, Q)), C, Nat.add(SR.b2n(mrel(~A, ~V, ~rel, old, v)), AS.occ(~A, ~V, ~rel, v, acc)), hc),
                  N.add_assoc(SR.b2n(mrel(~A, ~V, ~rel, old, v)), AS.occ(~A, ~V, ~rel, v, acc), Nat.add(X, Q))))))))

# ---- collect ----

def take_zero(~A: Data, ~V: Data, ~rel: A -> V -> Bool, +v: V, +xs: List<&2, Maybe<&2, A>>) -> {AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, SC.take(Maybe<&2, A>, xs, 0n)) == 0n : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

# the first p + 1 elements hold the first p and element p
def take_succ(~A: Data, ~V: Data, ~rel: A -> V -> Bool, +v: V, +xs: List<&2, Maybe<&2, A>>, +p: Nat, +x: Maybe<&2, A>, +h: {SC.nth(Maybe<&2, A>, xs, p) == Some{x} : Maybe<&2, Maybe<&2, A>>}) -> {AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, SC.take(Maybe<&2, A>, xs, 1n+p)) == Nat.add(AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, SC.take(Maybe<&2, A>, xs, p)), SR.b2n(mrel(~A, ~V, ~rel, x, v))) : Nat}:
  match xs p:
    case Nil{} _:
      Empty.absurd({0n == Nat.add(0n, SR.b2n(mrel(~A, ~V, ~rel, x, v))) : Nat}, SH.none_some(Maybe<&2, A>, x, h))
    case Con{+hd, +t} 0n:
      %SH.some_inj(Maybe<&2, A>, hd, x, h) : {Nat.add(SR.b2n(mrel(~A, ~V, ~rel, hd, v)), AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, SC.take(Maybe<&2, A>, t, 0n))) == Nat.add(0n, SR.b2n(mrel(~A, ~V, ~rel, _, v))) : Nat}
      %Equal.sym(Nat, AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, SC.take(Maybe<&2, A>, t, 0n)), 0n, take_zero(~A, ~V, ~rel, v, t)) : {Nat.add(SR.b2n(mrel(~A, ~V, ~rel, hd, v)), _) == Nat.add(0n, SR.b2n(mrel(~A, ~V, ~rel, hd, v))) : Nat}
      Equal.trans(Nat, Nat.add(SR.b2n(mrel(~A, ~V, ~rel, hd, v)), 0n), SR.b2n(mrel(~A, ~V, ~rel, hd, v)), Nat.add(0n, SR.b2n(mrel(~A, ~V, ~rel, hd, v))), N.add_zero(SR.b2n(mrel(~A, ~V, ~rel, hd, v))), Equal.sym(Nat, Nat.add(0n, SR.b2n(mrel(~A, ~V, ~rel, hd, v))), SR.b2n(mrel(~A, ~V, ~rel, hd, v)), zero_add(SR.b2n(mrel(~A, ~V, ~rel, hd, v)))))
    case Con{+hd, +t} 1n+q:
      Equal.trans(Nat, Nat.add(SR.b2n(mrel(~A, ~V, ~rel, hd, v)), AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, SC.take(Maybe<&2, A>, t, 1n+q))), Nat.add(SR.b2n(mrel(~A, ~V, ~rel, hd, v)), Nat.add(AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, SC.take(Maybe<&2, A>, t, q)), SR.b2n(mrel(~A, ~V, ~rel, x, v)))), Nat.add(Nat.add(SR.b2n(mrel(~A, ~V, ~rel, hd, v)), AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, SC.take(Maybe<&2, A>, t, q))), SR.b2n(mrel(~A, ~V, ~rel, x, v))),
        Equal.cong(Nat, Nat, z => Nat.add(SR.b2n(mrel(~A, ~V, ~rel, hd, v)), z), AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, SC.take(Maybe<&2, A>, t, 1n+q)), Nat.add(AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, SC.take(Maybe<&2, A>, t, q)), SR.b2n(mrel(~A, ~V, ~rel, x, v))), take_succ(~A, ~V, ~rel, v, t, q, x, h)),
        Equal.sym(Nat, Nat.add(Nat.add(SR.b2n(mrel(~A, ~V, ~rel, hd, v)), AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, SC.take(Maybe<&2, A>, t, q))), SR.b2n(mrel(~A, ~V, ~rel, x, v))), Nat.add(SR.b2n(mrel(~A, ~V, ~rel, hd, v)), Nat.add(AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, SC.take(Maybe<&2, A>, t, q)), SR.b2n(mrel(~A, ~V, ~rel, x, v)))), N.add_assoc(SR.b2n(mrel(~A, ~V, ~rel, hd, v)), AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, SC.take(Maybe<&2, A>, t, q)), SR.b2n(mrel(~A, ~V, ~rel, x, v)))))

# collect of slots k - 1, ..., 0: the first k slots, m and acc
def collect_occ(~A: Data, ~V: Data, ~rel: A -> V -> Bool, +v: V, +d: Nat, +k: Nat, +acc: List<&2, A>, +t: AR.Tree<Maybe<&2, A>>, +m: Maybe<&2, A>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hk: {Nat.is_le(k, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}) -> {AS.occ(~A, ~V, ~rel, v, R.collect(~A, k, acc, (AR.thaw(Maybe<&2, A>, t), m))) == Nat.add(AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, SC.take(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t), k)), Nat.add(SR.b2n(mrel(~A, ~V, ~rel, m, v)), AS.occ(~A, ~V, ~rel, v, acc))) : Nat}:
  match k:
    case 0n:
      %Equal.sym(Nat, AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, SC.take(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t), 0n)), 0n, take_zero(~A, ~V, ~rel, v, AR.slots(Maybe<&2, A>, t))) : {AS.occ(~A, ~V, ~rel, v, R.cons_some(A, m, acc)) == Nat.add(_, Nat.add(SR.b2n(mrel(~A, ~V, ~rel, m, v)), AS.occ(~A, ~V, ~rel, v, acc))) : Nat}
      Equal.trans(Nat, AS.occ(~A, ~V, ~rel, v, R.cons_some(A, m, acc)), Nat.add(SR.b2n(mrel(~A, ~V, ~rel, m, v)), AS.occ(~A, ~V, ~rel, v, acc)), Nat.add(0n, Nat.add(SR.b2n(mrel(~A, ~V, ~rel, m, v)), AS.occ(~A, ~V, ~rel, v, acc))), cons_some_occ(~A, ~V, ~rel, v, m, acc), Equal.sym(Nat, Nat.add(0n, Nat.add(SR.b2n(mrel(~A, ~V, ~rel, m, v)), AS.occ(~A, ~V, ~rel, v, acc))), Nat.add(SR.b2n(mrel(~A, ~V, ~rel, m, v)), AS.occ(~A, ~V, ~rel, v, acc)), zero_add(Nat.add(SR.b2n(mrel(~A, ~V, ~rel, m, v)), AS.occ(~A, ~V, ~rel, v, acc)))))
    case 1n+ +p:
      +hp = N.succ_le_lt(p, SC.pow2(d), hk)
      +pp = U32.to_nat(U32.from_nat(p))
      +epp = U.to_nat_from_nat(p, d, N.lt_le(d, 32n, hd), hp)
      +y = AS.at(Maybe<&2, A>, t, pp)
      +hpp = AS.idx_i(d, p, hd, hp)
      +acc2 = R.cons_some(A, m, acc)
      +T = AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, SC.take(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t), p))
      +e1 = Equal.cong(Array<Maybe<&2, A>> & Maybe<&2, A>, List<&2, A>, z => R.collect(~A, p, acc2, z), Array.get(Maybe<&2, A>, AR.thaw(Maybe<&2, A>, t), U32.from_nat(p)), (AR.thaw(Maybe<&2, A>, t), y),
        AR.get(Maybe<&2, A>, d, t, U32.from_nat(p), y, hd, hpp, AS.at_nth(Maybe<&2, A>, d, t, pp, pf, hpp), pf))
      +ih = collect_occ(~A, ~V, ~rel, v, d, p, acc2, t, y, hd, N.lt_le(p, SC.pow2(d), hp), pf)
      +hn = L.subst(Nat, z => {SC.nth(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t), z) == Some{y} : Maybe<&2, Maybe<&2, A>>}, pp, p, epp, AS.at_nth(Maybe<&2, A>, d, t, pp, pf, hpp))
      +ts = take_succ(~A, ~V, ~rel, v, AR.slots(Maybe<&2, A>, t), p, y, hn)
      +hc = cons_some_occ(~A, ~V, ~rel, v, m, acc)
      Equal.trans(Nat, AS.occ(~A, ~V, ~rel, v, R.collect(~A, 1n+p, acc, (AR.thaw(Maybe<&2, A>, t), m))), Nat.add(T, Nat.add(SR.b2n(mrel(~A, ~V, ~rel, y, v)), AS.occ(~A, ~V, ~rel, v, acc2))), Nat.add(AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, SC.take(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t), 1n+p)), Nat.add(SR.b2n(mrel(~A, ~V, ~rel, m, v)), AS.occ(~A, ~V, ~rel, v, acc))),
        Equal.trans(Nat, AS.occ(~A, ~V, ~rel, v, R.collect(~A, 1n+p, acc, (AR.thaw(Maybe<&2, A>, t), m))), AS.occ(~A, ~V, ~rel, v, R.collect(~A, p, acc2, (AR.thaw(Maybe<&2, A>, t), y))), Nat.add(T, Nat.add(SR.b2n(mrel(~A, ~V, ~rel, y, v)), AS.occ(~A, ~V, ~rel, v, acc2))),
          Equal.cong(List<&2, A>, Nat, z => AS.occ(~A, ~V, ~rel, v, z), R.collect(~A, 1n+p, acc, (AR.thaw(Maybe<&2, A>, t), m)), R.collect(~A, p, acc2, (AR.thaw(Maybe<&2, A>, t), y)), e1),
          ih),
        Equal.trans(Nat, Nat.add(T, Nat.add(SR.b2n(mrel(~A, ~V, ~rel, y, v)), AS.occ(~A, ~V, ~rel, v, acc2))), Nat.add(Nat.add(T, SR.b2n(mrel(~A, ~V, ~rel, y, v))), AS.occ(~A, ~V, ~rel, v, acc2)), Nat.add(AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, SC.take(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t), 1n+p)), Nat.add(SR.b2n(mrel(~A, ~V, ~rel, m, v)), AS.occ(~A, ~V, ~rel, v, acc))),
          Equal.sym(Nat, Nat.add(Nat.add(T, SR.b2n(mrel(~A, ~V, ~rel, y, v))), AS.occ(~A, ~V, ~rel, v, acc2)), Nat.add(T, Nat.add(SR.b2n(mrel(~A, ~V, ~rel, y, v)), AS.occ(~A, ~V, ~rel, v, acc2))), N.add_assoc(T, SR.b2n(mrel(~A, ~V, ~rel, y, v)), AS.occ(~A, ~V, ~rel, v, acc2))),
          Equal.trans(Nat, Nat.add(Nat.add(T, SR.b2n(mrel(~A, ~V, ~rel, y, v))), AS.occ(~A, ~V, ~rel, v, acc2)), Nat.add(AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, SC.take(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t), 1n+p)), AS.occ(~A, ~V, ~rel, v, acc2)), Nat.add(AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, SC.take(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t), 1n+p)), Nat.add(SR.b2n(mrel(~A, ~V, ~rel, m, v)), AS.occ(~A, ~V, ~rel, v, acc))),
            Equal.cong(Nat, Nat, z => Nat.add(z, AS.occ(~A, ~V, ~rel, v, acc2)), Nat.add(T, SR.b2n(mrel(~A, ~V, ~rel, y, v))), AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, SC.take(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t), 1n+p)), Equal.sym(Nat, AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, SC.take(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t), 1n+p)), Nat.add(T, SR.b2n(mrel(~A, ~V, ~rel, y, v))), ts)),
            Equal.cong(Nat, Nat, z => Nat.add(AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, SC.take(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t), 1n+p)), z), AS.occ(~A, ~V, ~rel, v, acc2), Nat.add(SR.b2n(mrel(~A, ~V, ~rel, m, v)), AS.occ(~A, ~V, ~rel, v, acc)), hc))))

# reading all 2^d slots: every slot's element, then acc
def collect_all(~A: Data, ~V: Data, ~rel: A -> V -> Bool, +v: V, +d: Nat, +acc: List<&2, A>, +t: AR.Tree<Maybe<&2, A>>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, d, t) == True{} : Bool}) -> {AS.occ(~A, ~V, ~rel, v, R.collect(~A, R.pow2n(d), acc, (AR.thaw(Maybe<&2, A>, t), None{}))) == Nat.add(AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, AR.slots(Maybe<&2, A>, t)), AS.occ(~A, ~V, ~rel, v, acc)) : Nat}:
  +et = Equal.trans(List<&2, Maybe<&2, A>>, SC.take(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t), SC.pow2(d)), SC.take(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t), SC.length(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t))), AR.slots(Maybe<&2, A>, t),
    Equal.cong(Nat, List<&2, Maybe<&2, A>>, z => SC.take(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t), z), SC.pow2(d), SC.length(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t)), Equal.sym(Nat, SC.length(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t)), SC.pow2(d), AR.slots_length(Maybe<&2, A>, d, t, pf))),
    AE.take_len(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t)))
  %Equal.sym(Nat, R.pow2n(d), SC.pow2(d), pow2n_eq(d)) : {AS.occ(~A, ~V, ~rel, v, R.collect(~A, _, acc, (AR.thaw(Maybe<&2, A>, t), None{}))) == Nat.add(AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, AR.slots(Maybe<&2, A>, t)), AS.occ(~A, ~V, ~rel, v, acc)) : Nat}
  Equal.trans(Nat, AS.occ(~A, ~V, ~rel, v, R.collect(~A, SC.pow2(d), acc, (AR.thaw(Maybe<&2, A>, t), None{}))), Nat.add(AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, SC.take(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t), SC.pow2(d))), Nat.add(0n, AS.occ(~A, ~V, ~rel, v, acc))), Nat.add(AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, AR.slots(Maybe<&2, A>, t)), AS.occ(~A, ~V, ~rel, v, acc)),
    collect_occ(~A, ~V, ~rel, v, d, SC.pow2(d), acc, t, None{}, hd, N.le_refl(SC.pow2(d)), pf),
    Equal.trans(Nat, Nat.add(AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, SC.take(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t), SC.pow2(d))), Nat.add(0n, AS.occ(~A, ~V, ~rel, v, acc))), Nat.add(AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, AR.slots(Maybe<&2, A>, t)), Nat.add(0n, AS.occ(~A, ~V, ~rel, v, acc))), Nat.add(AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, AR.slots(Maybe<&2, A>, t)), AS.occ(~A, ~V, ~rel, v, acc)),
      Equal.cong(List<&2, Maybe<&2, A>>, Nat, z => Nat.add(AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, z), Nat.add(0n, AS.occ(~A, ~V, ~rel, v, acc))), SC.take(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t), SC.pow2(d)), AR.slots(Maybe<&2, A>, t), et),
      Equal.cong(Nat, Nat, z => Nat.add(AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, AR.slots(Maybe<&2, A>, t)), z), Nat.add(0n, AS.occ(~A, ~V, ~rel, v, acc)), AS.occ(~A, ~V, ~rel, v, acc), zero_add(AS.occ(~A, ~V, ~rel, v, acc)))))

# ---- the shuffle ----

def len_eq(-A: Data, +xs: List<&2, A>) -> {List.length(&2, A, xs) == SC.length(A, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, +t}:
      N.succ_cong(List.length(&2, A, t), SC.length(A, t), len_eq(A, t))

def tthaw_eta(-A: Data, -S: Data, p: AR.Tree<A> & S) -> {AS.tthaw(A, S, p) == (AR.thaw(A, R.fst(AR.Tree<A>, S, p)), R.snd(AR.Tree<A>, S, p)) : Array<A> & S}:
  match p:
    case Tuple{+t, +s}:
      {==}

# the array path: n = length xs <= 2^d, d < 32
def arr_perm(~A: Data, ~V: Data, ~rel: A -> V -> Bool, ~S: Data, ~next: S -> W.U64 & S, +s: S, +xs: List<&2, A>, +n: Nat, +d: Nat, +v: V, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hn: {Nat.is_le(n, SC.pow2(d)) == True{} : Bool}, +hl: {SC.length(A, xs) == n : Nat}) -> {AS.occ(~A, ~V, ~rel, v, R.fst(List<&2, A>, S, R.shuffle_pick(~A, ~S, ~next, s, xs, n, d, True{}))) == AS.occ(~A, ~V, ~rel, v, xs) : Nat}:
  +t0 = AR.trep(Maybe<&2, A>, d, None{})
  +pf0 = AR.trep_perfect(Maybe<&2, A>, d, None{})
  +hk = L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, n, Nat.add(0n, SC.length(A, xs)),
    Equal.trans(Nat, n, SC.length(A, xs), Nat.add(0n, SC.length(A, xs)), Equal.sym(Nat, SC.length(A, xs), n, hl), Equal.sym(Nat, Nat.add(0n, SC.length(A, xs)), SC.length(A, xs), zero_add(SC.length(A, xs)))),
    hn)
  +TF = R.fst(AR.Tree<Maybe<&2, A>>, List<&2, A>, tfill(~A, d, xs, 0n, t0, [], None{}))
  +AF = R.snd(AR.Tree<Maybe<&2, A>>, List<&2, A>, tfill(~A, d, xs, 0n, t0, [], None{}))
  +pfF = tfill_perfect(~A, d, xs, 0n, t0, [], None{}, pf0)
  +GF = R.fst(AR.Tree<Maybe<&2, A>>, S, AS.tgo(~Maybe<&2, A>, ~S, ~next, d, Nat.sub(n, 1n), TF, s))
  +GS = R.snd(AR.Tree<Maybe<&2, A>>, S, AS.tgo(~Maybe<&2, A>, ~S, ~next, d, Nat.sub(n, 1n), TF, s))
  +q1 = Equal.cong(Array<Maybe<&2, A>>, List<&2, A> & S, z => R.shuffle_arr(~A, ~S, ~next, s, n, d, R.fill(~A, xs, 0n, [], (z, None{}))), Array.new(Maybe<&2, A>, d, None{}), AR.thaw(Maybe<&2, A>, t0), AR.new(Maybe<&2, A>, d, None{}))
  +q2 = Equal.cong(Array<Maybe<&2, A>> & List<&2, A>, List<&2, A> & S, z => R.shuffle_arr(~A, ~S, ~next, s, n, d, z), R.fill(~A, xs, 0n, [], (AR.thaw(Maybe<&2, A>, t0), None{})), AS.tthaw(Maybe<&2, A>, List<&2, A>, tfill(~A, d, xs, 0n, t0, [], None{})), fill_mirror(~A, d, xs, 0n, [], t0, None{}, hd, hk, pf0))
  +q3 = Equal.cong(Array<Maybe<&2, A>> & List<&2, A>, List<&2, A> & S, z => R.shuffle_arr(~A, ~S, ~next, s, n, d, z), AS.tthaw(Maybe<&2, A>, List<&2, A>, tfill(~A, d, xs, 0n, t0, [], None{})), (AR.thaw(Maybe<&2, A>, TF), AF), tthaw_eta(Maybe<&2, A>, List<&2, A>, tfill(~A, d, xs, 0n, t0, [], None{})))
  +q4 = Equal.cong(Array<Maybe<&2, A>> & S, List<&2, A> & S, z => R.collect_fin(~A, S, d, AF, z), R.shuffle_array(~Maybe<&2, A>, ~S, ~next, s, AR.thaw(Maybe<&2, A>, TF), n), AS.tthaw(Maybe<&2, A>, S, AS.tgo(~Maybe<&2, A>, ~S, ~next, d, Nat.sub(n, 1n), TF, s)), AS.array_mirror(~Maybe<&2, A>, ~S, ~next, s, d, TF, n, hd, hn, pfF))
  +q5 = Equal.cong(Array<Maybe<&2, A>> & S, List<&2, A> & S, z => R.collect_fin(~A, S, d, AF, z), AS.tthaw(Maybe<&2, A>, S, AS.tgo(~Maybe<&2, A>, ~S, ~next, d, Nat.sub(n, 1n), TF, s)), (AR.thaw(Maybe<&2, A>, GF), GS), tthaw_eta(Maybe<&2, A>, S, AS.tgo(~Maybe<&2, A>, ~S, ~next, d, Nat.sub(n, 1n), TF, s)))
  +qa = Equal.trans(List<&2, A> & S, R.shuffle_pick(~A, ~S, ~next, s, xs, n, d, True{}), R.collect_fin(~A, S, d, AF, AS.tthaw(Maybe<&2, A>, S, AS.tgo(~Maybe<&2, A>, ~S, ~next, d, Nat.sub(n, 1n), TF, s))), R.collect_fin(~A, S, d, AF, (AR.thaw(Maybe<&2, A>, GF), GS)),
    Equal.trans(List<&2, A> & S, R.shuffle_pick(~A, ~S, ~next, s, xs, n, d, True{}), R.shuffle_arr(~A, ~S, ~next, s, n, d, (AR.thaw(Maybe<&2, A>, TF), AF)), R.collect_fin(~A, S, d, AF, AS.tthaw(Maybe<&2, A>, S, AS.tgo(~Maybe<&2, A>, ~S, ~next, d, Nat.sub(n, 1n), TF, s))),
      Equal.trans(List<&2, A> & S, R.shuffle_pick(~A, ~S, ~next, s, xs, n, d, True{}), R.shuffle_arr(~A, ~S, ~next, s, n, d, AS.tthaw(Maybe<&2, A>, List<&2, A>, tfill(~A, d, xs, 0n, t0, [], None{}))), R.shuffle_arr(~A, ~S, ~next, s, n, d, (AR.thaw(Maybe<&2, A>, TF), AF)), Equal.trans(List<&2, A> & S, R.shuffle_pick(~A, ~S, ~next, s, xs, n, d, True{}), R.shuffle_arr(~A, ~S, ~next, s, n, d, R.fill(~A, xs, 0n, [], (AR.thaw(Maybe<&2, A>, t0), None{}))), R.shuffle_arr(~A, ~S, ~next, s, n, d, AS.tthaw(Maybe<&2, A>, List<&2, A>, tfill(~A, d, xs, 0n, t0, [], None{}))), q1, q2), q3),
      q4),
    q5)
  +c1 = Equal.cong(List<&2, A> & S, Nat, z => AS.occ(~A, ~V, ~rel, v, R.fst(List<&2, A>, S, z)), R.shuffle_pick(~A, ~S, ~next, s, xs, n, d, True{}), R.collect_fin(~A, S, d, AF, (AR.thaw(Maybe<&2, A>, GF), GS)), qa)
  +c2 = collect_all(~A, ~V, ~rel, v, d, AF, GF, hd, AS.tgo_perfect(~Maybe<&2, A>, ~S, ~next, d, Nat.sub(n, 1n), TF, s, pfF))
  +c3 = AS.tgo_occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), ~S, ~next, v, d, Nat.sub(n, 1n), TF, s, hd, AS.pred_lt(n, SC.pow2(d), hn, N.pow2_pos(d)), pfF)
  +c4 = tfill_occ(~A, ~V, ~rel, v, d, xs, 0n, [], t0, None{}, hd, hk, pf0)
  +z0 = Equal.trans(Nat, AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, AR.slots(Maybe<&2, A>, t0)), AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, SC.replicate(Maybe<&2, A>, SC.pow2(d), None{})), 0n,
    Equal.cong(List<&2, Maybe<&2, A>>, Nat, z => AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, z), AR.slots(Maybe<&2, A>, t0), SC.replicate(Maybe<&2, A>, SC.pow2(d), None{}), AR.trep_slots(Maybe<&2, A>, d, None{})),
    repl_none(~A, ~V, ~rel, v, SC.pow2(d)))
  +z1 = Equal.trans(Nat, Nat.add(AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, AR.slots(Maybe<&2, A>, t0)), Nat.add(0n, Nat.add(0n, AS.occ(~A, ~V, ~rel, v, xs)))), Nat.add(0n, Nat.add(0n, Nat.add(0n, AS.occ(~A, ~V, ~rel, v, xs)))), AS.occ(~A, ~V, ~rel, v, xs),
    Equal.cong(Nat, Nat, z => Nat.add(z, Nat.add(0n, Nat.add(0n, AS.occ(~A, ~V, ~rel, v, xs)))), AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, AR.slots(Maybe<&2, A>, t0)), 0n, z0),
    Equal.trans(Nat, Nat.add(0n, Nat.add(0n, Nat.add(0n, AS.occ(~A, ~V, ~rel, v, xs)))), Nat.add(0n, Nat.add(0n, AS.occ(~A, ~V, ~rel, v, xs))), AS.occ(~A, ~V, ~rel, v, xs), zero_add(Nat.add(0n, Nat.add(0n, AS.occ(~A, ~V, ~rel, v, xs)))),
      Equal.trans(Nat, Nat.add(0n, Nat.add(0n, AS.occ(~A, ~V, ~rel, v, xs))), Nat.add(0n, AS.occ(~A, ~V, ~rel, v, xs)), AS.occ(~A, ~V, ~rel, v, xs), zero_add(Nat.add(0n, AS.occ(~A, ~V, ~rel, v, xs))), zero_add(AS.occ(~A, ~V, ~rel, v, xs)))))
  Equal.trans(Nat, AS.occ(~A, ~V, ~rel, v, R.fst(List<&2, A>, S, R.shuffle_pick(~A, ~S, ~next, s, xs, n, d, True{}))), AS.occ(~A, ~V, ~rel, v, R.collect(~A, R.pow2n(d), AF, (AR.thaw(Maybe<&2, A>, GF), None{}))), AS.occ(~A, ~V, ~rel, v, xs),
    c1,
    Equal.trans(Nat, AS.occ(~A, ~V, ~rel, v, R.collect(~A, R.pow2n(d), AF, (AR.thaw(Maybe<&2, A>, GF), None{}))), Nat.add(AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, AR.slots(Maybe<&2, A>, GF)), AS.occ(~A, ~V, ~rel, v, AF)), AS.occ(~A, ~V, ~rel, v, xs),
      c2,
      Equal.trans(Nat, Nat.add(AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, AR.slots(Maybe<&2, A>, GF)), AS.occ(~A, ~V, ~rel, v, AF)), Nat.add(AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, AR.slots(Maybe<&2, A>, TF)), AS.occ(~A, ~V, ~rel, v, AF)), AS.occ(~A, ~V, ~rel, v, xs),
        Equal.cong(Nat, Nat, z => Nat.add(z, AS.occ(~A, ~V, ~rel, v, AF)), AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, AR.slots(Maybe<&2, A>, GF)), AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, AR.slots(Maybe<&2, A>, TF)), c3),
        Equal.trans(Nat, Nat.add(AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, AR.slots(Maybe<&2, A>, TF)), AS.occ(~A, ~V, ~rel, v, AF)), Nat.add(AS.occ(~Maybe<&2, A>, ~V, ~(m => w => mrel(~A, ~V, ~rel, m, w)), v, AR.slots(Maybe<&2, A>, t0)), Nat.add(0n, Nat.add(0n, AS.occ(~A, ~V, ~rel, v, xs)))), AS.occ(~A, ~V, ~rel, v, xs), c4, z1))))

def pick_perm(~A: Data, ~V: Data, ~rel: A -> V -> Bool, ~S: Data, ~next: S -> W.U64 & S, +s: S, +xs: List<&2, A>, +n: Nat, +d: Nat, +v: V, +b: Bool, +hb: {Bool.and(Nat.is_lt(d, 32n), Nat.is_le(n, R.pow2n(d))) == b : Bool}, +hl: {List.length(&2, A, xs) == n : Nat}) -> {AS.occ(~A, ~V, ~rel, v, R.fst(List<&2, A>, S, R.shuffle_pick(~A, ~S, ~next, s, xs, n, d, b))) == AS.occ(~A, ~V, ~rel, v, xs) : Nat}:
  match b:
    case True{}:
      +hn = L.subst(Nat, z => {Nat.is_le(n, z) == True{} : Bool}, R.pow2n(d), SC.pow2(d), pow2n_eq(d), L.and_right(Nat.is_lt(d, 32n), Nat.is_le(n, R.pow2n(d)), hb))
      arr_perm(~A, ~V, ~rel, ~S, ~next, s, xs, n, d, v, L.and_left(Nat.is_lt(d, 32n), Nat.is_le(n, R.pow2n(d)), hb), hn, Equal.trans(Nat, SC.length(A, xs), List.length(&2, A, xs), n, Equal.sym(Nat, List.length(&2, A, xs), SC.length(A, xs), len_eq(A, xs)), hl))
    case False{}:
      SH.shuffle_list_perm(~A, ~V, ~rel, ~S, ~next, s, xs, v)

# THEOREM (Shuffle.permutation)
def shuffle_perm(~A: Data, ~V: Data, ~rel: A -> V -> Bool, ~S: Data, ~next: S -> W.U64 & S, +s: S, +xs: List<&2, A>, +v: V) -> {SR.occurrences(~A, ~V, ~rel, v, R.fst(List<&2, A>, S, R.shuffle(~A, ~S, ~next, s, xs))) == SR.occurrences(~A, ~V, ~rel, v, xs) : Nat}:
  +n = List.length(&2, A, xs)
  +d = R.depth(List.length(&2, A, xs))
  pick_perm(~A, ~V, ~rel, ~S, ~next, s, xs, n, d, v, Bool.and(Nat.is_lt(d, 32n), Nat.is_le(n, R.pow2n(d))), {==}, {==})

# THEOREM (Perm.permutation)
def perm_perm(~S: Data, ~next: S -> W.U64 & S, +s: S, +n: Nat, +i: Nat) -> {SR.occurrences(~Nat, ~Nat, ~Nat.is_eq, i, R.fst(List<&2, Nat>, S, R.perm(~S, ~next, s, n))) == SR.b2n(Nat.is_lt(i, n)) : Nat}:
  Equal.trans(Nat, SR.occurrences(~Nat, ~Nat, ~Nat.is_eq, i, R.fst(List<&2, Nat>, S, R.shuffle(~Nat, ~S, ~next, s, R.range(n)))), SR.occurrences(~Nat, ~Nat, ~Nat.is_eq, i, R.range(n)), SR.b2n(Nat.is_lt(i, n)),
    shuffle_perm(~Nat, ~Nat, ~Nat.is_eq, ~S, ~next, s, R.range(n), i),
    SH.range_occ(n, [], i))
