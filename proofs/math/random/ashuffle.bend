import Base
import ../../../src/math/u64.bend as W
import ../../../src/math/w64.bend as X
import ../../../src/math/random/rand.bend as R
import ../../../spec/math/w64.bend as SW
import ../../../spec/math/random/rand.bend as SR
import ../../../spec/lib/common.bend as SC
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/list.bend as LL
import ../../lib/u32.bend as U
import ../../lib/u32alg.bend as UA
import ../../lib/array.bend as AR
import ../typed/w64add.bend as WA
import ./bounded.bend as BD
import ./shuffle.bend as SH

# Fisher-Yates on an array (src/math/random/rand.bend shuffle_array, Go's
# Shuffle(n, swap) on a slice) permutes the array's contents, for every
# source: each exchange of slots i and j is a Base Array.get, Array.swap and
# Array.set, and proofs/lib/array.bend proves each of them on the array
# thaw(t) of a perfect mirror tree t (the array's slots are t's leaves). The
# exchanged indices are in range: i < n <= 2^d, and j < i + 1 because
# uint64n(i + 1) is below its bound (Uint64n.lt). The loop is mirrored on
# trees (tgo): the array after the loop is thaw of tgo's tree, whose slots
# hold every element as often as before (the count argument of shuffle.bend,
# over SC.update / SC.nth).

def occ(~A: Data, ~V: Data, ~rel: A -> V -> Bool, +v: V, +xs: List<&2, A>) -> Nat:
  SR.occurrences(~A, ~V, ~rel, v, xs)

# ---- the count argument on slot lists ----

# writing x over the element y at i: occ + [y] == old occ + [x]
def put_occ(~A: Data, ~V: Data, ~rel: A -> V -> Bool, +v: V, +xs: List<&2, A>, +i: Nat, +x: A, +y: A, +h: {SC.nth(A, xs, i) == Some{y} : Maybe<&2, A>}) -> {Nat.add(occ(~A, ~V, ~rel, v, SC.update(A, xs, i, x)), SR.b2n(rel(y, v))) == Nat.add(occ(~A, ~V, ~rel, v, xs), SR.b2n(rel(x, v))) : Nat}:
  match xs i:
    case Nil{} _:
      Empty.absurd({Nat.add(0n, SR.b2n(rel(y, v))) == Nat.add(0n, SR.b2n(rel(x, v))) : Nat}, SH.none_some(A, y, h))
    case Con{+hd, +t} 0n:
      %SH.some_inj(A, hd, y, h) : {Nat.add(Nat.add(SR.b2n(rel(x, v)), occ(~A, ~V, ~rel, v, t)), SR.b2n(rel(_, v))) == Nat.add(Nat.add(SR.b2n(rel(hd, v)), occ(~A, ~V, ~rel, v, t)), SR.b2n(rel(x, v))) : Nat}
      SH.swap_ends(SR.b2n(rel(x, v)), SR.b2n(rel(hd, v)), occ(~A, ~V, ~rel, v, t))
    case Con{+hd, +t} 1n+p:
      Equal.trans(Nat, Nat.add(Nat.add(SR.b2n(rel(hd, v)), occ(~A, ~V, ~rel, v, SC.update(A, t, p, x))), SR.b2n(rel(y, v))), Nat.add(SR.b2n(rel(hd, v)), Nat.add(occ(~A, ~V, ~rel, v, t), SR.b2n(rel(x, v)))), Nat.add(Nat.add(SR.b2n(rel(hd, v)), occ(~A, ~V, ~rel, v, t)), SR.b2n(rel(x, v))),
        SH.assoc3(SR.b2n(rel(hd, v)), occ(~A, ~V, ~rel, v, SC.update(A, t, p, x)), SR.b2n(rel(y, v)), Nat.add(occ(~A, ~V, ~rel, v, t), SR.b2n(rel(x, v))), put_occ(~A, ~V, ~rel, v, t, p, x, y, h)),
        Equal.sym(Nat, Nat.add(Nat.add(SR.b2n(rel(hd, v)), occ(~A, ~V, ~rel, v, t)), SR.b2n(rel(x, v))), Nat.add(SR.b2n(rel(hd, v)), Nat.add(occ(~A, ~V, ~rel, v, t), SR.b2n(rel(x, v)))), N.add_assoc(SR.b2n(rel(hd, v)), occ(~A, ~V, ~rel, v, t), SR.b2n(rel(x, v)))))

# writing y at i keeps an element y at j
def nth_upd(-A: Data, +xs: List<&2, A>, +i: Nat, +j: Nat, +y: A, +h: {SC.nth(A, xs, j) == Some{y} : Maybe<&2, A>}) -> {SC.nth(A, SC.update(A, xs, i, y), j) == Some{y} : Maybe<&2, A>}:
  match xs i j:
    case Nil{} _ _:
      Empty.absurd({SC.nth(A, SC.update(A, Nil{}, i, y), j) == Some{y} : Maybe<&2, A>}, SH.none_some(A, y, h))
    case Con{+hd, +t} 0n 0n:
      {==}
    case Con{+hd, +t} 0n 1n+q:
      h
    case Con{+hd, +t} 1n+r 0n:
      h
    case Con{+hd, +t} 1n+r 1n+q:
      nth_upd(A, t, r, q, y, h)

# x = xs[i], y = xs[j]: writing x at j, then y at i, keeps every count
def exch_list(~A: Data, ~V: Data, ~rel: A -> V -> Bool, +v: V, +xs: List<&2, A>, +i: Nat, +j: Nat, +x: A, +y: A, +hx: {SC.nth(A, xs, i) == Some{x} : Maybe<&2, A>}, +hy: {SC.nth(A, xs, j) == Some{y} : Maybe<&2, A>}) -> {occ(~A, ~V, ~rel, v, SC.update(A, SC.update(A, xs, j, x), i, y)) == occ(~A, ~V, ~rel, v, xs) : Nat}:
  +ys = SC.update(A, xs, j, x)
  UA.add_cancel_r(occ(~A, ~V, ~rel, v, SC.update(A, ys, i, y)), occ(~A, ~V, ~rel, v, xs), SR.b2n(rel(x, v)),
    Equal.trans(Nat, Nat.add(occ(~A, ~V, ~rel, v, SC.update(A, ys, i, y)), SR.b2n(rel(x, v))), Nat.add(occ(~A, ~V, ~rel, v, ys), SR.b2n(rel(y, v))), Nat.add(occ(~A, ~V, ~rel, v, xs), SR.b2n(rel(x, v))),
      put_occ(~A, ~V, ~rel, v, ys, i, y, x, nth_upd(A, xs, j, i, x, hx)),
      put_occ(~A, ~V, ~rel, v, xs, j, x, y, hy)))

# ---- slots of a perfect tree ----

def tfirst(-A: Data, t: AR.Tree<A>) -> A:
  match t:
    case AR.TLeaf{x}:
      x
    case AR.TNode{l, r}:
      tfirst(A, l)

# slot i of t (i below t's 2^d slots)
def at(-A: Data, +t: AR.Tree<A>, +i: Nat) -> A:
  SH.some_or(A, SC.nth(A, AR.slots(A, t), i), tfirst(A, t))

def pick_some(-A: Data, +xs: List<&2, A>, +i: Nat, +dft: A, +h: {Nat.is_lt(i, SC.length(A, xs)) == True{} : Bool}) -> {SC.nth(A, xs, i) == Some{SH.some_or(A, SC.nth(A, xs, i), dft)} : Maybe<&2, A>}:
  match xs i:
    case Nil{} _:
      Empty.absurd({SC.nth(A, Nil{}, i) == Some{SH.some_or(A, SC.nth(A, Nil{}, i), dft)} : Maybe<&2, A>}, N.lt_zero_absurd(i, h))
    case Con{+hd, +t} 0n:
      {==}
    case Con{+hd, +t} 1n+p:
      pick_some(A, t, p, dft, h)

def at_nth(-A: Data, +d: Nat, +t: AR.Tree<A>, +i: Nat, +pf: {AR.perfect(A, d, t) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}) -> {SC.nth(A, AR.slots(A, t), i) == Some{at(A, t, i)} : Maybe<&2, A>}:
  pick_some(A, AR.slots(A, t), i, tfirst(A, t),
    L.subst(Nat, z => {Nat.is_lt(i, z) == True{} : Bool}, SC.pow2(d), SC.length(A, AR.slots(A, t)), Equal.sym(Nat, SC.length(A, AR.slots(A, t)), SC.pow2(d), AR.slots_length(A, d, t, pf)), hi))

# ---- one exchange ----

# the tree after exchanging slots i and j
def exch_tree(-A: Data, +d: Nat, +t: AR.Tree<A>, +i: Nat, +j: Nat) -> AR.Tree<A>:
  AR.upd(A, d, AR.upd(A, d, t, j, at(A, t, i)), i, at(A, t, j))

def exch_perfect(-A: Data, +d: Nat, +t: AR.Tree<A>, +i: Nat, +j: Nat, +pf: {AR.perfect(A, d, t) == True{} : Bool}) -> {AR.perfect(A, d, exch_tree(A, d, t, i, j)) == True{} : Bool}:
  AR.upd_perfect(A, d, AR.upd(A, d, t, j, at(A, t, i)), i, at(A, t, j), AR.upd_perfect(A, d, t, j, at(A, t, i), pf))

def exch_occ(~A: Data, ~V: Data, ~rel: A -> V -> Bool, +v: V, +d: Nat, +t: AR.Tree<A>, +i: Nat, +j: Nat, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(A, d, t) == True{} : Bool}) -> {occ(~A, ~V, ~rel, v, AR.slots(A, exch_tree(A, d, t, i, j))) == occ(~A, ~V, ~rel, v, AR.slots(A, t)) : Nat}:
  +x = at(A, t, i)
  +y = at(A, t, j)
  +t2 = AR.upd(A, d, t, j, x)
  +pf2 = AR.upd_perfect(A, d, t, j, x, pf)
  +es = Equal.trans(List<&2, A>, AR.slots(A, AR.upd(A, d, t2, i, y)), SC.update(A, AR.slots(A, t2), i, y), SC.update(A, SC.update(A, AR.slots(A, t), j, x), i, y),
    AR.upd_slots(A, d, t2, i, y, hi, pf2),
    Equal.cong(List<&2, A>, List<&2, A>, z => SC.update(A, z, i, y), AR.slots(A, t2), SC.update(A, AR.slots(A, t), j, x), AR.upd_slots(A, d, t, j, x, hj, pf)))
  Equal.trans(Nat, occ(~A, ~V, ~rel, v, AR.slots(A, AR.upd(A, d, t2, i, y))), occ(~A, ~V, ~rel, v, SC.update(A, SC.update(A, AR.slots(A, t), j, x), i, y)), occ(~A, ~V, ~rel, v, AR.slots(A, t)),
    Equal.cong(List<&2, A>, Nat, z => occ(~A, ~V, ~rel, v, z), AR.slots(A, AR.upd(A, d, t2, i, y)), SC.update(A, SC.update(A, AR.slots(A, t), j, x), i, y), es),
    exch_list(~A, ~V, ~rel, v, AR.slots(A, t), i, j, x, y, at_nth(A, d, t, i, pf, hi), at_nth(A, d, t, j, pf, hj)))

# R.exch on thaw(t) is thaw of the exchanged tree (Base get, swap, set)
def exch_thaw(~A: Data, +d: Nat, +t: AR.Tree<A>, +i: U32, +j: U32, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), SC.pow2(d)) == True{} : Bool}, +hj: {Nat.is_lt(U32.to_nat(j), SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(A, d, t) == True{} : Bool}) -> {R.exch(~A, AR.thaw(A, t), i, j) == AR.thaw(A, exch_tree(A, d, t, U32.to_nat(i), U32.to_nat(j))) : Array<A>}:
  +x = at(A, t, U32.to_nat(i))
  +y = at(A, t, U32.to_nat(j))
  +t2 = AR.upd(A, d, t, U32.to_nat(j), x)
  +pf2 = AR.upd_perfect(A, d, t, U32.to_nat(j), x, pf)
  +e1 = Equal.cong(Array<A> & A, Array<A>, r => R.exch_put(~A, i, j, r), Array.get(A, AR.thaw(A, t), i), (AR.thaw(A, t), x), AR.get(A, d, t, i, x, hd, hi, at_nth(A, d, t, U32.to_nat(i), pf, hi), pf))
  +e2 = Equal.cong(Array<A> & A, Array<A>, r => R.exch_set(~A, i, r), Array.swap(A, AR.thaw(A, t), j, x), (AR.thaw(A, t2), y), AR.swap(A, d, t, j, x, y, hd, hj, at_nth(A, d, t, U32.to_nat(j), pf, hj), pf))
  +e3 = AR.set(A, d, t2, i, y, at(A, t2, U32.to_nat(i)), hd, hi, at_nth(A, d, t2, U32.to_nat(i), pf2, hi), pf2)
  Equal.trans(Array<A>, R.exch(~A, AR.thaw(A, t), i, j), R.exch_set(~A, i, (AR.thaw(A, t2), y)), AR.thaw(A, AR.upd(A, d, t2, U32.to_nat(i), y)),
    Equal.trans(Array<A>, R.exch(~A, AR.thaw(A, t), i, j), R.exch_put(~A, i, j, (AR.thaw(A, t), x)), R.exch_set(~A, i, (AR.thaw(A, t2), y)), e1, e2),
    e3)

# ---- the indices ----

def bnd(+i: Nat) -> W.U64:
  W.U64{U32.from_nat(1n+i), 0}

# i < 2^d, d < 32: the U32 of i is i
def idx_i(+d: Nat, +i: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}) -> {Nat.is_lt(U32.to_nat(U32.from_nat(i)), SC.pow2(d)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, i, U32.to_nat(U32.from_nat(i)), Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, U.to_nat_from_nat(i, d, N.lt_le(d, 32n, hd), hi)), hi)

# the bound i + 1 as a 64-bit word has value i + 1
def bnd_value(+d: Nat, +i: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}) -> {SW.value(bnd(i)) == 1n+i : Nat}:
  +h1 = N.le_lt_trans(1n+i, SC.pow2(d), SC.pow2(1n+d), N.lt_succ_le_succ(i, SC.pow2(d), hi), N.pow2_lt_succ(d))
  Equal.trans(Nat, SW.value(bnd(i)), U32.to_nat(U32.from_nat(1n+i)), 1n+i,
    N.add_zero(U32.to_nat(U32.from_nat(1n+i))),
    U.to_nat_from_nat(1n+i, 1n+d, N.lt_succ_le_succ(d, 32n, hd), h1))

def bnd_nz(+d: Nat, +i: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}) -> {X.is_zero(bnd(i)) == False{} : Bool}:
  Equal.trans(Bool, X.is_zero(bnd(i)), Nat.is_eq(SW.value(bnd(i)), 0n), False{},
    WA.is_zero_value(bnd(i)),
    Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), SW.value(bnd(i)), 1n+i, bnd_value(d, i, hd, hi)))

# the draw j = uint64n(i + 1) is below i + 1
def draw_lt(~S: Data, ~next: S -> W.U64 & S, +d: Nat, +i: Nat, +s: S, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}) -> {Nat.is_lt(SW.value(R.fst(W.U64, S, R.uint64n(~S, ~next, s, bnd(i)))), 1n+i) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(SW.value(R.fst(W.U64, S, R.uint64n(~S, ~next, s, bnd(i)))), z) == True{} : Bool}, SW.value(bnd(i)), 1n+i, bnd_value(d, i, hd, hi),
    BD.uint64n_lt(~S, ~next, s, bnd(i), bnd_nz(d, i, hd, hi)))

def lo_le(+j: W.U64) -> {Nat.is_le(U32.to_nat(X.lo(j)), SW.value(j)) == True{} : Bool}:
  match j:
    case W.U64{+l, +h}:
      N.le_add_right(U32.to_nat(l), SC.shift(32n, U32.to_nat(h)))

# j < i + 1 <= 2^d: the low word of j is in range
def idx_j(+d: Nat, +i: Nat, +j: W.U64, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hj: {Nat.is_lt(SW.value(j), 1n+i) == True{} : Bool}) -> {Nat.is_lt(U32.to_nat(X.lo(j)), SC.pow2(d)) == True{} : Bool}:
  N.lt_le_trans(U32.to_nat(X.lo(j)), 1n+i, SC.pow2(d),
    N.le_lt_trans(U32.to_nat(X.lo(j)), SW.value(j), 1n+i, lo_le(j), hj),
    N.lt_succ_le_succ(i, SC.pow2(d), hi))

# ---- the loop, mirrored on trees ----

# the draw for index i: j = uint64n(i + 1) and the advanced source
def dj(~S: Data, ~next: S -> W.U64 & S, +s: S, +i: Nat) -> W.U64:
  R.fst(W.U64, S, R.uint64n(~S, ~next, s, bnd(i)))

def ds(~S: Data, ~next: S -> W.U64 & S, +s: S, +i: Nat) -> S:
  R.snd(W.U64, S, R.uint64n(~S, ~next, s, bnd(i)))

def pair_eta(-S: Data, p: W.U64 & S) -> {p == (R.fst(W.U64, S, p), R.snd(W.U64, S, p)) : W.U64 & S}:
  match p:
    case Tuple{+j, +s}:
      {==}

def exch_at_thaw(~A: Data, -S: Data, +d: Nat, +t: AR.Tree<A>, +i: Nat, +j: W.U64, +s: S, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hj: {Nat.is_lt(SW.value(j), 1n+i) == True{} : Bool}, +pf: {AR.perfect(A, d, t) == True{} : Bool}) -> {R.exch_at(~A, S, AR.thaw(A, t), U32.from_nat(i), (j, s)) == (AR.thaw(A, exch_tree(A, d, t, U32.to_nat(U32.from_nat(i)), U32.to_nat(X.lo(j)))), s) : Array<A> & S}:
  Equal.cong(Array<A>, Array<A> & S, a => (a, s), R.exch(~A, AR.thaw(A, t), U32.from_nat(i), X.lo(j)), AR.thaw(A, exch_tree(A, d, t, U32.to_nat(U32.from_nat(i)), U32.to_nat(X.lo(j)))),
    exch_thaw(~A, d, t, U32.from_nat(i), X.lo(j), hd, idx_i(d, i, hd, hi), idx_j(d, i, j, hi, hj), pf))

# the exchanged tree of step i
def tstep(~A: Data, ~S: Data, ~next: S -> W.U64 & S, +d: Nat, +t: AR.Tree<A>, +s: S, +i: Nat) -> AR.Tree<A>:
  exch_tree(A, d, t, U32.to_nat(U32.from_nat(i)), U32.to_nat(X.lo(dj(~S, ~next, s, i))))

# the tree and source after the steps i = k, ..., 1
def tgo(~A: Data, ~S: Data, ~next: S -> W.U64 & S, +d: Nat, k: Nat, +t: AR.Tree<A>, +s: S) -> AR.Tree<A> & S:
  match k:
    case 0n:
      (t, s)
    case 1n+ +p:
      tgo(~A, ~S, ~next, d, p, tstep(~A, ~S, ~next, d, t, s, 1n+p), ds(~S, ~next, s, 1n+p))

def tthaw(-A: Data, -S: Data, p: AR.Tree<A> & S) -> Array<A> & S:
  (t, s) = p
  (AR.thaw(A, t), s)

def go_mirror(~A: Data, ~S: Data, ~next: S -> W.U64 & S, +d: Nat, +k: Nat, +t: AR.Tree<A>, +s: S, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hk: {Nat.is_lt(k, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(A, d, t) == True{} : Bool}) -> {R.ashuffle_go(~A, ~S, ~next, k, (AR.thaw(A, t), s)) == tthaw(A, S, tgo(~A, ~S, ~next, d, k, t, s)) : Array<A> & S}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      +i = {1n+p : Nat}
      +j = dj(~S, ~next, s, i)
      +s2 = ds(~S, ~next, s, i)
      +t2 = tstep(~A, ~S, ~next, d, t, s, i)
      +fi = U32.from_nat(i)
      +e0 = Equal.cong(W.U64 & S, Array<A> & S, z => R.ashuffle_go(~A, ~S, ~next, p, R.exch_at(~A, S, AR.thaw(A, t), fi, z)), R.uint64n(~S, ~next, s, bnd(i)), (j, s2), pair_eta(S, R.uint64n(~S, ~next, s, bnd(i))))
      +e1 = Equal.cong(Array<A> & S, Array<A> & S, z => R.ashuffle_go(~A, ~S, ~next, p, z), R.exch_at(~A, S, AR.thaw(A, t), fi, (j, s2)), (AR.thaw(A, t2), s2),
        exch_at_thaw(~A, S, d, t, i, j, s2, hd, hk, draw_lt(~S, ~next, d, i, s, hd, hk), pf))
      +e2 = go_mirror(~A, ~S, ~next, d, p, t2, s2, hd, N.lt_trans(p, i, SC.pow2(d), N.lt_succ(p), hk), exch_perfect(A, d, t, U32.to_nat(fi), U32.to_nat(X.lo(j)), pf))
      Equal.trans(Array<A> & S, R.ashuffle_go(~A, ~S, ~next, i, (AR.thaw(A, t), s)), R.ashuffle_go(~A, ~S, ~next, p, (AR.thaw(A, t2), s2)), tthaw(A, S, tgo(~A, ~S, ~next, d, p, t2, s2)),
        Equal.trans(Array<A> & S, R.ashuffle_go(~A, ~S, ~next, i, (AR.thaw(A, t), s)), R.ashuffle_go(~A, ~S, ~next, p, R.exch_at(~A, S, AR.thaw(A, t), fi, (j, s2))), R.ashuffle_go(~A, ~S, ~next, p, (AR.thaw(A, t2), s2)), e0, e1),
        e2)

def tgo_perfect(~A: Data, ~S: Data, ~next: S -> W.U64 & S, +d: Nat, +k: Nat, +t: AR.Tree<A>, +s: S, +pf: {AR.perfect(A, d, t) == True{} : Bool}) -> {AR.perfect(A, d, R.fst(AR.Tree<A>, S, tgo(~A, ~S, ~next, d, k, t, s))) == True{} : Bool}:
  match k:
    case 0n:
      pf
    case 1n+ +p:
      tgo_perfect(~A, ~S, ~next, d, p, tstep(~A, ~S, ~next, d, t, s, 1n+p), ds(~S, ~next, s, 1n+p),
        exch_perfect(A, d, t, U32.to_nat(U32.from_nat(1n+p)), U32.to_nat(X.lo(dj(~S, ~next, s, 1n+p))), pf))

def tgo_occ(~A: Data, ~V: Data, ~rel: A -> V -> Bool, ~S: Data, ~next: S -> W.U64 & S, +v: V, +d: Nat, +k: Nat, +t: AR.Tree<A>, +s: S, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hk: {Nat.is_lt(k, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(A, d, t) == True{} : Bool}) -> {occ(~A, ~V, ~rel, v, AR.slots(A, R.fst(AR.Tree<A>, S, tgo(~A, ~S, ~next, d, k, t, s)))) == occ(~A, ~V, ~rel, v, AR.slots(A, t)) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      +i = U32.to_nat(U32.from_nat(1n+p))
      +j = U32.to_nat(X.lo(dj(~S, ~next, s, 1n+p)))
      +t2 = tstep(~A, ~S, ~next, d, t, s, 1n+p)
      Equal.trans(Nat, occ(~A, ~V, ~rel, v, AR.slots(A, R.fst(AR.Tree<A>, S, tgo(~A, ~S, ~next, d, p, t2, ds(~S, ~next, s, 1n+p))))), occ(~A, ~V, ~rel, v, AR.slots(A, t2)), occ(~A, ~V, ~rel, v, AR.slots(A, t)),
        tgo_occ(~A, ~V, ~rel, ~S, ~next, v, d, p, t2, ds(~S, ~next, s, 1n+p), hd, N.lt_trans(p, 1n+p, SC.pow2(d), N.lt_succ(p), hk), exch_perfect(A, d, t, i, j, pf)),
        exch_occ(~A, ~V, ~rel, v, d, t, i, j, idx_i(d, 1n+p, hd, hk), idx_j(d, 1n+p, dj(~S, ~next, s, 1n+p), hk, draw_lt(~S, ~next, d, 1n+p, s, hd, hk)), pf))

# n <= m, 1 <= m: n - 1 < m
def pred_lt(+n: Nat, +m: Nat, +hn: {Nat.is_le(n, m) == True{} : Bool}, +hm: {Nat.is_le(1n, m) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(n, 1n), m) == True{} : Bool}:
  match n:
    case 0n:
      N.succ_le_lt(0n, m, hm)
    case 1n+q:
      %Equal.sym(Nat, Nat.sub(q, 0n), q, N.sub_zero(q)) : {Nat.is_lt(_, m) == True{} : Bool}
      N.lt_le_trans(q, 1n+q, m, N.lt_succ(q), hn)

# shuffle_array on thaw(t) is thaw of the mirrored loop
def array_mirror(~A: Data, ~S: Data, ~next: S -> W.U64 & S, +s: S, +d: Nat, +t: AR.Tree<A>, +n: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hn: {Nat.is_le(n, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(A, d, t) == True{} : Bool}) -> {R.shuffle_array(~A, ~S, ~next, s, AR.thaw(A, t), n) == tthaw(A, S, tgo(~A, ~S, ~next, d, Nat.sub(n, 1n), t, s)) : Array<A> & S}:
  go_mirror(~A, ~S, ~next, d, Nat.sub(n, 1n), t, s, hd, pred_lt(n, SC.pow2(d), hn, N.pow2_pos(d)), pf)

def afst_tthaw(-A: Data, -S: Data, p: AR.Tree<A> & S) -> {SR.afst(A, S, tthaw(A, S, p)) == AR.thaw(A, R.fst(AR.Tree<A>, S, p)) : Array<A>}:
  match p:
    case Tuple{t, s}:
      {==}

# THEOREM (Shuffle.array_permutation)
def array_perm(~A: Data, ~V: Data, ~rel: A -> V -> Bool, ~S: Data, ~next: S -> W.U64 & S, +s: S, +d: Nat, +t: AR.Tree<A>, +n: Nat, +v: V, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hn: {Nat.is_le(n, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(A, d, t) == True{} : Bool}) -> {SR.occurrences(~A, ~V, ~rel, v, AR.slots(A, AR.freeze(A, SR.afst(A, S, R.shuffle_array(~A, ~S, ~next, s, AR.thaw(A, t), n))))) == SR.occurrences(~A, ~V, ~rel, v, AR.slots(A, t)) : Nat}:
  +g1 = R.fst(AR.Tree<A>, S, tgo(~A, ~S, ~next, d, Nat.sub(n, 1n), t, s))
  +e1 = Equal.cong(Array<A> & S, Nat, z => occ(~A, ~V, ~rel, v, AR.slots(A, AR.freeze(A, SR.afst(A, S, z)))), R.shuffle_array(~A, ~S, ~next, s, AR.thaw(A, t), n), tthaw(A, S, tgo(~A, ~S, ~next, d, Nat.sub(n, 1n), t, s)), array_mirror(~A, ~S, ~next, s, d, t, n, hd, hn, pf))
  +e2 = Equal.cong(Array<A>, Nat, z => occ(~A, ~V, ~rel, v, AR.slots(A, AR.freeze(A, z))), SR.afst(A, S, tthaw(A, S, tgo(~A, ~S, ~next, d, Nat.sub(n, 1n), t, s))), AR.thaw(A, g1), afst_tthaw(A, S, tgo(~A, ~S, ~next, d, Nat.sub(n, 1n), t, s)))
  +e3 = Equal.cong(AR.Tree<A>, Nat, z => occ(~A, ~V, ~rel, v, AR.slots(A, z)), AR.freeze(A, AR.thaw(A, g1)), g1, AR.freeze_thaw(A, g1))
  +e4 = tgo_occ(~A, ~V, ~rel, ~S, ~next, v, d, Nat.sub(n, 1n), t, s, hd, pred_lt(n, SC.pow2(d), hn, N.pow2_pos(d)), pf)
  Equal.trans(Nat, occ(~A, ~V, ~rel, v, AR.slots(A, AR.freeze(A, SR.afst(A, S, R.shuffle_array(~A, ~S, ~next, s, AR.thaw(A, t), n))))), occ(~A, ~V, ~rel, v, AR.slots(A, AR.freeze(A, SR.afst(A, S, tthaw(A, S, tgo(~A, ~S, ~next, d, Nat.sub(n, 1n), t, s)))))), occ(~A, ~V, ~rel, v, AR.slots(A, t)),
    e1,
    Equal.trans(Nat, occ(~A, ~V, ~rel, v, AR.slots(A, AR.freeze(A, SR.afst(A, S, tthaw(A, S, tgo(~A, ~S, ~next, d, Nat.sub(n, 1n), t, s)))))), occ(~A, ~V, ~rel, v, AR.slots(A, AR.freeze(A, AR.thaw(A, g1)))), occ(~A, ~V, ~rel, v, AR.slots(A, t)),
      e2,
      Equal.trans(Nat, occ(~A, ~V, ~rel, v, AR.slots(A, AR.freeze(A, AR.thaw(A, g1)))), occ(~A, ~V, ~rel, v, AR.slots(A, g1)), occ(~A, ~V, ~rel, v, AR.slots(A, t)), e3, e4)))
