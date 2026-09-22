import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/array.bend as AR
import ../spec/common.bend as SC
import ../../src/containers/deque.bend as DQ
import ./ring.bend as R
import ./state.bend as ST

# Growing a full ring (src/deque.bend `grow`): the len = 2^d elements are
# copied, in ring order, into slots 0 .. len - 1 of a new block of 2^(d+1)
# slots. `cpt` is the Data mirror of the copy loop `copy_go` (the block
# after k more copies starting at position j); cp_real says the runtime loop
# builds exactly thaw(cpt(...)), cp_slots what its slots are: the rotation
# of the old slots followed by the untouched filler.

def cpt(-T: Data, +D: Nat, k: Nat, +j: Nat, +lo: Nat, +c: Nat, td: AR.Tree<T>, +ts: AR.Tree<T>) -> AR.Tree<T>:
  match k:
    case 0n:
      td
    case 1n+ +p:
      cpt(T, D, p, 1n+j, lo, c, AR.upd(T, D, td, j, ST.vat(T, ts, DQ.wrap(Nat.add(lo, j), c))), ts)

def lt_add_s(+a: Nat, +p: Nat) -> {Nat.is_lt(a, Nat.add(a, 1n+p)) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+ +q:
      lt_add_s(q, p)

# add(j, 1 + p) <= c  ->  add(1 + j, p) <= c
def shift_le(+j: Nat, +p: Nat, +c: Nat, +h: {Nat.is_le(Nat.add(j, 1n+p), c) == True{} : Bool}) -> {Nat.is_le(Nat.add(1n+j, p), c) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(z, c) == True{} : Bool}, Nat.add(j, 1n+p), 1n+Nat.add(j, p), N.add_succ(j, p), h)

def cp_real(~T: Data, +d: Nat, k: Nat, +j: Nat, +lo: Nat, +td: AR.Tree<T>, +ts: AR.Tree<T>, +hd: {Nat.is_le(1n+d, 31n) == True{} : Bool}, +pts: {AR.perfect(T, d, ts) == True{} : Bool}, +ptd: {AR.perfect(T, 1n+d, td) == True{} : Bool}, +hlo: {Nat.is_lt(lo, SC.pow2(d)) == True{} : Bool}, +hjk: {Nat.is_le(Nat.add(j, k), SC.pow2(d)) == True{} : Bool}) -> {DQ.copy_go(~T, k, j, lo, SC.pow2(d), AR.thaw(T, td), (AR.thaw(T, ts), ST.vat(T, ts, DQ.wrap(Nat.add(lo, j), SC.pow2(d))))) == AR.thaw(T, cpt(T, 1n+d, k, j, lo, SC.pow2(d), td, ts)) : Array<T>}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      +c = SC.pow2(d)
      +hd0 = N.le_trans(d, 1n+d, 31n, N.le_succ(d), hd)
      +x = ST.vat(T, ts, DQ.wrap(Nat.add(lo, j), c))
      +hjc = N.lt_le_trans(j, Nat.add(j, 1n+p), c, lt_add_s(j, p), hjk)
      +hj2 = N.lt_le_trans(j, c, Nat.double(c), hjc, N.double_self_le(c))
      +h1j = N.le_trans(1n+j, Nat.add(1n+j, p), c, N.le_add_right(1n+j, p), shift_le(j, p, c, hjk))
      +w = DQ.wrap(Nat.add(lo, 1n+j), c)
      +hw = R.wrap_lt(Nat.add(lo, 1n+j), c, R.two_lt(lo, 1n+j, c, hlo, h1j))
      %Equal.sym(Array<T>, Array.set(T, AR.thaw(T, td), U32.from_nat(j), x), AR.thaw(T, AR.upd(T, 1n+d, td, j, x)), ST.set_at(T, 1n+d, td, j, x, hd, ptd, hj2)) : {DQ.copy_go(~T, p, 1n+j, lo, c, _, Array.get(T, AR.thaw(T, ts), U32.from_nat(w))) == AR.thaw(T, cpt(T, 1n+d, 1n+p, j, lo, c, td, ts)) : Array<T>}
      %Equal.sym(Array<T> & T, Array.get(T, AR.thaw(T, ts), U32.from_nat(w)), (AR.thaw(T, ts), ST.vat(T, ts, w)), ST.get_at(T, d, ts, w, hd0, pts, hw)) : {DQ.copy_go(~T, p, 1n+j, lo, c, AR.thaw(T, AR.upd(T, 1n+d, td, j, x)), _) == AR.thaw(T, cpt(T, 1n+d, 1n+p, j, lo, c, td, ts)) : Array<T>}
      cp_real(~T, d, p, 1n+j, lo, AR.upd(T, 1n+d, td, j, x), ts, hd, pts, AR.upd_perfect(T, 1n+d, td, j, x, ptd), hlo, shift_le(j, p, c, hjk))

def cp_perfect(-T: Data, +D: Nat, k: Nat, +j: Nat, +lo: Nat, +c: Nat, +td: AR.Tree<T>, +ts: AR.Tree<T>, +ptd: {AR.perfect(T, D, td) == True{} : Bool}) -> {AR.perfect(T, D, cpt(T, D, k, j, lo, c, td, ts)) == True{} : Bool}:
  match k:
    case 0n:
      ptd
    case 1n+ +p:
      cp_perfect(T, D, p, 1n+j, lo, c, AR.upd(T, D, td, j, ST.vat(T, ts, DQ.wrap(Nat.add(lo, j), c))), ts, AR.upd_perfect(T, D, td, j, ST.vat(T, ts, DQ.wrap(Nat.add(lo, j), c)), ptd))

def double_add(+n: Nat) -> {Nat.double(n) == Nat.add(n, n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      %Equal.sym(Nat, Nat.add(p, 1n+p), 1n+Nat.add(p, p), N.add_succ(p, p)) : {2n+Nat.double(p) == 1n+_ : Nat}
      N.succ_cong(1n+Nat.double(p), 1n+Nat.add(p, p), N.succ_cong(Nat.double(p), Nat.add(p, p), double_add(p)))

def drop_rep(-A: Data, +m: Nat, +n: Nat, +x: A) -> {SC.drop(A, SC.replicate(A, Nat.add(m, n), x), m) == SC.replicate(A, n, x) : List<&2, A>}:
  match m:
    case 0n:
      R.drop_zero(A, SC.replicate(A, n, x))
    case 1n+ +p:
      drop_rep(A, p, n, x)

# the ring position j of a good ring is the slot value the copy writes
def ring_at(-T: Data, +d: Nat, +lo: Nat, +j: Nat, +ts: AR.Tree<T>, +pts: {AR.perfect(T, d, ts) == True{} : Bool}, +hlo: {Nat.is_lt(lo, SC.pow2(d)) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}) -> {SC.nth(T, R.rot(T, AR.slots(T, ts), lo), j) == Some{ST.vat(T, ts, DQ.wrap(Nat.add(lo, j), SC.pow2(d)))} : Maybe<&2, T>}:
  +c = SC.pow2(d)
  +el = AR.slots_length(T, d, ts, pts)
  +hlo2 = L.subst(Nat, z => {Nat.is_lt(lo, z) == True{} : Bool}, c, SC.length(T, AR.slots(T, ts)), Equal.sym(Nat, SC.length(T, AR.slots(T, ts)), c, el), hlo)
  +hj2 = L.subst(Nat, z => {Nat.is_lt(j, z) == True{} : Bool}, c, SC.length(T, AR.slots(T, ts)), Equal.sym(Nat, SC.length(T, AR.slots(T, ts)), c, el), hj)
  +e1 = R.rot_nth(T, AR.slots(T, ts), lo, j, hlo2, hj2)
  +e2 = L.subst(Nat, z => {SC.nth(T, R.rot(T, AR.slots(T, ts), lo), j) == SC.nth(T, AR.slots(T, ts), DQ.wrap(Nat.add(lo, j), z)) : Maybe<&2, T>}, SC.length(T, AR.slots(T, ts)), c, el, e1)
  +hw = R.wrap_lt(Nat.add(lo, j), c, R.two_lt(lo, j, c, hlo, N.lt_le(j, c, hj)))
  Equal.trans(Maybe<&2, T>, SC.nth(T, R.rot(T, AR.slots(T, ts), lo), j), SC.nth(T, AR.slots(T, ts), DQ.wrap(Nat.add(lo, j), c)), Some{ST.vat(T, ts, DQ.wrap(Nat.add(lo, j), c))}, e2, ST.slot_val(T, d, ts, DQ.wrap(Nat.add(lo, j), c), pts, hw))

def cp_step_slots(-T: Data, +D: Nat, +j: Nat, +lo: Nat, +td: AR.Tree<T>, +ts: AR.Tree<T>, +G: List<&2, T>, +d: Nat, +pts: {AR.perfect(T, d, ts) == True{} : Bool}, +ptd: {AR.perfect(T, D, td) == True{} : Bool}, +hlo: {Nat.is_lt(lo, SC.pow2(d)) == True{} : Bool}, +hjc: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, +hG: {SC.length(T, G) == SC.pow2(D) : Nat}, +hcD: {Nat.is_le(SC.pow2(d), SC.pow2(D)) == True{} : Bool}, +hs: {AR.slots(T, td) == SC.append(T, SC.take(T, R.rot(T, AR.slots(T, ts), lo), j), SC.drop(T, G, j)) : List<&2, T>}) -> {AR.slots(T, AR.upd(T, D, td, j, ST.vat(T, ts, DQ.wrap(Nat.add(lo, j), SC.pow2(d))))) == SC.append(T, SC.take(T, R.rot(T, AR.slots(T, ts), lo), 1n+j), SC.drop(T, G, 1n+j)) : List<&2, T>}:
  +c = SC.pow2(d)
  +r = R.rot(T, AR.slots(T, ts), lo)
  +x = ST.vat(T, ts, DQ.wrap(Nat.add(lo, j), c))
  +hjD = N.lt_le_trans(j, c, SC.pow2(D), hjc, hcD)
  +el = AR.slots_length(T, d, ts, pts)
  +hlr = L.subst(Nat, z => {Nat.is_le(j, z) == True{} : Bool}, c, SC.length(T, r), Equal.sym(Nat, SC.length(T, r), c, Equal.trans(Nat, SC.length(T, r), SC.length(T, AR.slots(T, ts)), c, R.rot_len(T, AR.slots(T, ts), lo, L.subst(Nat, z => {Nat.is_le(lo, z) == True{} : Bool}, c, SC.length(T, AR.slots(T, ts)), Equal.sym(Nat, SC.length(T, AR.slots(T, ts)), c, el), N.lt_le(lo, c, hlo))), el)), N.lt_le(j, c, hjc))
  +elt = LL.sc_length_take(T, r, j, hlr)
  +hjG = L.subst(Nat, z => {Nat.is_lt(j, z) == True{} : Bool}, SC.pow2(D), SC.length(T, G), Equal.sym(Nat, SC.length(T, G), SC.pow2(D), hG), hjD)
  +g = L.some_value(T, SC.nth(T, G, j), x)
  +eg = ST.nth_some(T, G, j, x, hjG)
  %Equal.sym(List<&2, T>, AR.slots(T, AR.upd(T, D, td, j, x)), SC.update(T, AR.slots(T, td), j, x), AR.upd_slots(T, D, td, j, x, hjD, ptd)) : {_ == SC.append(T, SC.take(T, r, 1n+j), SC.drop(T, G, 1n+j)) : List<&2, T>}
  %Equal.sym(List<&2, T>, AR.slots(T, td), SC.append(T, SC.take(T, r, j), SC.drop(T, G, j)), hs) : {SC.update(T, _, j, x) == SC.append(T, SC.take(T, r, 1n+j), SC.drop(T, G, 1n+j)) : List<&2, T>}
  %Equal.sym(List<&2, T>, SC.update(T, SC.append(T, SC.take(T, r, j), SC.drop(T, G, j)), j, x), SC.append(T, SC.take(T, r, j), SC.update(T, SC.drop(T, G, j), Nat.sub(j, SC.length(T, SC.take(T, r, j))), x)), LL.update_append_right(T, SC.take(T, r, j), SC.drop(T, G, j), j, x, N.eq_le(SC.length(T, SC.take(T, r, j)), j, elt))) : {_ == SC.append(T, SC.take(T, r, 1n+j), SC.drop(T, G, 1n+j)) : List<&2, T>}
  %Equal.sym(Nat, SC.length(T, SC.take(T, r, j)), j, elt) : {SC.append(T, SC.take(T, r, j), SC.update(T, SC.drop(T, G, j), Nat.sub(j, _), x)) == SC.append(T, SC.take(T, r, 1n+j), SC.drop(T, G, 1n+j)) : List<&2, T>}
  %Equal.sym(Nat, Nat.sub(j, j), 0n, N.sub_self(j)) : {SC.append(T, SC.take(T, r, j), SC.update(T, SC.drop(T, G, j), _, x)) == SC.append(T, SC.take(T, r, 1n+j), SC.drop(T, G, 1n+j)) : List<&2, T>}
  %Equal.sym(List<&2, T>, SC.drop(T, G, j), Con{g, SC.drop(T, G, 1n+j)}, R.drop_cons(T, G, j, g, eg)) : {SC.append(T, SC.take(T, r, j), SC.update(T, _, 0n, x)) == SC.append(T, SC.take(T, r, 1n+j), SC.drop(T, G, 1n+j)) : List<&2, T>}
  %Equal.sym(List<&2, T>, SC.take(T, r, 1n+j), SC.snoc(T, SC.take(T, r, j), x), R.take_succ_snoc(T, r, j, x, ring_at(T, d, lo, j, ts, pts, hlo, hjc))) : {SC.append(T, SC.take(T, r, j), Con{x, SC.drop(T, G, 1n+j)}) == SC.append(T, _, SC.drop(T, G, 1n+j)) : List<&2, T>}
  Equal.sym(List<&2, T>, SC.append(T, SC.snoc(T, SC.take(T, r, j), x), SC.drop(T, G, 1n+j)), SC.append(T, SC.take(T, r, j), Con{x, SC.drop(T, G, 1n+j)}), LL.snoc_append_cons(T, SC.take(T, r, j), x, SC.drop(T, G, 1n+j)))

def cp_slots(-T: Data, +D: Nat, k: Nat, +j: Nat, +lo: Nat, +td: AR.Tree<T>, +ts: AR.Tree<T>, +G: List<&2, T>, +d: Nat, +pts: {AR.perfect(T, d, ts) == True{} : Bool}, +ptd: {AR.perfect(T, D, td) == True{} : Bool}, +hlo: {Nat.is_lt(lo, SC.pow2(d)) == True{} : Bool}, +hjk: {Nat.is_le(Nat.add(j, k), SC.pow2(d)) == True{} : Bool}, +hG: {SC.length(T, G) == SC.pow2(D) : Nat}, +hcD: {Nat.is_le(SC.pow2(d), SC.pow2(D)) == True{} : Bool}, +hs: {AR.slots(T, td) == SC.append(T, SC.take(T, R.rot(T, AR.slots(T, ts), lo), j), SC.drop(T, G, j)) : List<&2, T>}) -> {AR.slots(T, cpt(T, D, k, j, lo, SC.pow2(d), td, ts)) == SC.append(T, SC.take(T, R.rot(T, AR.slots(T, ts), lo), Nat.add(j, k)), SC.drop(T, G, Nat.add(j, k))) : List<&2, T>}:
  match k:
    case 0n:
      %Equal.sym(Nat, Nat.add(j, 0n), j, N.add_zero(j)) : {AR.slots(T, td) == SC.append(T, SC.take(T, R.rot(T, AR.slots(T, ts), lo), _), SC.drop(T, G, _)) : List<&2, T>}
      hs
    case 1n+ +p:
      +c = SC.pow2(d)
      +x = ST.vat(T, ts, DQ.wrap(Nat.add(lo, j), c))
      +hjc = N.lt_le_trans(j, Nat.add(j, 1n+p), c, lt_add_s(j, p), hjk)
      +ih = cp_slots(T, D, p, 1n+j, lo, AR.upd(T, D, td, j, x), ts, G, d, pts, AR.upd_perfect(T, D, td, j, x, ptd), hlo, shift_le(j, p, c, hjk), hG, hcD, cp_step_slots(T, D, j, lo, td, ts, G, d, pts, ptd, hlo, hjc, hG, hcD, hs))
      %Equal.sym(Nat, Nat.add(j, 1n+p), 1n+Nat.add(j, p), N.add_succ(j, p)) : {AR.slots(T, cpt(T, D, 1n+p, j, lo, c, td, ts)) == SC.append(T, SC.take(T, R.rot(T, AR.slots(T, ts), lo), _), SC.drop(T, G, _)) : List<&2, T>}
      ih

# The grown block of a full ring of 2^d elements.
def gt(-T: Data, +d: Nat, +lo: Nat, +t: AR.Tree<T>, +v: T) -> AR.Tree<T>:
  cpt(T, 1n+d, SC.pow2(d), 0n, lo, SC.pow2(d), AR.trep(T, 1n+d, v), t)

def grow_real(~T: Data, +d: Nat, +lo: Nat, +t: AR.Tree<T>, +v: T, +hd: {Nat.is_le(1n+d, 31n) == True{} : Bool}, +pf: {AR.perfect(T, d, t) == True{} : Bool}, +hlo: {Nat.is_lt(lo, SC.pow2(d)) == True{} : Bool}) -> {DQ.grow(~T, d, SC.pow2(d), lo, SC.pow2(d), AR.thaw(T, t), v) == AR.thaw(T, gt(T, d, lo, t, v)) : Array<T>}:
  +c = SC.pow2(d)
  +hd0 = N.le_trans(d, 1n+d, 31n, N.le_succ(d), hd)
  +w = DQ.wrap(Nat.add(lo, 0n), c)
  +hw = R.wrap_lt(Nat.add(lo, 0n), c, R.two_lt(lo, 0n, c, hlo, N.zero_le(c)))
  %Equal.sym(Array<T>, Array.new(T, 1n+d, v), AR.thaw(T, AR.trep(T, 1n+d, v)), AR.new(T, 1n+d, v)) : {DQ.copy_go(~T, c, 0n, lo, c, _, Array.get(T, AR.thaw(T, t), U32.from_nat(w))) == AR.thaw(T, gt(T, d, lo, t, v)) : Array<T>}
  %Equal.sym(Array<T> & T, Array.get(T, AR.thaw(T, t), U32.from_nat(w)), (AR.thaw(T, t), ST.vat(T, t, w)), ST.get_at(T, d, t, w, hd0, pf, hw)) : {DQ.copy_go(~T, c, 0n, lo, c, AR.thaw(T, AR.trep(T, 1n+d, v)), _) == AR.thaw(T, gt(T, d, lo, t, v)) : Array<T>}
  cp_real(~T, d, c, 0n, lo, AR.trep(T, 1n+d, v), t, hd, pf, AR.trep_perfect(T, 1n+d, v), hlo, N.le_refl(c))

def gt_perfect(-T: Data, +d: Nat, +lo: Nat, +t: AR.Tree<T>, +v: T) -> {AR.perfect(T, 1n+d, gt(T, d, lo, t, v)) == True{} : Bool}:
  cp_perfect(T, 1n+d, SC.pow2(d), 0n, lo, SC.pow2(d), AR.trep(T, 1n+d, v), t, AR.trep_perfect(T, 1n+d, v))

def gt_slots(-T: Data, +d: Nat, +lo: Nat, +t: AR.Tree<T>, +v: T, +pf: {AR.perfect(T, d, t) == True{} : Bool}, +hlo: {Nat.is_lt(lo, SC.pow2(d)) == True{} : Bool}) -> {AR.slots(T, gt(T, d, lo, t, v)) == SC.append(T, R.rot(T, AR.slots(T, t), lo), SC.replicate(T, SC.pow2(d), v)) : List<&2, T>}:
  +c = SC.pow2(d)
  +r = R.rot(T, AR.slots(T, t), lo)
  +G = SC.replicate(T, SC.pow2(1n+d), v)
  +el = AR.slots_length(T, d, t, pf)
  +elr = Equal.trans(Nat, SC.length(T, r), SC.length(T, AR.slots(T, t)), c, R.rot_len(T, AR.slots(T, t), lo, L.subst(Nat, z => {Nat.is_le(lo, z) == True{} : Bool}, c, SC.length(T, AR.slots(T, t)), Equal.sym(Nat, SC.length(T, AR.slots(T, t)), c, el), N.lt_le(lo, c, hlo))), el)
  +hs0 = Equal.trans(List<&2, T>, AR.slots(T, AR.trep(T, 1n+d, v)), G, SC.append(T, SC.take(T, r, 0n), SC.drop(T, G, 0n)), AR.trep_slots(T, 1n+d, v),
    L.subst(List<&2, T>, z => {G == SC.append(T, z, SC.drop(T, G, 0n)) : List<&2, T>}, Nil{}, SC.take(T, r, 0n), Equal.sym(List<&2, T>, SC.take(T, r, 0n), Nil{}, LL.sc_take_zero(T, r)), Equal.sym(List<&2, T>, SC.drop(T, G, 0n), G, R.drop_zero(T, G))))
  +e = cp_slots(T, 1n+d, c, 0n, lo, AR.trep(T, 1n+d, v), t, G, d, pf, AR.trep_perfect(T, 1n+d, v), hlo, N.le_refl(c), LL.length_replicate(T, SC.pow2(1n+d), v), N.double_self_le(c), hs0)
  %Equal.sym(List<&2, T>, AR.slots(T, gt(T, d, lo, t, v)), SC.append(T, SC.take(T, r, c), SC.drop(T, G, c)), e) : {_ == SC.append(T, r, SC.replicate(T, c, v)) : List<&2, T>}
  %Equal.sym(List<&2, T>, SC.take(T, r, c), r, L.subst(Nat, z => {SC.take(T, r, z) == r : List<&2, T>}, SC.length(T, r), c, elr, R.take_len(T, r))) : {SC.append(T, _, SC.drop(T, G, c)) == SC.append(T, r, SC.replicate(T, c, v)) : List<&2, T>}
  %Equal.sym(Nat, Nat.double(c), Nat.add(c, c), double_add(c)) : {SC.append(T, r, SC.drop(T, SC.replicate(T, _, v), c)) == SC.append(T, r, SC.replicate(T, c, v)) : List<&2, T>}
  %Equal.sym(List<&2, T>, SC.drop(T, SC.replicate(T, Nat.add(c, c), v), c), SC.replicate(T, c, v), drop_rep(T, c, c, v)) : {SC.append(T, r, _) == SC.append(T, r, SC.replicate(T, c, v)) : List<&2, T>}
  {==}
