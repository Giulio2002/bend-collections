import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/u32.bend as U32L
import ../lib/array.bend as A
import ../lib/flat.bend as FL
import ../../spec/common.bend as SC
import ../../src/segment_tree.bend as F

# The bridge between the two flat native `Base.Array`s of
# src/segment_tree.bend (cells and tags) and the lists the mathematics
# talks about. Both arrays hold the same cell type, so one set of lemmas
# serves both.
#
# Arrays are linear, so (exactly as in proofs/bitset)
# every statement is about `A.thaw(t)`, the array built from a Data mirror
# tree `t`; `cl(t)` is the list of the U32 values in index order.

def cmap(xs: List<&2, F.Cel>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{F.cval(x), cmap(t)}

def cl(t: A.Tree<F.Cel>) -> List<&2, U32>:
  cmap(A.slots(F.Cel, t))

# Slot q of a raw slot list (the callers always stay in range).
def cels(xs: List<&2, F.Cel>, q: Nat) -> F.Cel:
  match xs q:
    case Nil{} _:
      F.CV{0}
    case Con{x, t} 0n:
      x
    case Con{x, t} 1n+p:
      cels(t, p)

def cels_nth(xs: List<&2, F.Cel>, q: Nat, +h: {Nat.is_lt(q, SC.length(F.Cel, xs)) == True{} : Bool}) -> {SC.nth(F.Cel, xs, q) == Some{cels(xs, q)} : Maybe<&2, F.Cel>}:
  match xs q:
    case Nil{} _:
      Empty.absurd({SC.nth(F.Cel, Nil{}, q) == Some{cels(Nil{}, q)} : Maybe<&2, F.Cel>}, N.lt_zero_absurd(q, h))
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      cels_nth(t, p, h)

def cval_cels(xs: List<&2, F.Cel>, q: Nat) -> {F.cval(cels(xs, q)) == FL.nthc(cmap(xs), q) : U32}:
  match xs q:
    case Nil{} _:
      {==}
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      cval_cels(t, p)

# ---- shape ----

def cmap_length(xs: List<&2, F.Cel>) -> {SC.length(U32, cmap(xs)) == SC.length(F.Cel, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      N.succ_cong(SC.length(U32, cmap(t)), SC.length(F.Cel, t), cmap_length(t))

def cl_length(+d: Nat, +t: A.Tree<F.Cel>, +pf: {A.perfect(F.Cel, d, t) == True{} : Bool}) -> {SC.length(U32, cl(t)) == SC.pow2(d) : Nat}:
  Equal.trans(Nat, SC.length(U32, cmap(A.slots(F.Cel, t))), SC.length(F.Cel, A.slots(F.Cel, t)), SC.pow2(d),
    cmap_length(A.slots(F.Cel, t)), A.slots_length(F.Cel, d, t, pf))

def idx_ok(+d: Nat, +q: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hq: {Nat.is_lt(q, SC.pow2(d)) == True{} : Bool}) -> {U32.to_nat(U32.from_nat(q)) == q : Nat}:
  U32L.to_nat_from_nat(q, d, N.lt_le(d, 32n, hd), hq)

def slots_lt(+d: Nat, +t: A.Tree<F.Cel>, +q: Nat, +pf: {A.perfect(F.Cel, d, t) == True{} : Bool}, +hq: {Nat.is_lt(q, SC.pow2(d)) == True{} : Bool}) -> {Nat.is_lt(q, SC.length(F.Cel, A.slots(F.Cel, t))) == True{} : Bool}:
  L.subst(Nat, k => {Nat.is_lt(q, k) == True{} : Bool}, SC.pow2(d), SC.length(F.Cel, A.slots(F.Cel, t)),
    Equal.sym(Nat, SC.length(F.Cel, A.slots(F.Cel, t)), SC.pow2(d), A.slots_length(F.Cel, d, t, pf)), hq)

# ---- read ----

def get_ok(+d: Nat, +t: A.Tree<F.Cel>, +q: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hq: {Nat.is_lt(q, SC.pow2(d)) == True{} : Bool}, +pf: {A.perfect(F.Cel, d, t) == True{} : Bool}) -> {Array.get(F.Cel, A.thaw(F.Cel, t), U32.from_nat(q)) == (A.thaw(F.Cel, t), cels(A.slots(F.Cel, t), q)) : Array<F.Cel> & F.Cel}:
  A.get(F.Cel, d, t, U32.from_nat(q), cels(A.slots(F.Cel, t), q), hd,
    L.subst(Nat, j => {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, q, U32.to_nat(U32.from_nat(q)), Equal.sym(Nat, U32.to_nat(U32.from_nat(q)), q, idx_ok(d, q, hd, hq)), hq),
    L.subst(Nat, j => {SC.nth(F.Cel, A.slots(F.Cel, t), j) == Some{cels(A.slots(F.Cel, t), q)} : Maybe<&2, F.Cel>}, q, U32.to_nat(U32.from_nat(q)), Equal.sym(Nat, U32.to_nat(U32.from_nat(q)), q, idx_ok(d, q, hd, hq)), cels_nth(A.slots(F.Cel, t), q, slots_lt(d, t, q, pf, hq))),
    pf)

def read_ok(+d: Nat, +t: A.Tree<F.Cel>, +q: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hq: {Nat.is_lt(q, SC.pow2(d)) == True{} : Bool}, +pf: {A.perfect(F.Cel, d, t) == True{} : Bool}) -> {F.read(A.thaw(F.Cel, t), q) == (A.thaw(F.Cel, t), FL.nthc(cl(t), q)) : Array<F.Cel> & U32}:
  %cval_cels(A.slots(F.Cel, t), q) : {F.read(A.thaw(F.Cel, t), q) == (A.thaw(F.Cel, t), _) : Array<F.Cel> & U32}
  Equal.cong(Array<F.Cel> & F.Cel, Array<F.Cel> & U32, F.read_fin,
    Array.get(F.Cel, A.thaw(F.Cel, t), U32.from_nat(q)),
    (A.thaw(F.Cel, t), cels(A.slots(F.Cel, t), q)),
    get_ok(d, t, q, hd, hq, pf))

# ---- write ----

def write_ok(+d: Nat, +t: A.Tree<F.Cel>, +q: Nat, +v: U32, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hq: {Nat.is_lt(q, SC.pow2(d)) == True{} : Bool}, +pf: {A.perfect(F.Cel, d, t) == True{} : Bool}) -> {F.write(A.thaw(F.Cel, t), q, v) == A.thaw(F.Cel, A.upd(F.Cel, d, t, q, F.CV{v})) : Array<F.Cel>}:
  %idx_ok(d, q, hd, hq) : {F.write(A.thaw(F.Cel, t), q, v) == A.thaw(F.Cel, A.upd(F.Cel, d, t, _, F.CV{v})) : Array<F.Cel>}
  A.set(F.Cel, d, t, U32.from_nat(q), F.CV{v}, cels(A.slots(F.Cel, t), q), hd,
    L.subst(Nat, j => {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, q, U32.to_nat(U32.from_nat(q)), Equal.sym(Nat, U32.to_nat(U32.from_nat(q)), q, idx_ok(d, q, hd, hq)), hq),
    L.subst(Nat, j => {SC.nth(F.Cel, A.slots(F.Cel, t), j) == Some{cels(A.slots(F.Cel, t), q)} : Maybe<&2, F.Cel>}, q, U32.to_nat(U32.from_nat(q)), Equal.sym(Nat, U32.to_nat(U32.from_nat(q)), q, idx_ok(d, q, hd, hq)), cels_nth(A.slots(F.Cel, t), q, slots_lt(d, t, q, pf, hq))),
    pf)

def cmap_update(xs: List<&2, F.Cel>, q: Nat, +v: U32) -> {cmap(SC.update(F.Cel, xs, q, F.CV{v})) == SC.update(U32, cmap(xs), q, v) : List<&2, U32>}:
  match xs q:
    case Nil{} _:
      {==}
    case Con{x, t} 0n:
      {==}
    case Con{+x, +t} 1n+p:
      Equal.cong(List<&2, U32>, List<&2, U32>, w => Con{F.cval(x), w},
        cmap(SC.update(F.Cel, t, p, F.CV{v})), SC.update(U32, cmap(t), p, v), cmap_update(t, p, v))

def cl_upd(+d: Nat, +t: A.Tree<F.Cel>, +q: Nat, +v: U32, +hq: {Nat.is_lt(q, SC.pow2(d)) == True{} : Bool}, +pf: {A.perfect(F.Cel, d, t) == True{} : Bool}) -> {cl(A.upd(F.Cel, d, t, q, F.CV{v})) == SC.update(U32, cl(t), q, v) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, cmap(A.slots(F.Cel, A.upd(F.Cel, d, t, q, F.CV{v}))), cmap(SC.update(F.Cel, A.slots(F.Cel, t), q, F.CV{v})), SC.update(U32, cmap(A.slots(F.Cel, t)), q, v),
    Equal.cong(List<&2, F.Cel>, List<&2, U32>, w => cmap(w), A.slots(F.Cel, A.upd(F.Cel, d, t, q, F.CV{v})), SC.update(F.Cel, A.slots(F.Cel, t), q, F.CV{v}), A.upd_slots(F.Cel, d, t, q, F.CV{v}, hq, pf)),
    cmap_update(A.slots(F.Cel, t), q, v))

# ---- one read-modify-write ----

def bump_ok(+d: Nat, +t: A.Tree<F.Cel>, +q: Nat, +v: U32, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hq: {Nat.is_lt(q, SC.pow2(d)) == True{} : Bool}, +pf: {A.perfect(F.Cel, d, t) == True{} : Bool}) -> {F.bump(A.thaw(F.Cel, t), q, v) == A.thaw(F.Cel, A.upd(F.Cel, d, t, q, F.CV{U32.add(FL.nthc(cl(t), q), v)})) : Array<F.Cel>}:
  %Equal.sym(Array<F.Cel> & U32, F.read(A.thaw(F.Cel, t), q), (A.thaw(F.Cel, t), FL.nthc(cl(t), q)), read_ok(d, t, q, hd, hq, pf)) : {F.bump_fin(_, q, v) == A.thaw(F.Cel, A.upd(F.Cel, d, t, q, F.CV{U32.add(FL.nthc(cl(t), q), v)})) : Array<F.Cel>}
  write_ok(d, t, q, U32.add(FL.nthc(cl(t), q), v), hd, hq, pf)
