import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/u32.bend as U
import ../lib/array.bend as A
import ../../spec/common.bend as SC
import ../../src/bitset.bend as B
import ./model.bend as MD
import ./walk.bend as WK
import ./listx.bend as LX

# The bridge between src/bitset.bend's native Base.Array of words and the
# word list the rest of the proof talks about.
#
# Arrays are linear, so (exactly as in proofs/dynamic_array) every statement
# is about `A.thaw(t)`, the array built from a Data mirror tree `t` of the
# same shape; `ws(t)` is the list of the words it holds.

def wmap(xs: List<&2, B.Wd>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{B.wval(x), wmap(t)}

def ws(t: A.Tree<B.Wd>) -> List<&2, U32>:
  wmap(A.slots(B.Wd, t))

# Slot q of a word list (the callers always stay in range; the default keeps
# the function total and agrees with WK.nthw's default).
def nths(xs: List<&2, B.Wd>, q: Nat) -> B.Wd:
  match xs q:
    case Nil{} _:
      B.W{0}
    case Con{x, t} 0n:
      x
    case Con{x, t} 1n+p:
      nths(t, p)

# ---- wmap ----

def wmap_length(xs: List<&2, B.Wd>) -> {SC.length(U32, wmap(xs)) == SC.length(B.Wd, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      N.succ_cong(SC.length(U32, wmap(t)), SC.length(B.Wd, t), wmap_length(t))

def wmap_update(xs: List<&2, B.Wd>, q: Nat, +v: U32) -> {wmap(SC.update(B.Wd, xs, q, B.W{v})) == SC.update(U32, wmap(xs), q, v) : List<&2, U32>}:
  match xs q:
    case Nil{} _:
      {==}
    case Con{x, t} 0n:
      {==}
    case Con{+x, +t} 1n+p:
      Equal.cong(List<&2, U32>, List<&2, U32>, z => Con{B.wval(x), z},
        wmap(SC.update(B.Wd, t, p, B.W{v})), SC.update(U32, wmap(t), p, v), wmap_update(t, p, v))

def wval_nths(xs: List<&2, B.Wd>, q: Nat) -> {B.wval(nths(xs, q)) == WK.nthw(wmap(xs), q) : U32}:
  match xs q:
    case Nil{} _:
      {==}
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      wval_nths(t, p)

def nths_nth(xs: List<&2, B.Wd>, q: Nat, +h: {Nat.is_lt(q, SC.length(B.Wd, xs)) == True{} : Bool}) -> {SC.nth(B.Wd, xs, q) == Some{nths(xs, q)} : Maybe<&2, B.Wd>}:
  match xs q:
    case Nil{} _:
      Empty.absurd({SC.nth(B.Wd, Nil{}, q) == Some{nths(Nil{}, q)} : Maybe<&2, B.Wd>}, N.lt_zero_absurd(q, h))
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      nths_nth(t, p, h)

# ---- shape ----

def ws_length(+d: Nat, +t: A.Tree<B.Wd>, +pf: {A.perfect(B.Wd, d, t) == True{} : Bool}) -> {SC.length(U32, ws(t)) == SC.pow2(d) : Nat}:
  Equal.trans(Nat, SC.length(U32, wmap(A.slots(B.Wd, t))), SC.length(B.Wd, A.slots(B.Wd, t)), SC.pow2(d),
    wmap_length(A.slots(B.Wd, t)), A.slots_length(B.Wd, d, t, pf))

def slots_lt(+d: Nat, +t: A.Tree<B.Wd>, +q: Nat, +pf: {A.perfect(B.Wd, d, t) == True{} : Bool}, +hq: {Nat.is_lt(q, SC.pow2(d)) == True{} : Bool}) -> {Nat.is_lt(q, SC.length(B.Wd, A.slots(B.Wd, t))) == True{} : Bool}:
  L.subst(Nat, k => {Nat.is_lt(q, k) == True{} : Bool}, SC.pow2(d), SC.length(B.Wd, A.slots(B.Wd, t)),
    Equal.sym(Nat, SC.length(B.Wd, A.slots(B.Wd, t)), SC.pow2(d), A.slots_length(B.Wd, d, t, pf)), hq)

def idx_ok(+d: Nat, +q: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hq: {Nat.is_lt(q, SC.pow2(d)) == True{} : Bool}) -> {U32.to_nat(U32.from_nat(q)) == q : Nat}:
  U.to_nat_from_nat(q, d, N.lt_le(d, 32n, hd), hq)

# ---- read ----

def read_ok(+d: Nat, +t: A.Tree<B.Wd>, +q: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hq: {Nat.is_lt(q, SC.pow2(d)) == True{} : Bool}, +pf: {A.perfect(B.Wd, d, t) == True{} : Bool}) -> {B.read(A.thaw(B.Wd, t), d, q) == (A.thaw(B.Wd, t), WK.nthw(ws(t), q)) : Array<B.Wd> & U32}:
  %wval_nths(A.slots(B.Wd, t), q) : {B.read(A.thaw(B.Wd, t), d, q) == (A.thaw(B.Wd, t), _) : Array<B.Wd> & U32}
  Equal.cong(Array<B.Wd> & B.Wd, Array<B.Wd> & U32, B.read_fin,
    Array.get(B.Wd, A.thaw(B.Wd, t), U32.from_nat(q)),
    (A.thaw(B.Wd, t), nths(A.slots(B.Wd, t), q)),
    A.get(B.Wd, d, t, U32.from_nat(q), nths(A.slots(B.Wd, t), q), hd,
      L.subst(Nat, j => {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, q, U32.to_nat(U32.from_nat(q)), Equal.sym(Nat, U32.to_nat(U32.from_nat(q)), q, idx_ok(d, q, hd, hq)), hq),
      L.subst(Nat, j => {SC.nth(B.Wd, A.slots(B.Wd, t), j) == Some{nths(A.slots(B.Wd, t), q)} : Maybe<&2, B.Wd>}, q, U32.to_nat(U32.from_nat(q)), Equal.sym(Nat, U32.to_nat(U32.from_nat(q)), q, idx_ok(d, q, hd, hq)), nths_nth(A.slots(B.Wd, t), q, slots_lt(d, t, q, pf, hq))),
      pf))

# ---- write ----

def write_ok(+d: Nat, +t: A.Tree<B.Wd>, +q: Nat, +v: U32, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hq: {Nat.is_lt(q, SC.pow2(d)) == True{} : Bool}, +pf: {A.perfect(B.Wd, d, t) == True{} : Bool}) -> {B.write(A.thaw(B.Wd, t), d, q, v) == A.thaw(B.Wd, A.upd(B.Wd, d, t, q, B.W{v})) : Array<B.Wd>}:
  %idx_ok(d, q, hd, hq) : {B.write(A.thaw(B.Wd, t), d, q, v) == A.thaw(B.Wd, A.upd(B.Wd, d, t, _, B.W{v})) : Array<B.Wd>}
  A.set(B.Wd, d, t, U32.from_nat(q), B.W{v}, nths(A.slots(B.Wd, t), q), hd,
    L.subst(Nat, j => {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, q, U32.to_nat(U32.from_nat(q)), Equal.sym(Nat, U32.to_nat(U32.from_nat(q)), q, idx_ok(d, q, hd, hq)), hq),
    L.subst(Nat, j => {SC.nth(B.Wd, A.slots(B.Wd, t), j) == Some{nths(A.slots(B.Wd, t), q)} : Maybe<&2, B.Wd>}, q, U32.to_nat(U32.from_nat(q)), Equal.sym(Nat, U32.to_nat(U32.from_nat(q)), q, idx_ok(d, q, hd, hq)), nths_nth(A.slots(B.Wd, t), q, slots_lt(d, t, q, pf, hq))),
    pf)

def ws_upd(+d: Nat, +t: A.Tree<B.Wd>, +q: Nat, +v: U32, +hq: {Nat.is_lt(q, SC.pow2(d)) == True{} : Bool}, +pf: {A.perfect(B.Wd, d, t) == True{} : Bool}) -> {ws(A.upd(B.Wd, d, t, q, B.W{v})) == SC.update(U32, ws(t), q, v) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, wmap(A.slots(B.Wd, A.upd(B.Wd, d, t, q, B.W{v}))), wmap(SC.update(B.Wd, A.slots(B.Wd, t), q, B.W{v})), SC.update(U32, wmap(A.slots(B.Wd, t)), q, v),
    Equal.cong(List<&2, B.Wd>, List<&2, U32>, wmap, A.slots(B.Wd, A.upd(B.Wd, d, t, q, B.W{v})), SC.update(B.Wd, A.slots(B.Wd, t), q, B.W{v}), A.upd_slots(B.Wd, d, t, q, B.W{v}, hq, pf)),
    wmap_update(A.slots(B.Wd, t), q, v))

def upd_perfect(+d: Nat, +t: A.Tree<B.Wd>, +q: Nat, +v: U32, +pf: {A.perfect(B.Wd, d, t) == True{} : Bool}) -> {A.perfect(B.Wd, d, A.upd(B.Wd, d, t, q, B.W{v})) == True{} : Bool}:
  A.upd_perfect(B.Wd, d, t, q, B.W{v}, pf)

def wmap_replicate(+m: Nat, +v: U32) -> {wmap(SC.replicate(B.Wd, m, B.W{v})) == SC.replicate(U32, m, v) : List<&2, U32>}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(List<&2, U32>, List<&2, U32>, z => Con{v, z},
        wmap(SC.replicate(B.Wd, p, B.W{v})), SC.replicate(U32, p, v), wmap_replicate(p, v))

def ws_trep(+d: Nat, +v: U32) -> {ws(A.trep(B.Wd, d, B.W{v})) == SC.replicate(U32, SC.pow2(d), v) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, wmap(A.slots(B.Wd, A.trep(B.Wd, d, B.W{v}))), wmap(SC.replicate(B.Wd, SC.pow2(d), B.W{v})), SC.replicate(U32, SC.pow2(d), v),
    Equal.cong(List<&2, B.Wd>, List<&2, U32>, wmap, A.slots(B.Wd, A.trep(B.Wd, d, B.W{v})), SC.replicate(B.Wd, SC.pow2(d), B.W{v}), A.trep_slots(B.Wd, d, B.W{v})),
    wmap_replicate(SC.pow2(d), v))
