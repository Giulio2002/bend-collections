import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/u32.bend as U32L
import ../lib/array.bend as A
import ../../spec/common.bend as SC
import ../../src/union_find.bend as U
import ./cells.bend as CL
import ./model.bend as M

# The bridge between the three native Base.Array arenas of
# src/union_find.bend and the three slot lists the mathematics talks about.
#
# Arrays are linear, so (exactly as in proofs/dynamic_array and
# proofs/bitset) every statement is about `A.thaw(t)`, the array built from a
# Data mirror tree `t`.

def rsl(t: A.Tree<U.Nt>) -> List<&2, Nat>:
  CL.nmap(A.slots(U.Nt, t))

def msl(t: A.Tree<U.Ms>) -> List<&2, List<&2, Nat>>:
  CL.mmap(A.slots(U.Ms, t))

# Slot q of a raw slot list (the callers always stay in range).
def nths(xs: List<&2, U.Nt>, q: Nat) -> U.Nt:
  match xs q:
    case Nil{} _:
      U.N{0n}
    case Con{x, t} 0n:
      x
    case Con{x, t} 1n+p:
      nths(t, p)

def msths(xs: List<&2, U.Ms>, q: Nat) -> U.Ms:
  match xs q:
    case Nil{} _:
      U.M{Nil{}}
    case Con{x, t} 0n:
      x
    case Con{x, t} 1n+p:
      msths(t, p)

def nthn(xs: List<&2, Nat>, q: Nat) -> Nat:
  match xs q:
    case Nil{} _:
      0n
    case Con{x, t} 0n:
      x
    case Con{x, t} 1n+p:
      nthn(t, p)

def nthm(xs: List<&2, List<&2, Nat>>, q: Nat) -> List<&2, Nat>:
  match xs q:
    case Nil{} _:
      Nil{}
    case Con{x, t} 0n:
      x
    case Con{x, t} 1n+p:
      nthm(t, p)

# ---- the default accessors are nth in range ----

def nths_nth(xs: List<&2, U.Nt>, q: Nat, +h: {Nat.is_lt(q, SC.length(U.Nt, xs)) == True{} : Bool}) -> {SC.nth(U.Nt, xs, q) == Some{nths(xs, q)} : Maybe<&2, U.Nt>}:
  match xs q:
    case Nil{} _:
      Empty.absurd({SC.nth(U.Nt, Nil{}, q) == Some{nths(Nil{}, q)} : Maybe<&2, U.Nt>}, N.lt_zero_absurd(q, h))
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      nths_nth(t, p, h)

def msths_nth(xs: List<&2, U.Ms>, q: Nat, +h: {Nat.is_lt(q, SC.length(U.Ms, xs)) == True{} : Bool}) -> {SC.nth(U.Ms, xs, q) == Some{msths(xs, q)} : Maybe<&2, U.Ms>}:
  match xs q:
    case Nil{} _:
      Empty.absurd({SC.nth(U.Ms, Nil{}, q) == Some{msths(Nil{}, q)} : Maybe<&2, U.Ms>}, N.lt_zero_absurd(q, h))
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      msths_nth(t, p, h)

def nthn_nth(xs: List<&2, Nat>, q: Nat, +h: {Nat.is_lt(q, SC.length(Nat, xs)) == True{} : Bool}) -> {SC.nth(Nat, xs, q) == Some{nthn(xs, q)} : Maybe<&2, Nat>}:
  match xs q:
    case Nil{} _:
      Empty.absurd({SC.nth(Nat, Nil{}, q) == Some{nthn(Nil{}, q)} : Maybe<&2, Nat>}, N.lt_zero_absurd(q, h))
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      nthn_nth(t, p, h)

def nthm_nth(xs: List<&2, List<&2, Nat>>, q: Nat, +h: {Nat.is_lt(q, SC.length(List<&2, Nat>, xs)) == True{} : Bool}) -> {SC.nth(List<&2, Nat>, xs, q) == Some{nthm(xs, q)} : Maybe<&2, List<&2, Nat>>}:
  match xs q:
    case Nil{} _:
      Empty.absurd({SC.nth(List<&2, Nat>, Nil{}, q) == Some{nthm(Nil{}, q)} : Maybe<&2, List<&2, Nat>>}, N.lt_zero_absurd(q, h))
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      nthm_nth(t, p, h)

def nval_nths(xs: List<&2, U.Nt>, q: Nat) -> {U.nval(nths(xs, q)) == nthn(CL.nmap(xs), q) : Nat}:
  match xs q:
    case Nil{} _:
      {==}
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      nval_nths(t, p)

def mval_msths(xs: List<&2, U.Ms>, q: Nat) -> {U.mval(msths(xs, q)) == nthm(CL.mmap(xs), q) : List<&2, Nat>}:
  match xs q:
    case Nil{} _:
      {==}
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      mval_msths(t, p)

# ---- shape ----

def rsl_length(+d: Nat, +t: A.Tree<U.Nt>, +pf: {A.perfect(U.Nt, d, t) == True{} : Bool}) -> {SC.length(Nat, rsl(t)) == SC.pow2(d) : Nat}:
  Equal.trans(Nat, SC.length(Nat, CL.nmap(A.slots(U.Nt, t))), SC.length(U.Nt, A.slots(U.Nt, t)), SC.pow2(d),
    CL.nmap_length(A.slots(U.Nt, t)), A.slots_length(U.Nt, d, t, pf))

def msl_length(+d: Nat, +t: A.Tree<U.Ms>, +pf: {A.perfect(U.Ms, d, t) == True{} : Bool}) -> {SC.length(List<&2, Nat>, msl(t)) == SC.pow2(d) : Nat}:
  Equal.trans(Nat, SC.length(List<&2, Nat>, CL.mmap(A.slots(U.Ms, t))), SC.length(U.Ms, A.slots(U.Ms, t)), SC.pow2(d),
    CL.mmap_length(A.slots(U.Ms, t)), A.slots_length(U.Ms, d, t, pf))

def idx_ok(+d: Nat, +q: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hq: {Nat.is_lt(q, SC.pow2(d)) == True{} : Bool}) -> {U32.to_nat(U32.from_nat(q)) == q : Nat}:
  U32L.to_nat_from_nat(q, d, N.lt_le(d, 32n, hd), hq)

def slots_lt_n(+d: Nat, +t: A.Tree<U.Nt>, +q: Nat, +pf: {A.perfect(U.Nt, d, t) == True{} : Bool}, +hq: {Nat.is_lt(q, SC.pow2(d)) == True{} : Bool}) -> {Nat.is_lt(q, SC.length(U.Nt, A.slots(U.Nt, t))) == True{} : Bool}:
  L.subst(Nat, k => {Nat.is_lt(q, k) == True{} : Bool}, SC.pow2(d), SC.length(U.Nt, A.slots(U.Nt, t)),
    Equal.sym(Nat, SC.length(U.Nt, A.slots(U.Nt, t)), SC.pow2(d), A.slots_length(U.Nt, d, t, pf)), hq)

def slots_lt_m(+d: Nat, +t: A.Tree<U.Ms>, +q: Nat, +pf: {A.perfect(U.Ms, d, t) == True{} : Bool}, +hq: {Nat.is_lt(q, SC.pow2(d)) == True{} : Bool}) -> {Nat.is_lt(q, SC.length(U.Ms, A.slots(U.Ms, t))) == True{} : Bool}:
  L.subst(Nat, k => {Nat.is_lt(q, k) == True{} : Bool}, SC.pow2(d), SC.length(U.Ms, A.slots(U.Ms, t)),
    Equal.sym(Nat, SC.length(U.Ms, A.slots(U.Ms, t)), SC.pow2(d), A.slots_length(U.Ms, d, t, pf)), hq)

# ---- read ----

def read_nat_ok(+d: Nat, +t: A.Tree<U.Nt>, +q: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hq: {Nat.is_lt(q, SC.pow2(d)) == True{} : Bool}, +pf: {A.perfect(U.Nt, d, t) == True{} : Bool}) -> {U.read_nat(A.thaw(U.Nt, t), d, q) == (A.thaw(U.Nt, t), nthn(rsl(t), q)) : Array<U.Nt> & Nat}:
  %nval_nths(A.slots(U.Nt, t), q) : {U.read_nat(A.thaw(U.Nt, t), d, q) == (A.thaw(U.Nt, t), _) : Array<U.Nt> & Nat}
  Equal.cong(Array<U.Nt> & U.Nt, Array<U.Nt> & Nat, U.read_nat_fin,
    Array.get(U.Nt, A.thaw(U.Nt, t), U32.from_nat(q)),
    (A.thaw(U.Nt, t), nths(A.slots(U.Nt, t), q)),
    A.get(U.Nt, d, t, U32.from_nat(q), nths(A.slots(U.Nt, t), q), hd,
      L.subst(Nat, j => {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, q, U32.to_nat(U32.from_nat(q)), Equal.sym(Nat, U32.to_nat(U32.from_nat(q)), q, idx_ok(d, q, hd, hq)), hq),
      L.subst(Nat, j => {SC.nth(U.Nt, A.slots(U.Nt, t), j) == Some{nths(A.slots(U.Nt, t), q)} : Maybe<&2, U.Nt>}, q, U32.to_nat(U32.from_nat(q)), Equal.sym(Nat, U32.to_nat(U32.from_nat(q)), q, idx_ok(d, q, hd, hq)), nths_nth(A.slots(U.Nt, t), q, slots_lt_n(d, t, q, pf, hq))),
      pf))

def read_ms_ok(+d: Nat, +t: A.Tree<U.Ms>, +q: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hq: {Nat.is_lt(q, SC.pow2(d)) == True{} : Bool}, +pf: {A.perfect(U.Ms, d, t) == True{} : Bool}) -> {U.read_ms(A.thaw(U.Ms, t), d, q) == (A.thaw(U.Ms, t), nthm(msl(t), q)) : Array<U.Ms> & List<&2, Nat>}:
  %mval_msths(A.slots(U.Ms, t), q) : {U.read_ms(A.thaw(U.Ms, t), d, q) == (A.thaw(U.Ms, t), _) : Array<U.Ms> & List<&2, Nat>}
  Equal.cong(Array<U.Ms> & U.Ms, Array<U.Ms> & List<&2, Nat>, U.read_ms_fin,
    Array.get(U.Ms, A.thaw(U.Ms, t), U32.from_nat(q)),
    (A.thaw(U.Ms, t), msths(A.slots(U.Ms, t), q)),
    A.get(U.Ms, d, t, U32.from_nat(q), msths(A.slots(U.Ms, t), q), hd,
      L.subst(Nat, j => {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, q, U32.to_nat(U32.from_nat(q)), Equal.sym(Nat, U32.to_nat(U32.from_nat(q)), q, idx_ok(d, q, hd, hq)), hq),
      L.subst(Nat, j => {SC.nth(U.Ms, A.slots(U.Ms, t), j) == Some{msths(A.slots(U.Ms, t), q)} : Maybe<&2, U.Ms>}, q, U32.to_nat(U32.from_nat(q)), Equal.sym(Nat, U32.to_nat(U32.from_nat(q)), q, idx_ok(d, q, hd, hq)), msths_nth(A.slots(U.Ms, t), q, slots_lt_m(d, t, q, pf, hq))),
      pf))

# ---- write ----

def write_nat_ok(+d: Nat, +t: A.Tree<U.Nt>, +q: Nat, +v: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hq: {Nat.is_lt(q, SC.pow2(d)) == True{} : Bool}, +pf: {A.perfect(U.Nt, d, t) == True{} : Bool}) -> {U.write_nat(A.thaw(U.Nt, t), d, q, v) == A.thaw(U.Nt, A.upd(U.Nt, d, t, q, U.N{v})) : Array<U.Nt>}:
  %idx_ok(d, q, hd, hq) : {U.write_nat(A.thaw(U.Nt, t), d, q, v) == A.thaw(U.Nt, A.upd(U.Nt, d, t, _, U.N{v})) : Array<U.Nt>}
  A.set(U.Nt, d, t, U32.from_nat(q), U.N{v}, nths(A.slots(U.Nt, t), q), hd,
    L.subst(Nat, j => {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, q, U32.to_nat(U32.from_nat(q)), Equal.sym(Nat, U32.to_nat(U32.from_nat(q)), q, idx_ok(d, q, hd, hq)), hq),
    L.subst(Nat, j => {SC.nth(U.Nt, A.slots(U.Nt, t), j) == Some{nths(A.slots(U.Nt, t), q)} : Maybe<&2, U.Nt>}, q, U32.to_nat(U32.from_nat(q)), Equal.sym(Nat, U32.to_nat(U32.from_nat(q)), q, idx_ok(d, q, hd, hq)), nths_nth(A.slots(U.Nt, t), q, slots_lt_n(d, t, q, pf, hq))),
    pf)

def write_ms_ok(+d: Nat, +t: A.Tree<U.Ms>, +q: Nat, +v: List<&2, Nat>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hq: {Nat.is_lt(q, SC.pow2(d)) == True{} : Bool}, +pf: {A.perfect(U.Ms, d, t) == True{} : Bool}) -> {U.write_ms(A.thaw(U.Ms, t), d, q, v) == A.thaw(U.Ms, A.upd(U.Ms, d, t, q, U.M{v})) : Array<U.Ms>}:
  %idx_ok(d, q, hd, hq) : {U.write_ms(A.thaw(U.Ms, t), d, q, v) == A.thaw(U.Ms, A.upd(U.Ms, d, t, _, U.M{v})) : Array<U.Ms>}
  A.set(U.Ms, d, t, U32.from_nat(q), U.M{v}, msths(A.slots(U.Ms, t), q), hd,
    L.subst(Nat, j => {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, q, U32.to_nat(U32.from_nat(q)), Equal.sym(Nat, U32.to_nat(U32.from_nat(q)), q, idx_ok(d, q, hd, hq)), hq),
    L.subst(Nat, j => {SC.nth(U.Ms, A.slots(U.Ms, t), j) == Some{msths(A.slots(U.Ms, t), q)} : Maybe<&2, U.Ms>}, q, U32.to_nat(U32.from_nat(q)), Equal.sym(Nat, U32.to_nat(U32.from_nat(q)), q, idx_ok(d, q, hd, hq)), msths_nth(A.slots(U.Ms, t), q, slots_lt_m(d, t, q, pf, hq))),
    pf)

# ---- the slot lists after a write ----

def nmap_update(xs: List<&2, U.Nt>, q: Nat, +v: Nat) -> {CL.nmap(SC.update(U.Nt, xs, q, U.N{v})) == SC.update(Nat, CL.nmap(xs), q, v) : List<&2, Nat>}:
  match xs q:
    case Nil{} _:
      {==}
    case Con{x, t} 0n:
      {==}
    case Con{+x, +t} 1n+p:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, w => Con{U.nval(x), w},
        CL.nmap(SC.update(U.Nt, t, p, U.N{v})), SC.update(Nat, CL.nmap(t), p, v), nmap_update(t, p, v))

def mmap_update(xs: List<&2, U.Ms>, q: Nat, +v: List<&2, Nat>) -> {CL.mmap(SC.update(U.Ms, xs, q, U.M{v})) == SC.update(List<&2, Nat>, CL.mmap(xs), q, v) : List<&2, List<&2, Nat>>}:
  match xs q:
    case Nil{} _:
      {==}
    case Con{x, t} 0n:
      {==}
    case Con{+x, +t} 1n+p:
      Equal.cong(List<&2, List<&2, Nat>>, List<&2, List<&2, Nat>>, w => Con{U.mval(x), w},
        CL.mmap(SC.update(U.Ms, t, p, U.M{v})), SC.update(List<&2, Nat>, CL.mmap(t), p, v), mmap_update(t, p, v))

def rsl_upd(+d: Nat, +t: A.Tree<U.Nt>, +q: Nat, +v: Nat, +hq: {Nat.is_lt(q, SC.pow2(d)) == True{} : Bool}, +pf: {A.perfect(U.Nt, d, t) == True{} : Bool}) -> {rsl(A.upd(U.Nt, d, t, q, U.N{v})) == SC.update(Nat, rsl(t), q, v) : List<&2, Nat>}:
  Equal.trans(List<&2, Nat>, CL.nmap(A.slots(U.Nt, A.upd(U.Nt, d, t, q, U.N{v}))), CL.nmap(SC.update(U.Nt, A.slots(U.Nt, t), q, U.N{v})), SC.update(Nat, CL.nmap(A.slots(U.Nt, t)), q, v),
    Equal.cong(List<&2, U.Nt>, List<&2, Nat>, CL.nmap, A.slots(U.Nt, A.upd(U.Nt, d, t, q, U.N{v})), SC.update(U.Nt, A.slots(U.Nt, t), q, U.N{v}), A.upd_slots(U.Nt, d, t, q, U.N{v}, hq, pf)),
    nmap_update(A.slots(U.Nt, t), q, v))

def msl_upd(+d: Nat, +t: A.Tree<U.Ms>, +q: Nat, +v: List<&2, Nat>, +hq: {Nat.is_lt(q, SC.pow2(d)) == True{} : Bool}, +pf: {A.perfect(U.Ms, d, t) == True{} : Bool}) -> {msl(A.upd(U.Ms, d, t, q, U.M{v})) == SC.update(List<&2, Nat>, msl(t), q, v) : List<&2, List<&2, Nat>>}:
  Equal.trans(List<&2, List<&2, Nat>>, CL.mmap(A.slots(U.Ms, A.upd(U.Ms, d, t, q, U.M{v}))), CL.mmap(SC.update(U.Ms, A.slots(U.Ms, t), q, U.M{v})), SC.update(List<&2, Nat>, CL.mmap(A.slots(U.Ms, t)), q, v),
    Equal.cong(List<&2, U.Ms>, List<&2, List<&2, Nat>>, CL.mmap, A.slots(U.Ms, A.upd(U.Ms, d, t, q, U.M{v})), SC.update(U.Ms, A.slots(U.Ms, t), q, U.M{v}), A.upd_slots(U.Ms, d, t, q, U.M{v}, hq, pf)),
    mmap_update(A.slots(U.Ms, t), q, v))

# ---- the relinking loop on the roots arena ----

def rtree(ms: List<&2, Nat>, +d: Nat, t: A.Tree<U.Nt>, +big: Nat) -> A.Tree<U.Nt>:
  match ms:
    case Nil{}:
      t
    case Con{+m, rest}:
      rtree(rest, d, A.upd(U.Nt, d, t, m, U.N{big}), big)

def rtree_perfect(ms: List<&2, Nat>, +d: Nat, +t: A.Tree<U.Nt>, +big: Nat, +pf: {A.perfect(U.Nt, d, t) == True{} : Bool}) -> {A.perfect(U.Nt, d, rtree(ms, d, t, big)) == True{} : Bool}:
  match ms:
    case Nil{}:
      pf
    case Con{+m, rest}:
      rtree_perfect(rest, d, A.upd(U.Nt, d, t, m, U.N{big}), big, A.upd_perfect(U.Nt, d, t, m, U.N{big}, pf))

def relink_ok(ms: List<&2, Nat>, +d: Nat, +t: A.Tree<U.Nt>, +big: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +pf: {A.perfect(U.Nt, d, t) == True{} : Bool}, +hb: {M.below(ms, SC.pow2(d)) == True{} : Bool}) -> {U.relink(ms, A.thaw(U.Nt, t), d, big) == A.thaw(U.Nt, rtree(ms, d, t, big)) : Array<U.Nt>}:
  match ms:
    case Nil{}:
      {==}
    case Con{+m, +rest}:
      +hm = L.and_left(Nat.is_lt(m, SC.pow2(d)), M.below(rest, SC.pow2(d)), hb)
      %Equal.sym(Array<U.Nt>, U.write_nat(A.thaw(U.Nt, t), d, m, big), A.thaw(U.Nt, A.upd(U.Nt, d, t, m, U.N{big})), write_nat_ok(d, t, m, big, hd, hm, pf)) : {U.relink(rest, _, d, big) == A.thaw(U.Nt, rtree(Con{m, rest}, d, t, big)) : Array<U.Nt>}
      relink_ok(rest, d, A.upd(U.Nt, d, t, m, U.N{big}), big, hd, A.upd_perfect(U.Nt, d, t, m, U.N{big}, pf), L.and_right(Nat.is_lt(m, SC.pow2(d)), M.below(rest, SC.pow2(d)), hb))

def rsl_rtree(ms: List<&2, Nat>, +d: Nat, +t: A.Tree<U.Nt>, +big: Nat, +pf: {A.perfect(U.Nt, d, t) == True{} : Bool}, +hb: {M.below(ms, SC.pow2(d)) == True{} : Bool}) -> {rsl(rtree(ms, d, t, big)) == CL.rlr(ms, rsl(t), big) : List<&2, Nat>}:
  match ms:
    case Nil{}:
      {==}
    case Con{+m, +rest}:
      +hm = L.and_left(Nat.is_lt(m, SC.pow2(d)), M.below(rest, SC.pow2(d)), hb)
      Equal.trans(List<&2, Nat>, rsl(rtree(rest, d, A.upd(U.Nt, d, t, m, U.N{big}), big)), CL.rlr(rest, rsl(A.upd(U.Nt, d, t, m, U.N{big})), big), CL.rlr(rest, SC.update(Nat, rsl(t), m, big), big),
        rsl_rtree(rest, d, A.upd(U.Nt, d, t, m, U.N{big}), big, A.upd_perfect(U.Nt, d, t, m, U.N{big}, pf), L.and_right(Nat.is_lt(m, SC.pow2(d)), M.below(rest, SC.pow2(d)), hb)),
        Equal.cong(List<&2, Nat>, List<&2, Nat>, w => CL.rlr(rest, w, big), rsl(A.upd(U.Nt, d, t, m, U.N{big})), SC.update(Nat, rsl(t), m, big), rsl_upd(d, t, m, big, hm, pf)))
