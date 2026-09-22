import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/array.bend as AR
import ../graph/shift.bend as SH
import ../../spec/common.bend as SC
import ../../src/doubly_linked_list.bend as D
import ./state.bend as ST

# The link invariant `lk` under arena updates and list surgery.

# ---- Booleans ----

def and_assoc3(a: Bool, b: Bool, c: Bool, +d: Bool) -> {Bool.and(a, Bool.and(b, Bool.and(c, d))) == Bool.and(Bool.and(a, Bool.and(b, c)), d) : Bool}:
  match a b c:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} c0:
      {==}
    case False{} b0 c0:
      {==}

def or_false_l(+a: Bool, +b: Bool, +h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, L.false_true(Equal.sym(Bool, True{}, False{}, h)))
    case False{}:
      {==}

def or_false_r(+a: Bool, +b: Bool, +h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({b == False{} : Bool}, L.false_true(Equal.sym(Bool, True{}, False{}, h)))
    case False{}:
      h

# ---- reading after an update ----

def lat_same(+xs: List<&2, U32>, +p: Nat, +v: U32, +h: {Nat.is_lt(p, SC.length(U32, xs)) == True{} : Bool}) -> {ST.lat(SC.update(U32, xs, p, v), p) == v : U32}:
  Equal.cong(Maybe<&2, U32>, U32, m => L.some_value(U32, m, 0), SC.nth(U32, SC.update(U32, xs, p, v), p), Some{v}, LL.nth_update_same(U32, xs, p, v, h))

def lat_other(+xs: List<&2, U32>, +j: Nat, +v: U32, +p: Nat, +h: {Nat.is_eq(j, p) == False{} : Bool}) -> {ST.lat(SC.update(U32, xs, j, v), p) == ST.lat(xs, p) : U32}:
  Equal.cong(Maybe<&2, U32>, U32, m => L.some_value(U32, m, 0), SC.nth(U32, SC.update(U32, xs, j, v), p), SC.nth(U32, xs, p), LL.nth_update_other(U32, xs, j, p, v, h))

def vat_same(-T: Data, +xs: List<&2, Maybe<&2, T>>, +p: Nat, +v: Maybe<&2, T>, +h: {Nat.is_lt(p, SC.length(Maybe<&2, T>, xs)) == True{} : Bool}) -> {ST.vat(T, SC.update(Maybe<&2, T>, xs, p, v), p) == v : Maybe<&2, T>}:
  Equal.cong(Maybe<&2, Maybe<&2, T>>, Maybe<&2, T>, m => ST.flat(T, m), SC.nth(Maybe<&2, T>, SC.update(Maybe<&2, T>, xs, p, v), p), Some{v}, LL.nth_update_same(Maybe<&2, T>, xs, p, v, h))

def vat_other(-T: Data, +xs: List<&2, Maybe<&2, T>>, +j: Nat, +v: Maybe<&2, T>, +p: Nat, +h: {Nat.is_eq(j, p) == False{} : Bool}) -> {ST.vat(T, SC.update(Maybe<&2, T>, xs, j, v), p) == ST.vat(T, xs, p) : Maybe<&2, T>}:
  Equal.cong(Maybe<&2, Maybe<&2, T>>, Maybe<&2, T>, m => ST.flat(T, m), SC.nth(Maybe<&2, T>, SC.update(Maybe<&2, T>, xs, j, v), p), SC.nth(Maybe<&2, T>, xs, p), LL.nth_update_other(Maybe<&2, T>, xs, j, p, v, h))

# ---- lk ignores updates away from its ids ----

def lk_frame_p(+xs: List<&2, Nat>, +pv: U32, +e: U32, +ps: List<&2, U32>, +ns: List<&2, U32>, +j: Nat, +v: U32, +hj: {ST.lmem(j, xs) == False{} : Bool}) -> {ST.lk(xs, pv, e, SC.update(U32, ps, j, v), ns) == ST.lk(xs, pv, e, ps, ns) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hx = or_false_l(Nat.is_eq(x, j), ST.lmem(j, t), hj)
      +ht = or_false_r(Nat.is_eq(x, j), ST.lmem(j, t), hj)
      +e1 = Equal.cong(U32, Bool, z => Bool.and(U32.is_eq(z, pv), Bool.and(U32.is_eq(ST.lat(ns, x), ST.hd_or(t, e)), ST.lk(t, ST.ln(x), e, SC.update(U32, ps, j, v), ns))), ST.lat(SC.update(U32, ps, j, v), x), ST.lat(ps, x), lat_other(ps, j, v, x, SH.ne_flip(x, j, hx)))
      Equal.trans(Bool, Bool.and(U32.is_eq(ST.lat(SC.update(U32, ps, j, v), x), pv), Bool.and(U32.is_eq(ST.lat(ns, x), ST.hd_or(t, e)), ST.lk(t, ST.ln(x), e, SC.update(U32, ps, j, v), ns))), Bool.and(U32.is_eq(ST.lat(ps, x), pv), Bool.and(U32.is_eq(ST.lat(ns, x), ST.hd_or(t, e)), ST.lk(t, ST.ln(x), e, SC.update(U32, ps, j, v), ns))), ST.lk(Con{x, t}, pv, e, ps, ns),
        e1,
        Equal.cong(Bool, Bool, z => Bool.and(U32.is_eq(ST.lat(ps, x), pv), Bool.and(U32.is_eq(ST.lat(ns, x), ST.hd_or(t, e)), z)), ST.lk(t, ST.ln(x), e, SC.update(U32, ps, j, v), ns), ST.lk(t, ST.ln(x), e, ps, ns), lk_frame_p(t, ST.ln(x), e, ps, ns, j, v, ht)))

def lk_frame_n(+xs: List<&2, Nat>, +pv: U32, +e: U32, +ps: List<&2, U32>, +ns: List<&2, U32>, +j: Nat, +v: U32, +hj: {ST.lmem(j, xs) == False{} : Bool}) -> {ST.lk(xs, pv, e, ps, SC.update(U32, ns, j, v)) == ST.lk(xs, pv, e, ps, ns) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hx = or_false_l(Nat.is_eq(x, j), ST.lmem(j, t), hj)
      +ht = or_false_r(Nat.is_eq(x, j), ST.lmem(j, t), hj)
      +e1 = Equal.cong(U32, Bool, z => Bool.and(U32.is_eq(ST.lat(ps, x), pv), Bool.and(U32.is_eq(z, ST.hd_or(t, e)), ST.lk(t, ST.ln(x), e, ps, SC.update(U32, ns, j, v)))), ST.lat(SC.update(U32, ns, j, v), x), ST.lat(ns, x), lat_other(ns, j, v, x, SH.ne_flip(x, j, hx)))
      Equal.trans(Bool, Bool.and(U32.is_eq(ST.lat(ps, x), pv), Bool.and(U32.is_eq(ST.lat(SC.update(U32, ns, j, v), x), ST.hd_or(t, e)), ST.lk(t, ST.ln(x), e, ps, SC.update(U32, ns, j, v)))), Bool.and(U32.is_eq(ST.lat(ps, x), pv), Bool.and(U32.is_eq(ST.lat(ns, x), ST.hd_or(t, e)), ST.lk(t, ST.ln(x), e, ps, SC.update(U32, ns, j, v)))), ST.lk(Con{x, t}, pv, e, ps, ns),
        e1,
        Equal.cong(Bool, Bool, z => Bool.and(U32.is_eq(ST.lat(ps, x), pv), Bool.and(U32.is_eq(ST.lat(ns, x), ST.hd_or(t, e)), z)), ST.lk(t, ST.ln(x), e, ps, SC.update(U32, ns, j, v)), ST.lk(t, ST.ln(x), e, ps, ns), lk_frame_n(t, ST.ln(x), e, ps, ns, j, v, ht)))

# ---- lk over an append ----

# the link to the last id of a, or pv when a is empty
def lastl(a: List<&2, Nat>, +pv: U32) -> U32:
  match a:
    case Nil{}:
      pv
    case Con{+x, t}:
      ST.ln(ST.lst_or(t, x))

def hd_or_app(+t: List<&2, Nat>, +b: List<&2, Nat>, +e: U32) -> {ST.hd_or(SC.append(Nat, t, b), e) == ST.hd_or(t, ST.hd_or(b, e)) : U32}:
  match t:
    case Nil{}:
      {==}
    case Con{+y, +r}:
      {==}

def lastl_cons(+x: Nat, +t: List<&2, Nat>, +pv: U32) -> {lastl(t, ST.ln(x)) == lastl(Con{x, t}, pv) : U32}:
  match t:
    case Nil{}:
      {==}
    case Con{+y, +r}:
      {==}

def lk_app(+a: List<&2, Nat>, +b: List<&2, Nat>, +pv: U32, +e: U32, +ps: List<&2, U32>, +ns: List<&2, U32>) -> {ST.lk(SC.append(Nat, a, b), pv, e, ps, ns) == Bool.and(ST.lk(a, pv, ST.hd_or(b, e), ps, ns), ST.lk(b, lastl(a, pv), e, ps, ns)) : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +pa = U32.is_eq(ST.lat(ps, x), pv)
      +nb = U32.is_eq(ST.lat(ns, x), ST.hd_or(SC.append(Nat, t, b), e))
      +nb2 = U32.is_eq(ST.lat(ns, x), ST.hd_or(t, ST.hd_or(b, e)))
      +c = ST.lk(t, ST.ln(x), ST.hd_or(b, e), ps, ns)
      +dd = ST.lk(b, lastl(t, ST.ln(x)), e, ps, ns)
      +e1 = Equal.cong(Bool, Bool, z => Bool.and(pa, Bool.and(nb, z)), ST.lk(SC.append(Nat, t, b), ST.ln(x), e, ps, ns), Bool.and(c, dd), lk_app(t, b, ST.ln(x), e, ps, ns))
      +e2 = Equal.cong(U32, Bool, z => Bool.and(pa, Bool.and(U32.is_eq(ST.lat(ns, x), z), Bool.and(c, dd))), ST.hd_or(SC.append(Nat, t, b), e), ST.hd_or(t, ST.hd_or(b, e)), hd_or_app(t, b, e))
      +e3 = and_assoc3(pa, nb2, c, dd)
      +e4 = Equal.cong(U32, Bool, z => Bool.and(Bool.and(pa, Bool.and(nb2, c)), ST.lk(b, z, e, ps, ns)), lastl(t, ST.ln(x)), lastl(Con{x, t}, pv), lastl_cons(x, t, pv))
      Equal.trans(Bool, Bool.and(pa, Bool.and(nb, ST.lk(SC.append(Nat, t, b), ST.ln(x), e, ps, ns))), Bool.and(pa, Bool.and(nb, Bool.and(c, dd))), Bool.and(Bool.and(pa, Bool.and(nb2, c)), ST.lk(b, lastl(Con{x, t}, pv), e, ps, ns)), e1,
        Equal.trans(Bool, Bool.and(pa, Bool.and(nb, Bool.and(c, dd))), Bool.and(pa, Bool.and(nb2, Bool.and(c, dd))), Bool.and(Bool.and(pa, Bool.and(nb2, c)), ST.lk(b, lastl(Con{x, t}, pv), e, ps, ns)), e2,
          Equal.trans(Bool, Bool.and(pa, Bool.and(nb2, Bool.and(c, dd))), Bool.and(Bool.and(pa, Bool.and(nb2, c)), dd), Bool.and(Bool.and(pa, Bool.and(nb2, c)), ST.lk(b, lastl(Con{x, t}, pv), e, ps, ns)), e3, e4)))
