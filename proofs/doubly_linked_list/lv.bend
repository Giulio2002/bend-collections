import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../spec/common.bend as SC
import ../spec/doubly_linked_list.bend as S
import ../hash_table/state.bend as HT
import ../lru/lists.bend as LS
import ../lru/dll.bend as DL
import ./state.bend as ST
import ./rel.bend as RL
import ./vals.bend as VA

# Liveness of ids after writes to the value list, and the live and vacant
# id lists under them.


def live_other(-T: Data, +vl: List<&2, Maybe<&2, T>>, +n: Nat, +v: Maybe<&2, T>, +y: Nat, +ne: {Nat.is_eq(n, y) == False{} : Bool}) -> {ST.live(T, SC.update(Maybe<&2, T>, vl, n, v), y) == ST.live(T, vl, y) : Bool}:
  Equal.cong(Maybe<&2, T>, Bool, m => ST.some_b(T, m), S.val_of(T, SC.update(Maybe<&2, T>, vl, n, v), y), S.val_of(T, vl, y), VA.val_upd_other(T, vl, n, y, v, ne))

def live_same(-T: Data, +vl: List<&2, Maybe<&2, T>>, +n: Nat, +v: Maybe<&2, T>, +hl: {Nat.is_lt(n, SC.length(Maybe<&2, T>, vl)) == True{} : Bool}) -> {ST.live(T, SC.update(Maybe<&2, T>, vl, n, v), n) == ST.some_b(T, v) : Bool}:
  Equal.cong(Maybe<&2, T>, Bool, m => ST.some_b(T, m), S.val_of(T, SC.update(Maybe<&2, T>, vl, n, v), n), v, VA.val_upd_same(T, vl, n, v, hl))

def live_c(-T: Data, +vl: List<&2, Maybe<&2, T>>, +n: Nat, +v: Maybe<&2, T>, +y: Nat, +hl: {Nat.is_lt(n, SC.length(Maybe<&2, T>, vl)) == True{} : Bool}, +hv: {ST.some_b(T, v) == True{} : Bool}, +h: {ST.live(T, vl, y) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(n, y) == c : Bool}) -> {ST.live(T, SC.update(Maybe<&2, T>, vl, n, v), y) == True{} : Bool}:
  match c:
    case True{}:
      L.subst(Nat, z => {ST.live(T, SC.update(Maybe<&2, T>, vl, n, v), z) == True{} : Bool}, n, y, N.eq_from_is_eq(n, y, hc), RL.by_eq(ST.live(T, SC.update(Maybe<&2, T>, vl, n, v), n), ST.some_b(T, v), live_same(T, vl, n, v, hl), hv))
    case False{}:
      RL.by_eq(ST.live(T, SC.update(Maybe<&2, T>, vl, n, v), y), ST.live(T, vl, y), live_other(T, vl, n, v, y, hc), h)

# a live value written anywhere keeps the live ids live
def slok_upd(~T: Data, +xs: List<&2, Nat>, +fr: Nat, +vl: List<&2, Maybe<&2, T>>, +n: Nat, +v: Maybe<&2, T>, +hl: {Nat.is_lt(n, SC.length(Maybe<&2, T>, vl)) == True{} : Bool}, +hv: {ST.some_b(T, v) == True{} : Bool}, +h: {ST.slok(~T, xs, fr, vl) == True{} : Bool}) -> {ST.slok(~T, xs, fr, SC.update(Maybe<&2, T>, vl, n, v)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +h0 = L.and_left(Bool.and(Nat.is_lt(x, fr), ST.live(T, vl, x)), ST.slok(~T, t, fr, vl), h)
      +h1 = L.and_right(Bool.and(Nat.is_lt(x, fr), ST.live(T, vl, x)), ST.slok(~T, t, fr, vl), h)
      +hx = L.and_intro(Nat.is_lt(x, fr), ST.live(T, SC.update(Maybe<&2, T>, vl, n, v), x), L.and_left(Nat.is_lt(x, fr), ST.live(T, vl, x), h0), live_c(T, vl, n, v, x, hl, hv, L.and_right(Nat.is_lt(x, fr), ST.live(T, vl, x), h0), Nat.is_eq(n, x), {==}))
      L.and_intro(Bool.and(Nat.is_lt(x, fr), ST.live(T, SC.update(Maybe<&2, T>, vl, n, v), x)), ST.slok(~T, t, fr, SC.update(Maybe<&2, T>, vl, n, v)), hx, slok_upd(~T, t, fr, vl, n, v, hl, hv, h1))

def ne_hd(+x: Nat, +n: Nat, +t: List<&2, Nat>, +h: {HT.memn(n, Con{x, t}) == False{} : Bool}) -> {Nat.is_eq(n, x) == False{} : Bool}:
  DL.ne_sym(x, n, DL.or_ff_l(Nat.is_eq(x, n), HT.memn(n, t), h))

def ne_tl(+x: Nat, +n: Nat, +t: List<&2, Nat>, +h: {HT.memn(n, Con{x, t}) == False{} : Bool}) -> {HT.memn(n, t) == False{} : Bool}:
  DL.or_ff_r(Nat.is_eq(x, n), HT.memn(n, t), h)

# a write off the ids keeps them as they were
def slok_off(~T: Data, +xs: List<&2, Nat>, +fr: Nat, +vl: List<&2, Maybe<&2, T>>, +n: Nat, +v: Maybe<&2, T>, +hn: {HT.memn(n, xs) == False{} : Bool}, +h: {ST.slok(~T, xs, fr, vl) == True{} : Bool}) -> {ST.slok(~T, xs, fr, SC.update(Maybe<&2, T>, vl, n, v)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +h0 = L.and_left(Bool.and(Nat.is_lt(x, fr), ST.live(T, vl, x)), ST.slok(~T, t, fr, vl), h)
      +h1 = L.and_right(Bool.and(Nat.is_lt(x, fr), ST.live(T, vl, x)), ST.slok(~T, t, fr, vl), h)
      +hx = RL.by_eq(Bool.and(Nat.is_lt(x, fr), ST.live(T, SC.update(Maybe<&2, T>, vl, n, v), x)), Bool.and(Nat.is_lt(x, fr), ST.live(T, vl, x)), Equal.cong(Bool, Bool, z => Bool.and(Nat.is_lt(x, fr), z), ST.live(T, SC.update(Maybe<&2, T>, vl, n, v), x), ST.live(T, vl, x), live_other(T, vl, n, v, x, ne_hd(x, n, t, hn))), h0)
      L.and_intro(Bool.and(Nat.is_lt(x, fr), ST.live(T, SC.update(Maybe<&2, T>, vl, n, v), x)), ST.slok(~T, t, fr, SC.update(Maybe<&2, T>, vl, n, v)), hx, slok_off(~T, t, fr, vl, n, v, ne_tl(x, n, t, hn), h1))

def flok_off(~T: Data, +xs: List<&2, Nat>, +fr: Nat, +vl: List<&2, Maybe<&2, T>>, +n: Nat, +v: Maybe<&2, T>, +hn: {HT.memn(n, xs) == False{} : Bool}, +h: {ST.flok(~T, xs, fr, vl) == True{} : Bool}) -> {ST.flok(~T, xs, fr, SC.update(Maybe<&2, T>, vl, n, v)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +h0 = L.and_left(Bool.and(Nat.is_lt(x, fr), Bool.not(ST.live(T, vl, x))), ST.flok(~T, t, fr, vl), h)
      +h1 = L.and_right(Bool.and(Nat.is_lt(x, fr), Bool.not(ST.live(T, vl, x))), ST.flok(~T, t, fr, vl), h)
      +hx = RL.by_eq(Bool.and(Nat.is_lt(x, fr), Bool.not(ST.live(T, SC.update(Maybe<&2, T>, vl, n, v), x))), Bool.and(Nat.is_lt(x, fr), Bool.not(ST.live(T, vl, x))), Equal.cong(Bool, Bool, z => Bool.and(Nat.is_lt(x, fr), Bool.not(z)), ST.live(T, SC.update(Maybe<&2, T>, vl, n, v), x), ST.live(T, vl, x), live_other(T, vl, n, v, x, ne_hd(x, n, t, hn))), h0)
      L.and_intro(Bool.and(Nat.is_lt(x, fr), Bool.not(ST.live(T, SC.update(Maybe<&2, T>, vl, n, v), x))), ST.flok(~T, t, fr, SC.update(Maybe<&2, T>, vl, n, v)), hx, flok_off(~T, t, fr, vl, n, v, ne_tl(x, n, t, hn), h1))

# a larger bound
def slok_mono(~T: Data, +xs: List<&2, Nat>, +fr: Nat, +fr2: Nat, +vl: List<&2, Maybe<&2, T>>, +hle: {Nat.is_le(fr, fr2) == True{} : Bool}, +h: {ST.slok(~T, xs, fr, vl) == True{} : Bool}) -> {ST.slok(~T, xs, fr2, vl) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +h0 = L.and_left(Bool.and(Nat.is_lt(x, fr), ST.live(T, vl, x)), ST.slok(~T, t, fr, vl), h)
      +h1 = L.and_right(Bool.and(Nat.is_lt(x, fr), ST.live(T, vl, x)), ST.slok(~T, t, fr, vl), h)
      +hx = L.and_intro(Nat.is_lt(x, fr2), ST.live(T, vl, x), N.lt_le_trans(x, fr, fr2, L.and_left(Nat.is_lt(x, fr), ST.live(T, vl, x), h0), hle), L.and_right(Nat.is_lt(x, fr), ST.live(T, vl, x), h0))
      L.and_intro(Bool.and(Nat.is_lt(x, fr2), ST.live(T, vl, x)), ST.slok(~T, t, fr2, vl), hx, slok_mono(~T, t, fr, fr2, vl, hle, h1))

def flok_mono(~T: Data, +xs: List<&2, Nat>, +fr: Nat, +fr2: Nat, +vl: List<&2, Maybe<&2, T>>, +hle: {Nat.is_le(fr, fr2) == True{} : Bool}, +h: {ST.flok(~T, xs, fr, vl) == True{} : Bool}) -> {ST.flok(~T, xs, fr2, vl) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +h0 = L.and_left(Bool.and(Nat.is_lt(x, fr), Bool.not(ST.live(T, vl, x))), ST.flok(~T, t, fr, vl), h)
      +h1 = L.and_right(Bool.and(Nat.is_lt(x, fr), Bool.not(ST.live(T, vl, x))), ST.flok(~T, t, fr, vl), h)
      +hx = L.and_intro(Nat.is_lt(x, fr2), Bool.not(ST.live(T, vl, x)), N.lt_le_trans(x, fr, fr2, L.and_left(Nat.is_lt(x, fr), Bool.not(ST.live(T, vl, x)), h0), hle), L.and_right(Nat.is_lt(x, fr), Bool.not(ST.live(T, vl, x)), h0))
      L.and_intro(Bool.and(Nat.is_lt(x, fr2), Bool.not(ST.live(T, vl, x))), ST.flok(~T, t, fr2, vl), hx, flok_mono(~T, t, fr, fr2, vl, hle, h1))

# a vacant id is on no list of live ids
def vac_c(-T: Data, +x: Nat, +y: Nat, +vl: List<&2, Maybe<&2, T>>, +hx: {ST.live(T, vl, x) == False{} : Bool}, +hy: {ST.live(T, vl, y) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(y, x) == c : Bool}, +m: Bool, +ih: {m == False{} : Bool}) -> {Bool.or(c, m) == False{} : Bool}:
  match c:
    case True{}:
      +hy2 = L.subst(Nat, z => {ST.live(T, vl, z) == True{} : Bool}, y, x, N.eq_from_is_eq(y, x, hc), hy)
      Empty.absurd({Bool.or(True{}, m) == False{} : Bool}, L.true_not_false(ST.live(T, vl, x), hy2, hx))
    case False{}:
      ih

def vac_ns(~T: Data, +x: Nat, +xs: List<&2, Nat>, +fr: Nat, +vl: List<&2, Maybe<&2, T>>, +hx: {ST.live(T, vl, x) == False{} : Bool}, +h: {ST.slok(~T, xs, fr, vl) == True{} : Bool}) -> {HT.memn(x, xs) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      +h0 = L.and_left(Bool.and(Nat.is_lt(y, fr), ST.live(T, vl, y)), ST.slok(~T, t, fr, vl), h)
      +h1 = L.and_right(Bool.and(Nat.is_lt(y, fr), ST.live(T, vl, y)), ST.slok(~T, t, fr, vl), h)
      vac_c(T, x, y, vl, hx, L.and_right(Nat.is_lt(y, fr), ST.live(T, vl, y), h0), Nat.is_eq(y, x), {==}, HT.memn(x, t), vac_ns(~T, x, t, fr, vl, hx, h1))

# the last id of a (a ++ b live) is off a vacant list
def lin_vac(~T: Data, +a: List<&2, Nat>, +b: List<&2, Nat>, +fr: Nat, +vl: List<&2, Maybe<&2, T>>, +fl: List<&2, Nat>, +hs: {ST.slok(~T, SC.append(Nat, a, b), fr, vl) == True{} : Bool}, +hf: {ST.flok(~T, fl, fr, vl) == True{} : Bool}) -> {RL.lastin(a, fl) == False{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+a0, +t}:
      +z = DL.lastn(t, a0)
      +hm = LS.mem_app_l(z, Con{a0, t}, b, DL.lastn_mem(t, a0))
      RL.live_nf(~T, z, fl, fr, vl, L.and_right(Nat.is_lt(z, fr), ST.live(T, vl, z), RL.slok_mem(~T, z, SC.append(Nat, Con{a0, t}, b), fr, vl, hs, hm)), hf)
