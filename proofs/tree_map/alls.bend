import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../spec/common.bend as SC
import ../hash_table/state.bend as HT
import ../lru/state.bend as LST
import ../lru/lists.bend as LS
import ./state.bend as ST
import ./path.bend as P
import ./dj.bend as DJ

# Id lists under an insertion: bounds, lengths and repeats with a new id put
# between the ids before and after the gap, and a free id moved out of the
# free list. (source: tools/generators/tm_hand/alls.src)


def allin_l(+a: List<&2, Nat>, +b: List<&2, Nat>, +n: Nat, +h: {ST.allin(SC.append(Nat, a, b), n) == True{} : Bool}) -> {ST.allin(a, n) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.and_intro(Bool.and(Nat.is_lt(0n, x), Nat.is_le(x, n)), ST.allin(t, n), L.and_left(Bool.and(Nat.is_lt(0n, x), Nat.is_le(x, n)), ST.allin(SC.append(Nat, t, b), n), h), allin_l(t, b, n, L.and_right(Bool.and(Nat.is_lt(0n, x), Nat.is_le(x, n)), ST.allin(SC.append(Nat, t, b), n), h)))

def allin_r(+a: List<&2, Nat>, +b: List<&2, Nat>, +n: Nat, +h: {ST.allin(SC.append(Nat, a, b), n) == True{} : Bool}) -> {ST.allin(b, n) == True{} : Bool}:
  match a:
    case Nil{}:
      h
    case Con{+x, +t}:
      allin_r(t, b, n, L.and_right(Bool.and(Nat.is_lt(0n, x), Nat.is_le(x, n)), ST.allin(SC.append(Nat, t, b), n), h))

def allin_app(+a: List<&2, Nat>, +b: List<&2, Nat>, +n: Nat, +ha: {ST.allin(a, n) == True{} : Bool}, +hb: {ST.allin(b, n) == True{} : Bool}) -> {ST.allin(SC.append(Nat, a, b), n) == True{} : Bool}:
  match a:
    case Nil{}:
      hb
    case Con{+x, +t}:
      L.and_intro(Bool.and(Nat.is_lt(0n, x), Nat.is_le(x, n)), ST.allin(SC.append(Nat, t, b), n), L.and_left(Bool.and(Nat.is_lt(0n, x), Nat.is_le(x, n)), ST.allin(t, n), ha), allin_app(t, b, n, L.and_right(Bool.and(Nat.is_lt(0n, x), Nat.is_le(x, n)), ST.allin(t, n), ha), hb))

def inb_up(+x: Nat, +n: Nat, +h: {Bool.and(Nat.is_lt(0n, x), Nat.is_le(x, n)) == True{} : Bool}) -> {Bool.and(Nat.is_lt(0n, x), Nat.is_le(x, 1n+n)) == True{} : Bool}:
  L.and_intro(Nat.is_lt(0n, x), Nat.is_le(x, 1n+n), L.and_left(Nat.is_lt(0n, x), Nat.is_le(x, n), h), N.le_trans(x, n, 1n+n, L.and_right(Nat.is_lt(0n, x), Nat.is_le(x, n), h), N.le_succ(n)))

def allin_up(+xs: List<&2, Nat>, +n: Nat, +h: {ST.allin(xs, n) == True{} : Bool}) -> {ST.allin(xs, 1n+n) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.and_intro(Bool.and(Nat.is_lt(0n, x), Nat.is_le(x, 1n+n)), ST.allin(t, 1n+n), inb_up(x, n, L.and_left(Bool.and(Nat.is_lt(0n, x), Nat.is_le(x, n)), ST.allin(t, n), h)), allin_up(t, n, L.and_right(Bool.and(Nat.is_lt(0n, x), Nat.is_le(x, n)), ST.allin(t, n), h)))

# an id past the bound is absent
def allin_out(+xs: List<&2, Nat>, +n: Nat, +h: {ST.allin(xs, n) == True{} : Bool}) -> {HT.memn(1n+n, xs) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hx = L.and_right(Nat.is_lt(0n, x), Nat.is_le(x, n), L.and_left(Bool.and(Nat.is_lt(0n, x), Nat.is_le(x, n)), ST.allin(t, n), h))
      DJ.nm_cons(1n+n, x, t, N.is_eq_lt(x, 1n+n, N.le_lt_succ(x, n, hx)), allin_out(t, n, L.and_right(Bool.and(Nat.is_lt(0n, x), Nat.is_le(x, n)), ST.allin(t, n), h)))

def am_c(+x: Nat, +t: List<&2, Nat>, +n: Nat, +y: Nat, +h: {ST.allin(Con{x, t}, n) == True{} : Bool}, +hm: {HT.memn(y, Con{x, t}) == True{} : Bool}, +e: Bool, +he: {Nat.is_eq(x, y) == e : Bool}, ih: @+hmt: {HT.memn(y, t) == True{} : Bool} -> {Bool.and(Nat.is_lt(0n, y), Nat.is_le(y, n)) == True{} : Bool}) -> {Bool.and(Nat.is_lt(0n, y), Nat.is_le(y, n)) == True{} : Bool}:
  match e:
    case True{}:
      L.subst(Nat, z => {Bool.and(Nat.is_lt(0n, z), Nat.is_le(z, n)) == True{} : Bool}, x, y, N.eq_from_is_eq(x, y, he), L.and_left(Bool.and(Nat.is_lt(0n, x), Nat.is_le(x, n)), ST.allin(t, n), h))
    case False{}:
      ih(L.subst(Bool, z => {Bool.or(z, HT.memn(y, t)) == True{} : Bool}, Nat.is_eq(x, y), False{}, he, hm))

# ---- the new id between before and after ----

def nd_put(+b: List<&2, Nat>, +x: Nat, +a: List<&2, Nat>, +h: {LST.nodupn(SC.append(Nat, b, a)) == True{} : Bool}, +hx: {HT.memn(x, SC.append(Nat, b, a)) == False{} : Bool}) -> {LST.nodupn(SC.append(Nat, b, Con{x, a})) == True{} : Bool}:
  L.subst(Bool, w => {w == True{} : Bool}, Bool.and(LST.nodupn(SC.append(Nat, b, a)), Bool.not(HT.memn(x, SC.append(Nat, b, a)))), LST.nodupn(SC.append(Nat, b, Con{x, a})), Equal.sym(Bool, LST.nodupn(SC.append(Nat, b, Con{x, a})), Bool.and(LST.nodupn(SC.append(Nat, b, a)), Bool.not(HT.memn(x, SC.append(Nat, b, a)))), LS.nd_mid(b, x, a)), L.and_intro(LST.nodupn(SC.append(Nat, b, a)), Bool.not(HT.memn(x, SC.append(Nat, b, a))), h, L.subst(Bool, w => {Bool.not(w) == True{} : Bool}, False{}, HT.memn(x, SC.append(Nat, b, a)), Equal.sym(Bool, HT.memn(x, SC.append(Nat, b, a)), False{}, hx), {==})))

def len_put(+b: List<&2, Nat>, +x: Nat, +a: List<&2, Nat>) -> {SC.length(Nat, SC.append(Nat, b, Con{x, a})) == 1n+SC.length(Nat, SC.append(Nat, b, a)) : Nat}:
  P.cons_len(b, x, a)

# a member is within the bound
def allin_mem(+xs: List<&2, Nat>, +n: Nat, +y: Nat, +h: {ST.allin(xs, n) == True{} : Bool}, +hm: {HT.memn(y, xs) == True{} : Bool}) -> {Bool.and(Nat.is_lt(0n, y), Nat.is_le(y, n)) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({Bool.and(Nat.is_lt(0n, y), Nat.is_le(y, n)) == True{} : Bool}, L.false_true(hm))
    case Con{+x, +t}:
      am_c(x, t, n, y, h, hm, Nat.is_eq(x, y), {==}, hmt => allin_mem(t, n, y, L.and_right(Bool.and(Nat.is_lt(0n, x), Nat.is_le(x, n)), ST.allin(t, n), h), hmt))

