import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../spec/common.bend as SC
import ./state.bend as ST
import ./path.bend as P
import ./dj.bend as DJ
import ../lib/nat_list.bend as NL

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
def allin_out(+xs: List<&2, Nat>, +n: Nat, +h: {ST.allin(xs, n) == True{} : Bool}) -> {NL.memn(1n+n, xs) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hx = L.and_right(Nat.is_lt(0n, x), Nat.is_le(x, n), L.and_left(Bool.and(Nat.is_lt(0n, x), Nat.is_le(x, n)), ST.allin(t, n), h))
      DJ.nm_cons(1n+n, x, t, N.is_eq_lt(x, 1n+n, N.le_lt_succ(x, n, hx)), allin_out(t, n, L.and_right(Bool.and(Nat.is_lt(0n, x), Nat.is_le(x, n)), ST.allin(t, n), h)))

def am_c(+x: Nat, +t: List<&2, Nat>, +n: Nat, +y: Nat, +h: {ST.allin(Con{x, t}, n) == True{} : Bool}, +hm: {NL.memn(y, Con{x, t}) == True{} : Bool}, +e: Bool, +he: {Nat.is_eq(x, y) == e : Bool}, ih: @+hmt: {NL.memn(y, t) == True{} : Bool} -> {Bool.and(Nat.is_lt(0n, y), Nat.is_le(y, n)) == True{} : Bool}) -> {Bool.and(Nat.is_lt(0n, y), Nat.is_le(y, n)) == True{} : Bool}:
  match e:
    case True{}:
      L.subst(Nat, z => {Bool.and(Nat.is_lt(0n, z), Nat.is_le(z, n)) == True{} : Bool}, x, y, N.eq_from_is_eq(x, y, he), L.and_left(Bool.and(Nat.is_lt(0n, x), Nat.is_le(x, n)), ST.allin(t, n), h))
    case False{}:
      ih(L.subst(Bool, z => {Bool.or(z, NL.memn(y, t)) == True{} : Bool}, Nat.is_eq(x, y), False{}, he, hm))

# ---- the new id between before and after ----

def nd_put(+b: List<&2, Nat>, +x: Nat, +a: List<&2, Nat>, +h: {NL.nodupn(SC.append(Nat, b, a)) == True{} : Bool}, +hx: {NL.memn(x, SC.append(Nat, b, a)) == False{} : Bool}) -> {NL.nodupn(SC.append(Nat, b, Con{x, a})) == True{} : Bool}:
  L.subst(Bool, w => {w == True{} : Bool}, Bool.and(NL.nodupn(SC.append(Nat, b, a)), Bool.not(NL.memn(x, SC.append(Nat, b, a)))), NL.nodupn(SC.append(Nat, b, Con{x, a})), Equal.sym(Bool, NL.nodupn(SC.append(Nat, b, Con{x, a})), Bool.and(NL.nodupn(SC.append(Nat, b, a)), Bool.not(NL.memn(x, SC.append(Nat, b, a)))), NL.nd_mid(b, x, a)), L.and_intro(NL.nodupn(SC.append(Nat, b, a)), Bool.not(NL.memn(x, SC.append(Nat, b, a))), h, L.subst(Bool, w => {Bool.not(w) == True{} : Bool}, False{}, NL.memn(x, SC.append(Nat, b, a)), Equal.sym(Bool, NL.memn(x, SC.append(Nat, b, a)), False{}, hx), {==})))

def len_put(+b: List<&2, Nat>, +x: Nat, +a: List<&2, Nat>) -> {SC.length(Nat, SC.append(Nat, b, Con{x, a})) == 1n+SC.length(Nat, SC.append(Nat, b, a)) : Nat}:
  P.cons_len(b, x, a)

# a member is within the bound
def allin_mem(+xs: List<&2, Nat>, +n: Nat, +y: Nat, +h: {ST.allin(xs, n) == True{} : Bool}, +hm: {NL.memn(y, xs) == True{} : Bool}) -> {Bool.and(Nat.is_lt(0n, y), Nat.is_le(y, n)) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({Bool.and(Nat.is_lt(0n, y), Nat.is_le(y, n)) == True{} : Bool}, L.false_true(hm))
    case Con{+x, +t}:
      am_c(x, t, n, y, h, hm, Nat.is_eq(x, y), {==}, hmt => allin_mem(t, n, y, L.and_right(Bool.and(Nat.is_lt(0n, x), Nat.is_le(x, n)), ST.allin(t, n), h), hmt))


# ---- a free id moved between before and after ----


def mv_eq(+b: List<&2, Nat>, +a: List<&2, Nat>, +x: Nat, +t: List<&2, Nat>) -> {SC.append(Nat, SC.append(Nat, b, Con{x, a}), t) == SC.append(Nat, b, Con{x, SC.append(Nat, a, t)}) : List<&2, Nat>}:
  LL.append_assoc(Nat, b, Con{x, a}, t)

def nd_move(+b: List<&2, Nat>, +a: List<&2, Nat>, +x: Nat, +t: List<&2, Nat>, +h: {NL.nodupn(SC.append(Nat, SC.append(Nat, b, a), Con{x, t})) == True{} : Bool}) -> {NL.nodupn(SC.append(Nat, SC.append(Nat, b, Con{x, a}), t)) == True{} : Bool}:
  +e0 = NL.nd_mid(SC.append(Nat, b, a), x, t)
  +h0 = L.subst(Bool, w => {w == True{} : Bool}, NL.nodupn(SC.append(Nat, SC.append(Nat, b, a), Con{x, t})), Bool.and(NL.nodupn(SC.append(Nat, SC.append(Nat, b, a), t)), Bool.not(NL.memn(x, SC.append(Nat, SC.append(Nat, b, a), t)))), e0, h)
  +ea = LL.append_assoc(Nat, b, a, t)
  +h1 = L.subst(List<&2, Nat>, z => {Bool.and(NL.nodupn(z), Bool.not(NL.memn(x, z))) == True{} : Bool}, SC.append(Nat, SC.append(Nat, b, a), t), SC.append(Nat, b, SC.append(Nat, a, t)), ea, h0)
  +h2 = L.subst(Bool, w => {w == True{} : Bool}, Bool.and(NL.nodupn(SC.append(Nat, b, SC.append(Nat, a, t))), Bool.not(NL.memn(x, SC.append(Nat, b, SC.append(Nat, a, t))))), NL.nodupn(SC.append(Nat, b, Con{x, SC.append(Nat, a, t)})), Equal.sym(Bool, NL.nodupn(SC.append(Nat, b, Con{x, SC.append(Nat, a, t)})), Bool.and(NL.nodupn(SC.append(Nat, b, SC.append(Nat, a, t))), Bool.not(NL.memn(x, SC.append(Nat, b, SC.append(Nat, a, t))))), NL.nd_mid(b, x, SC.append(Nat, a, t))), h1)
  L.subst(List<&2, Nat>, z => {NL.nodupn(z) == True{} : Bool}, SC.append(Nat, b, Con{x, SC.append(Nat, a, t)}), SC.append(Nat, SC.append(Nat, b, Con{x, a}), t), Equal.sym(List<&2, Nat>, SC.append(Nat, SC.append(Nat, b, Con{x, a}), t), SC.append(Nat, b, Con{x, SC.append(Nat, a, t)}), mv_eq(b, a, x, t)), h2)

def len_move(+b: List<&2, Nat>, +a: List<&2, Nat>, +x: Nat, +t: List<&2, Nat>) -> {SC.length(Nat, SC.append(Nat, SC.append(Nat, b, Con{x, a}), t)) == SC.length(Nat, SC.append(Nat, SC.append(Nat, b, a), Con{x, t})) : Nat}:
  +e1 = L.subst(List<&2, Nat>, z => {SC.length(Nat, SC.append(Nat, SC.append(Nat, b, Con{x, a}), t)) == SC.length(Nat, z) : Nat}, SC.append(Nat, SC.append(Nat, b, Con{x, a}), t), SC.append(Nat, b, Con{x, SC.append(Nat, a, t)}), mv_eq(b, a, x, t), {==})
  +e2 = P.cons_len(b, x, SC.append(Nat, a, t))
  +e3 = P.cons_len(SC.append(Nat, b, a), x, t)
  +e4 = L.subst(List<&2, Nat>, z => {1n+SC.length(Nat, SC.append(Nat, b, SC.append(Nat, a, t))) == 1n+SC.length(Nat, z) : Nat}, SC.append(Nat, b, SC.append(Nat, a, t)), SC.append(Nat, SC.append(Nat, b, a), t), Equal.sym(List<&2, Nat>, SC.append(Nat, SC.append(Nat, b, a), t), SC.append(Nat, b, SC.append(Nat, a, t)), LL.append_assoc(Nat, b, a, t)), {==})
  Equal.trans(Nat, SC.length(Nat, SC.append(Nat, SC.append(Nat, b, Con{x, a}), t)), SC.length(Nat, SC.append(Nat, b, Con{x, SC.append(Nat, a, t)})), SC.length(Nat, SC.append(Nat, SC.append(Nat, b, a), Con{x, t})), e1, Equal.trans(Nat, SC.length(Nat, SC.append(Nat, b, Con{x, SC.append(Nat, a, t)})), 1n+SC.length(Nat, SC.append(Nat, b, SC.append(Nat, a, t))), SC.length(Nat, SC.append(Nat, SC.append(Nat, b, a), Con{x, t})), e2, Equal.trans(Nat, 1n+SC.length(Nat, SC.append(Nat, b, SC.append(Nat, a, t))), 1n+SC.length(Nat, SC.append(Nat, SC.append(Nat, b, a), t)), SC.length(Nat, SC.append(Nat, SC.append(Nat, b, a), Con{x, t})), e4, Equal.sym(Nat, SC.length(Nat, SC.append(Nat, SC.append(Nat, b, a), Con{x, t})), 1n+SC.length(Nat, SC.append(Nat, SC.append(Nat, b, a), t)), e3))))

def allin_move(+b: List<&2, Nat>, +a: List<&2, Nat>, +x: Nat, +t: List<&2, Nat>, +n: Nat, +h: {ST.allin(SC.append(Nat, SC.append(Nat, b, a), Con{x, t}), n) == True{} : Bool}) -> {ST.allin(SC.append(Nat, SC.append(Nat, b, Con{x, a}), t), n) == True{} : Bool}:
  +hba = allin_l(SC.append(Nat, b, a), Con{x, t}, n, h)
  +hxt = allin_r(SC.append(Nat, b, a), Con{x, t}, n, h)
  +hx = L.and_left(Bool.and(Nat.is_lt(0n, x), Nat.is_le(x, n)), ST.allin(t, n), hxt)
  +ht = L.and_right(Bool.and(Nat.is_lt(0n, x), Nat.is_le(x, n)), ST.allin(t, n), hxt)
  allin_app(SC.append(Nat, b, Con{x, a}), t, n, allin_app(b, Con{x, a}, n, allin_l(b, a, n, hba), L.and_intro(Bool.and(Nat.is_lt(0n, x), Nat.is_le(x, n)), ST.allin(a, n), hx, allin_r(b, a, n, hba))), ht)
