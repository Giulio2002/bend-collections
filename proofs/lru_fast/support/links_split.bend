# Retained proof dependency: history/retired-doubly-linked-list/proofs/dlist/split.bend
# Only declarations needed by the LRU refinement are kept; no retired runtime is imported.
# Proof-only dependency extracted from retained LRU support; no retired collection API.
import Base
import ../../lib/logic.bend as L
import ../../lib/list.bend as LL
import ../../../spec/common.bend as SC
import links_state.bend as ST
import links_links.bend as LK
import links_items.bend as IT
import links_nbrs.bend as NB
import links_mu0.bend as MU0

def spre_at(b: Bool, +x: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      Nil{}
    case False{}:
      Con{x, rest}


def spre(xs: List<&2, Nat>, +n: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, t}:
      spre_at(Nat.is_eq(x, n), x, spre(t, n))


def spost_at(b: Bool, t: List<&2, Nat>, rest: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      t
    case False{}:
      rest


def spost(xs: List<&2, Nat>, +n: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, +t}:
      spost_at(Nat.is_eq(x, n), t, spost(t, n))


def SpIH(+t: List<&2, Nat>, +n: Nat) -> Type:
  @+hm: {ST.lmem(n, t) == True{} : Bool} -> {t == SC.append(Nat, spre(t, n), Con{n, spost(t, n)}) : List<&2, Nat>}


def split_c(+x: Nat, +t: List<&2, Nat>, +n: Nat, c: Bool, +ec: {Nat.is_eq(x, n) == c : Bool}, +hm: {Bool.or(c, ST.lmem(n, t)) == True{} : Bool}, ih: SpIH(t, n)) -> {Con{x, t} == SC.append(Nat, spre_at(c, x, spre(t, n)), Con{n, spost_at(c, t, spost(t, n))}) : List<&2, Nat>}:
  match c:
    case True{}:
      Equal.cong(Nat, List<&2, Nat>, z => Con{z, t}, x, n, IT.eq_nat_true(x, n, ec))
    case False{}:
      LL.cons_cong(Nat, x, t, SC.append(Nat, spre(t, n), Con{n, spost(t, n)}), ih(hm))


def split_eq(+xs: List<&2, Nat>, +n: Nat, +hm: {ST.lmem(n, xs) == True{} : Bool}) -> {xs == SC.append(Nat, spre(xs, n), Con{n, spost(xs, n)}) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      Empty.absurd({Nil{} == SC.append(Nat, spre(Nil{}, n), Con{n, spost(Nil{}, n)}) : List<&2, Nat>}, NB.lmem_nil(n, hm))
    case Con{+x, +t}:
      split_c(x, t, n, Nat.is_eq(x, n), {==}, hm, hm2 => split_eq(t, n, hm2))

# ---- membership and duplicates across an append ----


def or_assoc(a: Bool, b: Bool, +c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(a, b), c) : Bool}:
  match a b:
    case True{} b0:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}


def lmem_app(+i: Nat, +a: List<&2, Nat>, +b: List<&2, Nat>) -> {ST.lmem(i, SC.append(Nat, a, b)) == Bool.or(ST.lmem(i, a), ST.lmem(i, b)) : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Equal.trans(Bool, Bool.or(Nat.is_eq(x, i), ST.lmem(i, SC.append(Nat, t, b))), Bool.or(Nat.is_eq(x, i), Bool.or(ST.lmem(i, t), ST.lmem(i, b))), Bool.or(Bool.or(Nat.is_eq(x, i), ST.lmem(i, t)), ST.lmem(i, b)),
        Equal.cong(Bool, Bool, z => Bool.or(Nat.is_eq(x, i), z), ST.lmem(i, SC.append(Nat, t, b)), Bool.or(ST.lmem(i, t), ST.lmem(i, b)), lmem_app(i, t, b)),
        or_assoc(Nat.is_eq(x, i), ST.lmem(i, t), ST.lmem(i, b)))


def or_ff(+a: Bool, +b: Bool, +ha: {a == False{} : Bool}, +hb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}:
  L.subst(Bool, z => {Bool.or(z, b) == False{} : Bool}, False{}, a, Equal.sym(Bool, a, False{}, ha), hb)


def nodup_app_l(+a: List<&2, Nat>, +b: List<&2, Nat>, +h: {ST.nodup(SC.append(Nat, a, b)) == True{} : Bool}) -> {ST.nodup(a) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hx = MU0.not_true(ST.lmem(x, SC.append(Nat, t, b)), L.and_left(Bool.not(ST.lmem(x, SC.append(Nat, t, b))), ST.nodup(SC.append(Nat, t, b)), h))
      +hxt = LK.or_false_l(ST.lmem(x, t), ST.lmem(x, b), L.subst(Bool, z => {z == False{} : Bool}, ST.lmem(x, SC.append(Nat, t, b)), Bool.or(ST.lmem(x, t), ST.lmem(x, b)), lmem_app(x, t, b), hx))
      L.and_intro(Bool.not(ST.lmem(x, t)), ST.nodup(t), L.subst(Bool, z => {Bool.not(z) == True{} : Bool}, False{}, ST.lmem(x, t), Equal.sym(Bool, ST.lmem(x, t), False{}, hxt), {==}), nodup_app_l(t, b, L.and_right(Bool.not(ST.lmem(x, SC.append(Nat, t, b))), ST.nodup(SC.append(Nat, t, b)), h)))


def nodup_app_r(+a: List<&2, Nat>, +b: List<&2, Nat>, +h: {ST.nodup(SC.append(Nat, a, b)) == True{} : Bool}) -> {ST.nodup(b) == True{} : Bool}:
  match a:
    case Nil{}:
      h
    case Con{+x, +t}:
      nodup_app_r(t, b, L.and_right(Bool.not(ST.lmem(x, SC.append(Nat, t, b))), ST.nodup(SC.append(Nat, t, b)), h))

# no id of a occurs in b

def disj(a: List<&2, Nat>, +b: List<&2, Nat>) -> Bool:
  match a:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(Bool.not(ST.lmem(x, b)), disj(t, b))


def nodup_disj(+a: List<&2, Nat>, +b: List<&2, Nat>, +h: {ST.nodup(SC.append(Nat, a, b)) == True{} : Bool}) -> {disj(a, b) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hx = MU0.not_true(ST.lmem(x, SC.append(Nat, t, b)), L.and_left(Bool.not(ST.lmem(x, SC.append(Nat, t, b))), ST.nodup(SC.append(Nat, t, b)), h))
      +hxb = LK.or_false_r(ST.lmem(x, t), ST.lmem(x, b), L.subst(Bool, z => {z == False{} : Bool}, ST.lmem(x, SC.append(Nat, t, b)), Bool.or(ST.lmem(x, t), ST.lmem(x, b)), lmem_app(x, t, b), hx))
      L.and_intro(Bool.not(ST.lmem(x, b)), disj(t, b), L.subst(Bool, z => {Bool.not(z) == True{} : Bool}, False{}, ST.lmem(x, b), Equal.sym(Bool, ST.lmem(x, b), False{}, hxb), {==}), nodup_disj(t, b, L.and_right(Bool.not(ST.lmem(x, SC.append(Nat, t, b))), ST.nodup(SC.append(Nat, t, b)), h)))

# an id of b is not in a

def ne_c(+x: Nat, +y: Nat, +b: List<&2, Nat>, +hx: {ST.lmem(x, b) == False{} : Bool}, +hy: {ST.lmem(y, b) == True{} : Bool}, c: Bool, +ec: {Nat.is_eq(x, y) == c : Bool}) -> {Nat.is_eq(x, y) == False{} : Bool}:
  match c:
    case False{}:
      ec
    case True{}:
      Empty.absurd({Nat.is_eq(x, y) == False{} : Bool}, L.false_true(Equal.trans(Bool, False{}, ST.lmem(x, b), True{}, Equal.sym(Bool, ST.lmem(x, b), False{}, hx), L.subst(Nat, z => {ST.lmem(z, b) == True{} : Bool}, y, x, Equal.sym(Nat, x, y, IT.eq_nat_true(x, y, ec)), hy))))


def ne_of_mem(+x: Nat, +y: Nat, +b: List<&2, Nat>, +hx: {ST.lmem(x, b) == False{} : Bool}, +hy: {ST.lmem(y, b) == True{} : Bool}) -> {Nat.is_eq(x, y) == False{} : Bool}:
  ne_c(x, y, b, hx, hy, Nat.is_eq(x, y), {==})


def disj_mem(+a: List<&2, Nat>, +b: List<&2, Nat>, +y: Nat, +h: {disj(a, b) == True{} : Bool}, +hy: {ST.lmem(y, b) == True{} : Bool}) -> {ST.lmem(y, a) == False{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hxb = MU0.not_true(ST.lmem(x, b), L.and_left(Bool.not(ST.lmem(x, b)), disj(t, b), h))
      +hxy = ne_of_mem(x, y, b, hxb, hy)
      or_ff(Nat.is_eq(x, y), ST.lmem(y, t), hxy, disj_mem(t, b, y, L.and_right(Bool.not(ST.lmem(x, b)), disj(t, b), h), hy))

# x not in b and y in b: x != y


def alllt_join(+a: List<&2, Nat>, +b: List<&2, Nat>, +n: Nat, +ha: {ST.alllt(a, n) == True{} : Bool}, +hb: {ST.alllt(b, n) == True{} : Bool}) -> {ST.alllt(SC.append(Nat, a, b), n) == True{} : Bool}:
  match a:
    case Nil{}:
      hb
    case Con{+x, +t}:
      L.and_intro(Nat.is_lt(x, n), ST.alllt(SC.append(Nat, t, b), n), IT.lt_head(x, t, n, ha), alllt_join(t, b, n, IT.lt_tail(x, t, n, ha), hb))


def nodup_cut(+a: List<&2, Nat>, +n: Nat, +b: List<&2, Nat>, +h: {ST.nodup(SC.append(Nat, a, Con{n, b})) == True{} : Bool}) -> {ST.nodup(SC.append(Nat, a, b)) == True{} : Bool}:
  match a:
    case Nil{}:
      L.and_right(Bool.not(ST.lmem(n, b)), ST.nodup(b), h)
    case Con{+x, +t}:
      +hx = MU0.not_true(ST.lmem(x, SC.append(Nat, t, Con{n, b})), L.and_left(Bool.not(ST.lmem(x, SC.append(Nat, t, Con{n, b}))), ST.nodup(SC.append(Nat, t, Con{n, b})), h))
      +h1 = Equal.trans(Bool, Bool.or(ST.lmem(x, t), Bool.or(Nat.is_eq(n, x), ST.lmem(x, b))), ST.lmem(x, SC.append(Nat, t, Con{n, b})), False{}, Equal.sym(Bool, ST.lmem(x, SC.append(Nat, t, Con{n, b})), Bool.or(ST.lmem(x, t), Bool.or(Nat.is_eq(n, x), ST.lmem(x, b))), lmem_app(x, t, Con{n, b})), hx)
      +hxt = LK.or_false_l(ST.lmem(x, t), Bool.or(Nat.is_eq(n, x), ST.lmem(x, b)), h1)
      +hxb = LK.or_false_r(Nat.is_eq(n, x), ST.lmem(x, b), LK.or_false_r(ST.lmem(x, t), Bool.or(Nat.is_eq(n, x), ST.lmem(x, b)), h1))
      +hx2 = Equal.trans(Bool, ST.lmem(x, SC.append(Nat, t, b)), Bool.or(ST.lmem(x, t), ST.lmem(x, b)), False{}, lmem_app(x, t, b), or_ff(ST.lmem(x, t), ST.lmem(x, b), hxt, hxb))
      L.and_intro(Bool.not(ST.lmem(x, SC.append(Nat, t, b))), ST.nodup(SC.append(Nat, t, b)), L.subst(Bool, z => {Bool.not(z) == True{} : Bool}, False{}, ST.lmem(x, SC.append(Nat, t, b)), Equal.sym(Bool, ST.lmem(x, SC.append(Nat, t, b)), False{}, hx2), {==}),
        nodup_cut(t, n, b, L.and_right(Bool.not(ST.lmem(x, SC.append(Nat, t, Con{n, b}))), ST.nodup(SC.append(Nat, t, Con{n, b})), h)))
