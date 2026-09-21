import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../../spec/common.bend as SC
import ../../src/deque.bend as DQ

# List facts behind the ring buffer (src/deque.bend).
#
# The slots of the ring are a list s of c elements; the ring read from offset
# lo is the rotation  rot(s, lo) = drop(s, lo) ++ take(s, lo),  so ring
# position j is list index j of the rotation. The elements of the deque are
# the first len ring positions: take(rot(s, lo), len). The runtime reaches
# ring position j at slot DQ.wrap(lo + j, c) (lo + j reduced mod c), and the
# lemmas below relate that slot arithmetic to plain list positions:
#
#   rot_nth      reading slot wrap(lo + j)  = reading position j
#   rot_update   writing slot wrap(lo + j)  = writing position j
#   rot_step     moving lo one slot right   = rotating by one position
#
# plus the take/snoc/tail/init facts each end operation needs.

def rot(-A: Data, +s: List<&2, A>, +k: Nat) -> List<&2, A>:
  SC.append(A, SC.drop(A, s, k), SC.take(A, s, k))

# ---- arithmetic ----

def wrap_small(+x: Nat, +c: Nat, +h: {Nat.is_lt(x, c) == True{} : Bool}) -> {DQ.wrap(x, c) == x : Nat}:
  L.subst(Bool, z => {DQ.wrap_go(x, c, z) == x : Nat}, True{}, Nat.is_lt(x, c), Equal.sym(Bool, Nat.is_lt(x, c), True{}, h), {==})

def wrap_big(+x: Nat, +c: Nat, +h: {Nat.is_lt(x, c) == False{} : Bool}) -> {DQ.wrap(x, c) == Nat.sub(x, c) : Nat}:
  L.subst(Bool, z => {DQ.wrap_go(x, c, z) == Nat.sub(x, c) : Nat}, False{}, Nat.is_lt(x, c), Equal.sym(Bool, Nat.is_lt(x, c), False{}, h), {==})

# c <= x < 2c: x - c < c
def big_lt(+x: Nat, +c: Nat, +h: {Nat.is_lt(x, c) == False{} : Bool}, +h2: {Nat.is_lt(x, Nat.add(c, c)) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(x, c), c) == True{} : Bool}:
  N.sub_lt(x, c, c, N.not_lt_le(x, c, h), h2)

def wrap_go_lt(+x: Nat, +c: Nat, +h2: {Nat.is_lt(x, Nat.add(c, c)) == True{} : Bool}, b: Bool, +eb: {Nat.is_lt(x, c) == b : Bool}) -> {Nat.is_lt(DQ.wrap(x, c), c) == True{} : Bool}:
  match b:
    case True{}:
      L.subst(Nat, z => {Nat.is_lt(z, c) == True{} : Bool}, x, DQ.wrap(x, c), Equal.sym(Nat, DQ.wrap(x, c), x, wrap_small(x, c, eb)), eb)
    case False{}:
      L.subst(Nat, z => {Nat.is_lt(z, c) == True{} : Bool}, Nat.sub(x, c), DQ.wrap(x, c), Equal.sym(Nat, DQ.wrap(x, c), Nat.sub(x, c), wrap_big(x, c, eb)), big_lt(x, c, eb, h2))

def wrap_lt(+x: Nat, +c: Nat, +h2: {Nat.is_lt(x, Nat.add(c, c)) == True{} : Bool}) -> {Nat.is_lt(DQ.wrap(x, c), c) == True{} : Bool}:
  wrap_go_lt(x, c, h2, Nat.is_lt(x, c), {==})

# lo < c, j <= c: lo + j < 2c
def two_lt(+lo: Nat, +j: Nat, +c: Nat, +hlo: {Nat.is_lt(lo, c) == True{} : Bool}, +hj: {Nat.is_le(j, c) == True{} : Bool}) -> {Nat.is_lt(Nat.add(lo, j), Nat.add(c, c)) == True{} : Bool}:
  +a = N.le_add_left(j, c, lo, hj)
  +b = L.subst(Nat, z => {Nat.is_lt(z, Nat.add(c, c)) == True{} : Bool}, Nat.add(c, lo), Nat.add(lo, c), N.add_comm(c, lo), N.lt_add_left(lo, c, c, hlo))
  N.le_lt_trans(Nat.add(lo, j), Nat.add(lo, c), Nat.add(c, c), a, b)

# ---- drop / take ----

def drop_zero(-A: Data, +xs: List<&2, A>) -> {SC.drop(A, xs, 0n) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

def nth_drop(-A: Data, +xs: List<&2, A>, +k: Nat, +j: Nat) -> {SC.nth(A, SC.drop(A, xs, k), j) == SC.nth(A, xs, Nat.add(k, j)) : Maybe<&2, A>}:
  match xs k:
    case Nil{} _:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{+h, +t} 1n+ +p:
      nth_drop(A, t, p, j)

def length_drop(-A: Data, +xs: List<&2, A>, +k: Nat) -> {SC.length(A, SC.drop(A, xs, k)) == Nat.sub(SC.length(A, xs), k) : Nat}:
  match xs k:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+q:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{+h, +t} 1n+ +p:
      length_drop(A, t, p)

def drop_cons(-A: Data, +xs: List<&2, A>, +k: Nat, +h: A, +e: {SC.nth(A, xs, k) == Some{h} : Maybe<&2, A>}) -> {SC.drop(A, xs, k) == Con{h, SC.drop(A, xs, 1n+k)} : List<&2, A>}:
  match xs k:
    case Nil{} _:
      Empty.absurd({SC.drop(A, Nil{}, k) == Con{h, SC.drop(A, Nil{}, 1n+k)} : List<&2, A>}, L.none_some(A, h, e))
    case Con{+x, +t} 0n:
      %Equal.sym(List<&2, A>, SC.drop(A, t, 0n), t, drop_zero(A, t)) : {Con{x, t} == Con{h, _} : List<&2, A>}
      %L.some_inj(A, x, h, e) : {Con{x, t} == Con{_, t} : List<&2, A>}
      {==}
    case Con{+x, +t} 1n+ +p:
      drop_cons(A, t, p, h, e)

def take_succ_snoc(-A: Data, +xs: List<&2, A>, +k: Nat, +h: A, +e: {SC.nth(A, xs, k) == Some{h} : Maybe<&2, A>}) -> {SC.take(A, xs, 1n+k) == SC.snoc(A, SC.take(A, xs, k), h) : List<&2, A>}:
  match xs k:
    case Nil{} _:
      Empty.absurd({SC.take(A, Nil{}, 1n+k) == SC.snoc(A, SC.take(A, Nil{}, k), h) : List<&2, A>}, L.none_some(A, h, e))
    case Con{+x, +t} 0n:
      %Equal.sym(List<&2, A>, SC.take(A, t, 0n), Nil{}, LL.sc_take_zero(A, t)) : {Con{x, _} == Con{h, Nil{}} : List<&2, A>}
      %L.some_inj(A, x, h, e) : {Con{x, Nil{}} == Con{_, Nil{}} : List<&2, A>}
      {==}
    case Con{+x, +t} 1n+ +p:
      LL.cons_cong(A, x, SC.take(A, t, 1n+p), SC.snoc(A, SC.take(A, t, p), h), take_succ_snoc(A, t, p, h, e))

def take_len(-A: Data, +xs: List<&2, A>) -> {SC.take(A, xs, SC.length(A, xs)) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      LL.cons_cong(A, h, SC.take(A, t, SC.length(A, t)), t, take_len(A, t))

def drop_len(-A: Data, +xs: List<&2, A>) -> {SC.drop(A, xs, SC.length(A, xs)) == Nil{} : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      drop_len(A, t)

def append_nil_r(-A: Data, +xs: List<&2, A>) -> {SC.append(A, xs, Nil{}) == xs : List<&2, A>}:
  LL.append_nil(A, xs)

def rot_zero(-A: Data, +s: List<&2, A>) -> {rot(A, s, 0n) == s : List<&2, A>}:
  %Equal.sym(List<&2, A>, SC.drop(A, s, 0n), s, drop_zero(A, s)) : {SC.append(A, _, SC.take(A, s, 0n)) == s : List<&2, A>}
  %Equal.sym(List<&2, A>, SC.take(A, s, 0n), Nil{}, LL.sc_take_zero(A, s)) : {SC.append(A, s, _) == s : List<&2, A>}
  LL.append_nil(A, s)

# ---- subtraction facts ----

# lo + j < c  ->  j < c - lo
def lt_sub_of_add(+lo: Nat, +j: Nat, +c: Nat, +h: {Nat.is_lt(Nat.add(lo, j), c) == True{} : Bool}) -> {Nat.is_lt(j, Nat.sub(c, lo)) == True{} : Bool}:
  match lo c:
    case 0n _:
      %Equal.sym(Nat, Nat.sub(c, 0n), c, N.sub_zero(c)) : {Nat.is_lt(j, _) == True{} : Bool}
      h
    case 1n+p 0n:
      Empty.absurd({Nat.is_lt(j, Nat.sub(0n, 1n+p)) == True{} : Bool}, L.false_true(h))
    case 1n+ +p 1n+ +q:
      lt_sub_of_add(p, j, q, h)

# c <= lo + j  ->  c - lo <= j
def sub_le_of_le_add(+lo: Nat, +j: Nat, +c: Nat, +h: {Nat.is_le(c, Nat.add(lo, j)) == True{} : Bool}) -> {Nat.is_le(Nat.sub(c, lo), j) == True{} : Bool}:
  match lo c:
    case 0n _:
      %Equal.sym(Nat, Nat.sub(c, 0n), c, N.sub_zero(c)) : {Nat.is_le(_, j) == True{} : Bool}
      h
    case 1n+p 0n:
      N.zero_le(j)
    case 1n+ +p 1n+ +q:
      sub_le_of_le_add(p, j, q, h)

# lo <= c: (lo + j) - c = j - (c - lo)
def sub_shift(+lo: Nat, +j: Nat, +c: Nat, +h: {Nat.is_le(lo, c) == True{} : Bool}) -> {Nat.sub(Nat.add(lo, j), c) == Nat.sub(j, Nat.sub(c, lo)) : Nat}:
  match lo c:
    case 0n _:
      %Equal.sym(Nat, Nat.sub(c, 0n), c, N.sub_zero(c)) : {Nat.sub(j, c) == Nat.sub(j, _) : Nat}
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.sub(Nat.add(1n+p, j), 0n) == Nat.sub(j, Nat.sub(0n, 1n+p)) : Nat}, L.false_true(h))
    case 1n+ +p 1n+ +q:
      sub_shift(p, j, q, h)

# c <= x < c + lo  ->  x - c < lo
def sub_lt_c(+x: Nat, +c: Nat, +lo: Nat, +hc: {Nat.is_le(c, x) == True{} : Bool}, +h: {Nat.is_lt(x, Nat.add(c, lo)) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(x, c), lo) == True{} : Bool}:
  match x c:
    case _ 0n:
      %Equal.sym(Nat, Nat.sub(x, 0n), x, N.sub_zero(x)) : {Nat.is_lt(_, lo) == True{} : Bool}
      h
    case 0n 1n+q:
      Empty.absurd({Nat.is_lt(Nat.sub(0n, 1n+q), lo) == True{} : Bool}, L.false_true(hc))
    case 1n+ +p 1n+ +q:
      sub_lt_c(p, q, lo, hc, h)

# c - lo <= j < c, lo <= c  ->  j - (c - lo) < lo
def sub_sub_lt(+lo: Nat, +j: Nat, +c: Nat, +hl: {Nat.is_le(lo, c) == True{} : Bool}, +hc: {Nat.is_le(c, Nat.add(lo, j)) == True{} : Bool}, +hj: {Nat.is_lt(j, c) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(j, Nat.sub(c, lo)), lo) == True{} : Bool}:
  +e1 = sub_shift(lo, j, c, hl)
  +lt = N.lt_add_left(j, c, lo, hj)
  +lt2 = L.subst(Nat, z => {Nat.is_lt(Nat.add(lo, j), z) == True{} : Bool}, Nat.add(lo, c), Nat.add(c, lo), N.add_comm(lo, c), lt)
  L.subst(Nat, z => {Nat.is_lt(z, lo) == True{} : Bool}, Nat.sub(Nat.add(lo, j), c), Nat.sub(j, Nat.sub(c, lo)), e1, sub_lt_c(Nat.add(lo, j), c, lo, hc, lt2))


# ---- the rotation ----

def rot_len(-A: Data, +s: List<&2, A>, +lo: Nat, +hl: {Nat.is_le(lo, SC.length(A, s)) == True{} : Bool}) -> {SC.length(A, rot(A, s, lo)) == SC.length(A, s) : Nat}:
  %Equal.sym(Nat, SC.length(A, rot(A, s, lo)), Nat.add(SC.length(A, SC.drop(A, s, lo)), SC.length(A, SC.take(A, s, lo))), LL.length_append(A, SC.drop(A, s, lo), SC.take(A, s, lo))) : {_ == SC.length(A, s) : Nat}
  %Equal.sym(Nat, SC.length(A, SC.drop(A, s, lo)), Nat.sub(SC.length(A, s), lo), length_drop(A, s, lo)) : {Nat.add(_, SC.length(A, SC.take(A, s, lo))) == SC.length(A, s) : Nat}
  %Equal.sym(Nat, SC.length(A, SC.take(A, s, lo)), lo, LL.sc_length_take(A, s, lo, hl)) : {Nat.add(Nat.sub(SC.length(A, s), lo), _) == SC.length(A, s) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.sub(SC.length(A, s), lo), lo), Nat.add(lo, Nat.sub(SC.length(A, s), lo)), N.add_comm(Nat.sub(SC.length(A, s), lo), lo)) : {_ == SC.length(A, s) : Nat}
  N.sub_add(SC.length(A, s), lo, hl)

def rot_nth_lo(-A: Data, +s: List<&2, A>, +lo: Nat, +j: Nat, +h: {Nat.is_lt(Nat.add(lo, j), SC.length(A, s)) == True{} : Bool}) -> {SC.nth(A, rot(A, s, lo), j) == SC.nth(A, s, Nat.add(lo, j)) : Maybe<&2, A>}:
  +hj = L.subst(Nat, z => {Nat.is_lt(j, z) == True{} : Bool}, Nat.sub(SC.length(A, s), lo), SC.length(A, SC.drop(A, s, lo)), Equal.sym(Nat, SC.length(A, SC.drop(A, s, lo)), Nat.sub(SC.length(A, s), lo), length_drop(A, s, lo)), lt_sub_of_add(lo, j, SC.length(A, s), h))
  Equal.trans(Maybe<&2, A>, SC.nth(A, rot(A, s, lo), j), SC.nth(A, SC.drop(A, s, lo), j), SC.nth(A, s, Nat.add(lo, j)), LL.nth_append_left(A, SC.drop(A, s, lo), SC.take(A, s, lo), j, hj), nth_drop(A, s, lo, j))

def rot_nth_hi(-A: Data, +s: List<&2, A>, +lo: Nat, +j: Nat, +hl: {Nat.is_le(lo, SC.length(A, s)) == True{} : Bool}, +hc: {Nat.is_le(SC.length(A, s), Nat.add(lo, j)) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.length(A, s)) == True{} : Bool}) -> {SC.nth(A, rot(A, s, lo), j) == SC.nth(A, s, Nat.sub(Nat.add(lo, j), SC.length(A, s))) : Maybe<&2, A>}:
  +c = SC.length(A, s)
  +ld = Equal.sym(Nat, SC.length(A, SC.drop(A, s, lo)), Nat.sub(c, lo), length_drop(A, s, lo))
  +hd = L.subst(Nat, z => {Nat.is_le(z, j) == True{} : Bool}, Nat.sub(c, lo), SC.length(A, SC.drop(A, s, lo)), ld, sub_le_of_le_add(lo, j, c, hc))
  %Equal.sym(Maybe<&2, A>, SC.nth(A, rot(A, s, lo), j), SC.nth(A, SC.take(A, s, lo), Nat.sub(j, SC.length(A, SC.drop(A, s, lo)))), LL.nth_append_right(A, SC.drop(A, s, lo), SC.take(A, s, lo), j, hd)) : {_ == SC.nth(A, s, Nat.sub(Nat.add(lo, j), c)) : Maybe<&2, A>}
  %ld : {SC.nth(A, SC.take(A, s, lo), Nat.sub(j, _)) == SC.nth(A, s, Nat.sub(Nat.add(lo, j), c)) : Maybe<&2, A>}
  %Equal.sym(Maybe<&2, A>, SC.nth(A, SC.take(A, s, lo), Nat.sub(j, Nat.sub(c, lo))), SC.nth(A, s, Nat.sub(j, Nat.sub(c, lo))), LL.sc_nth_take(A, s, lo, Nat.sub(j, Nat.sub(c, lo)), sub_sub_lt(lo, j, c, hl, hc, hj))) : {_ == SC.nth(A, s, Nat.sub(Nat.add(lo, j), c)) : Maybe<&2, A>}
  %Equal.sym(Nat, Nat.sub(Nat.add(lo, j), c), Nat.sub(j, Nat.sub(c, lo)), sub_shift(lo, j, c, hl)) : {SC.nth(A, s, Nat.sub(j, Nat.sub(c, lo))) == SC.nth(A, s, _) : Maybe<&2, A>}
  {==}

def rot_nth_go(-A: Data, +s: List<&2, A>, +lo: Nat, +j: Nat, +hlo: {Nat.is_lt(lo, SC.length(A, s)) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.length(A, s)) == True{} : Bool}, b: Bool, +eb: {Nat.is_lt(Nat.add(lo, j), SC.length(A, s)) == b : Bool}) -> {SC.nth(A, rot(A, s, lo), j) == SC.nth(A, s, DQ.wrap(Nat.add(lo, j), SC.length(A, s))) : Maybe<&2, A>}:
  match b:
    case True{}:
      %Equal.sym(Nat, DQ.wrap(Nat.add(lo, j), SC.length(A, s)), Nat.add(lo, j), wrap_small(Nat.add(lo, j), SC.length(A, s), eb)) : {SC.nth(A, rot(A, s, lo), j) == SC.nth(A, s, _) : Maybe<&2, A>}
      rot_nth_lo(A, s, lo, j, eb)
    case False{}:
      %Equal.sym(Nat, DQ.wrap(Nat.add(lo, j), SC.length(A, s)), Nat.sub(Nat.add(lo, j), SC.length(A, s)), wrap_big(Nat.add(lo, j), SC.length(A, s), eb)) : {SC.nth(A, rot(A, s, lo), j) == SC.nth(A, s, _) : Maybe<&2, A>}
      rot_nth_hi(A, s, lo, j, N.lt_le(lo, SC.length(A, s), hlo), N.not_lt_le(Nat.add(lo, j), SC.length(A, s), eb), hj)

# reading slot wrap(lo + j) is reading ring position j
def rot_nth(-A: Data, +s: List<&2, A>, +lo: Nat, +j: Nat, +hlo: {Nat.is_lt(lo, SC.length(A, s)) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.length(A, s)) == True{} : Bool}) -> {SC.nth(A, rot(A, s, lo), j) == SC.nth(A, s, DQ.wrap(Nat.add(lo, j), SC.length(A, s))) : Maybe<&2, A>}:
  rot_nth_go(A, s, lo, j, hlo, hj, Nat.is_lt(Nat.add(lo, j), SC.length(A, s)), {==})

# ---- updates ----

def update_oob(-A: Data, +xs: List<&2, A>, +i: Nat, +v: A, +h: {Nat.is_le(SC.length(A, xs), i) == True{} : Bool}) -> {SC.update(A, xs, i, v) == xs : List<&2, A>}:
  match xs i:
    case Nil{} _:
      {==}
    case Con{h0, t} 0n:
      Empty.absurd({SC.update(A, Con{h0, t}, 0n, v) == Con{h0, t} : List<&2, A>}, L.false_true(h))
    case Con{+h0, +t} 1n+ +p:
      LL.cons_cong(A, h0, SC.update(A, t, p, v), t, update_oob(A, t, p, v, h))

def drop_update_hi(-A: Data, +xs: List<&2, A>, +k: Nat, +i: Nat, +v: A) -> {SC.drop(A, SC.update(A, xs, Nat.add(k, i), v), k) == SC.update(A, SC.drop(A, xs, k), i, v) : List<&2, A>}:
  match xs k:
    case Nil{} _:
      {==}
    case Con{+h, +t} 0n:
      drop_zero(A, SC.update(A, Con{h, t}, i, v))
    case Con{+h, +t} 1n+ +p:
      drop_update_hi(A, t, p, i, v)

def drop_update_lo(-A: Data, +xs: List<&2, A>, +k: Nat, +i: Nat, +v: A, +h: {Nat.is_lt(i, k) == True{} : Bool}) -> {SC.drop(A, SC.update(A, xs, i, v), k) == SC.drop(A, xs, k) : List<&2, A>}:
  match xs k i:
    case Nil{} _ _:
      {==}
    case Con{h0, t} 0n _:
      Empty.absurd({SC.drop(A, SC.update(A, Con{h0, t}, i, v), 0n) == SC.drop(A, Con{h0, t}, 0n) : List<&2, A>}, N.lt_zero_absurd(i, h))
    case Con{h0, t} 1n+p 0n:
      {==}
    case Con{+h0, +t} 1n+ +p 1n+ +q:
      drop_update_lo(A, t, p, q, v, h)

def rot_update_lo(-A: Data, +s: List<&2, A>, +lo: Nat, +j: Nat, +v: A, +h: {Nat.is_lt(Nat.add(lo, j), SC.length(A, s)) == True{} : Bool}) -> {rot(A, SC.update(A, s, Nat.add(lo, j), v), lo) == SC.update(A, rot(A, s, lo), j, v) : List<&2, A>}:
  +c = SC.length(A, s)
  +hl = N.le_trans(lo, Nat.add(lo, j), c, N.le_add_right(lo, j), N.lt_le(Nat.add(lo, j), c, h))
  +hj = L.subst(Nat, z => {Nat.is_lt(j, z) == True{} : Bool}, Nat.sub(c, lo), SC.length(A, SC.drop(A, s, lo)), Equal.sym(Nat, SC.length(A, SC.drop(A, s, lo)), Nat.sub(c, lo), length_drop(A, s, lo)), lt_sub_of_add(lo, j, c, h))
  +ht = L.subst(Nat, z => {Nat.is_le(z, Nat.add(lo, j)) == True{} : Bool}, lo, SC.length(A, SC.take(A, s, lo)), Equal.sym(Nat, SC.length(A, SC.take(A, s, lo)), lo, LL.sc_length_take(A, s, lo, hl)), N.le_add_right(lo, j))
  %Equal.sym(List<&2, A>, SC.drop(A, SC.update(A, s, Nat.add(lo, j), v), lo), SC.update(A, SC.drop(A, s, lo), j, v), drop_update_hi(A, s, lo, j, v)) : {SC.append(A, _, SC.take(A, SC.update(A, s, Nat.add(lo, j), v), lo)) == SC.update(A, rot(A, s, lo), j, v) : List<&2, A>}
  %Equal.sym(List<&2, A>, SC.take(A, SC.update(A, s, Nat.add(lo, j), v), lo), SC.update(A, SC.take(A, s, lo), Nat.add(lo, j), v), LL.sc_take_update(A, s, Nat.add(lo, j), v, lo)) : {SC.append(A, SC.update(A, SC.drop(A, s, lo), j, v), _) == SC.update(A, rot(A, s, lo), j, v) : List<&2, A>}
  %Equal.sym(List<&2, A>, SC.update(A, SC.take(A, s, lo), Nat.add(lo, j), v), SC.take(A, s, lo), update_oob(A, SC.take(A, s, lo), Nat.add(lo, j), v, ht)) : {SC.append(A, SC.update(A, SC.drop(A, s, lo), j, v), _) == SC.update(A, rot(A, s, lo), j, v) : List<&2, A>}
  Equal.sym(List<&2, A>, SC.update(A, rot(A, s, lo), j, v), SC.append(A, SC.update(A, SC.drop(A, s, lo), j, v), SC.take(A, s, lo)), LL.update_append_left(A, SC.drop(A, s, lo), SC.take(A, s, lo), j, v, hj))

def rot_update_hi(-A: Data, +s: List<&2, A>, +lo: Nat, +j: Nat, +v: A, +hl: {Nat.is_le(lo, SC.length(A, s)) == True{} : Bool}, +hc: {Nat.is_le(SC.length(A, s), Nat.add(lo, j)) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.length(A, s)) == True{} : Bool}) -> {rot(A, SC.update(A, s, Nat.sub(Nat.add(lo, j), SC.length(A, s)), v), lo) == SC.update(A, rot(A, s, lo), j, v) : List<&2, A>}:
  +c = SC.length(A, s)
  +i = Nat.sub(Nat.add(lo, j), c)
  +esh = sub_shift(lo, j, c, hl)
  +hi = L.subst(Nat, z => {Nat.is_lt(z, lo) == True{} : Bool}, Nat.sub(j, Nat.sub(c, lo)), i, Equal.sym(Nat, i, Nat.sub(j, Nat.sub(c, lo)), esh), sub_sub_lt(lo, j, c, hl, hc, hj))
  +ld = length_drop(A, s, lo)
  +hd = L.subst(Nat, z => {Nat.is_le(z, j) == True{} : Bool}, Nat.sub(c, lo), SC.length(A, SC.drop(A, s, lo)), Equal.sym(Nat, SC.length(A, SC.drop(A, s, lo)), Nat.sub(c, lo), ld), sub_le_of_le_add(lo, j, c, hc))
  +ei = Equal.trans(Nat, Nat.sub(j, SC.length(A, SC.drop(A, s, lo))), Nat.sub(j, Nat.sub(c, lo)), i, Equal.cong(Nat, Nat, z => Nat.sub(j, z), SC.length(A, SC.drop(A, s, lo)), Nat.sub(c, lo), ld), Equal.sym(Nat, i, Nat.sub(j, Nat.sub(c, lo)), esh))
  %Equal.sym(List<&2, A>, SC.drop(A, SC.update(A, s, i, v), lo), SC.drop(A, s, lo), drop_update_lo(A, s, lo, i, v, hi)) : {SC.append(A, _, SC.take(A, SC.update(A, s, i, v), lo)) == SC.update(A, rot(A, s, lo), j, v) : List<&2, A>}
  %Equal.sym(List<&2, A>, SC.take(A, SC.update(A, s, i, v), lo), SC.update(A, SC.take(A, s, lo), i, v), LL.sc_take_update(A, s, i, v, lo)) : {SC.append(A, SC.drop(A, s, lo), _) == SC.update(A, rot(A, s, lo), j, v) : List<&2, A>}
  %ei : {SC.append(A, SC.drop(A, s, lo), SC.update(A, SC.take(A, s, lo), _, v)) == SC.update(A, rot(A, s, lo), j, v) : List<&2, A>}
  Equal.sym(List<&2, A>, SC.update(A, rot(A, s, lo), j, v), SC.append(A, SC.drop(A, s, lo), SC.update(A, SC.take(A, s, lo), Nat.sub(j, SC.length(A, SC.drop(A, s, lo))), v)), LL.update_append_right(A, SC.drop(A, s, lo), SC.take(A, s, lo), j, v, hd))

def rot_update_go(-A: Data, +s: List<&2, A>, +lo: Nat, +j: Nat, +v: A, +hlo: {Nat.is_lt(lo, SC.length(A, s)) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.length(A, s)) == True{} : Bool}, b: Bool, +eb: {Nat.is_lt(Nat.add(lo, j), SC.length(A, s)) == b : Bool}) -> {rot(A, SC.update(A, s, DQ.wrap(Nat.add(lo, j), SC.length(A, s)), v), lo) == SC.update(A, rot(A, s, lo), j, v) : List<&2, A>}:
  match b:
    case True{}:
      %Equal.sym(Nat, DQ.wrap(Nat.add(lo, j), SC.length(A, s)), Nat.add(lo, j), wrap_small(Nat.add(lo, j), SC.length(A, s), eb)) : {rot(A, SC.update(A, s, _, v), lo) == SC.update(A, rot(A, s, lo), j, v) : List<&2, A>}
      rot_update_lo(A, s, lo, j, v, eb)
    case False{}:
      %Equal.sym(Nat, DQ.wrap(Nat.add(lo, j), SC.length(A, s)), Nat.sub(Nat.add(lo, j), SC.length(A, s)), wrap_big(Nat.add(lo, j), SC.length(A, s), eb)) : {rot(A, SC.update(A, s, _, v), lo) == SC.update(A, rot(A, s, lo), j, v) : List<&2, A>}
      rot_update_hi(A, s, lo, j, v, N.lt_le(lo, SC.length(A, s), hlo), N.not_lt_le(Nat.add(lo, j), SC.length(A, s), eb), hj)

# writing slot wrap(lo + j) is writing ring position j
def rot_update(-A: Data, +s: List<&2, A>, +lo: Nat, +j: Nat, +v: A, +hlo: {Nat.is_lt(lo, SC.length(A, s)) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.length(A, s)) == True{} : Bool}) -> {rot(A, SC.update(A, s, DQ.wrap(Nat.add(lo, j), SC.length(A, s)), v), lo) == SC.update(A, rot(A, s, lo), j, v) : List<&2, A>}:
  rot_update_go(A, s, lo, j, v, hlo, hj, Nat.is_lt(Nat.add(lo, j), SC.length(A, s)), {==})

# ---- moving the offset one slot right ----

def rot_step_lo(-A: Data, +s: List<&2, A>, +lo: Nat, +h: A, +e: {SC.nth(A, s, lo) == Some{h} : Maybe<&2, A>}) -> {rot(A, s, 1n+lo) == SC.snoc(A, SC.tail(A, rot(A, s, lo)), h) : List<&2, A>}:
  %Equal.sym(List<&2, A>, SC.drop(A, s, lo), Con{h, SC.drop(A, s, 1n+lo)}, drop_cons(A, s, lo, h, e)) : {rot(A, s, 1n+lo) == SC.snoc(A, SC.tail(A, SC.append(A, _, SC.take(A, s, lo))), h) : List<&2, A>}
  %Equal.sym(List<&2, A>, SC.take(A, s, 1n+lo), SC.snoc(A, SC.take(A, s, lo), h), take_succ_snoc(A, s, lo, h, e)) : {SC.append(A, SC.drop(A, s, 1n+lo), _) == SC.snoc(A, SC.append(A, SC.drop(A, s, 1n+lo), SC.take(A, s, lo)), h) : List<&2, A>}
  LL.append_snoc(A, SC.drop(A, s, 1n+lo), SC.take(A, s, lo), h)

def rot_step_wrap(-A: Data, +s: List<&2, A>, +lo: Nat, +h: A, +e: {SC.nth(A, s, lo) == Some{h} : Maybe<&2, A>}, +ec: {1n+lo == SC.length(A, s) : Nat}) -> {rot(A, s, 0n) == SC.snoc(A, SC.tail(A, rot(A, s, lo)), h) : List<&2, A>}:
  +c = SC.length(A, s)
  +edn = Equal.trans(List<&2, A>, SC.drop(A, s, 1n+lo), SC.drop(A, s, c), Nil{}, Equal.cong(Nat, List<&2, A>, z => SC.drop(A, s, z), 1n+lo, c, ec), drop_len(A, s))
  +etk = Equal.trans(List<&2, A>, SC.take(A, s, 1n+lo), SC.take(A, s, c), s, Equal.cong(Nat, List<&2, A>, z => SC.take(A, s, z), 1n+lo, c, ec), take_len(A, s))
  %Equal.sym(List<&2, A>, rot(A, s, 0n), s, rot_zero(A, s)) : {_ == SC.snoc(A, SC.tail(A, rot(A, s, lo)), h) : List<&2, A>}
  %Equal.sym(List<&2, A>, SC.drop(A, s, lo), Con{h, SC.drop(A, s, 1n+lo)}, drop_cons(A, s, lo, h, e)) : {s == SC.snoc(A, SC.tail(A, SC.append(A, _, SC.take(A, s, lo))), h) : List<&2, A>}
  %Equal.sym(List<&2, A>, SC.drop(A, s, 1n+lo), Nil{}, edn) : {s == SC.snoc(A, SC.append(A, _, SC.take(A, s, lo)), h) : List<&2, A>}
  %take_succ_snoc(A, s, lo, h, e) : {s == _ : List<&2, A>}
  Equal.sym(List<&2, A>, SC.take(A, s, 1n+lo), s, etk)

def rot_step_go(-A: Data, +s: List<&2, A>, +lo: Nat, +h: A, +e: {SC.nth(A, s, lo) == Some{h} : Maybe<&2, A>}, +hlo: {Nat.is_lt(lo, SC.length(A, s)) == True{} : Bool}, b: Bool, +eb: {Nat.is_lt(1n+lo, SC.length(A, s)) == b : Bool}) -> {rot(A, s, DQ.wrap(1n+lo, SC.length(A, s))) == SC.snoc(A, SC.tail(A, rot(A, s, lo)), h) : List<&2, A>}:
  match b:
    case True{}:
      %Equal.sym(Nat, DQ.wrap(1n+lo, SC.length(A, s)), 1n+lo, wrap_small(1n+lo, SC.length(A, s), eb)) : {rot(A, s, _) == SC.snoc(A, SC.tail(A, rot(A, s, lo)), h) : List<&2, A>}
      rot_step_lo(A, s, lo, h, e)
    case False{}:
      +ec = N.le_antisym(1n+lo, SC.length(A, s), N.lt_succ_le_succ(lo, SC.length(A, s), hlo), N.not_lt_le(1n+lo, SC.length(A, s), eb))
      +ez = Equal.trans(Nat, Nat.sub(1n+lo, SC.length(A, s)), Nat.sub(1n+lo, 1n+lo), 0n, Equal.cong(Nat, Nat, z => Nat.sub(1n+lo, z), SC.length(A, s), 1n+lo, Equal.sym(Nat, 1n+lo, SC.length(A, s), ec)), N.sub_self(1n+lo))
      %Equal.sym(Nat, DQ.wrap(1n+lo, SC.length(A, s)), Nat.sub(1n+lo, SC.length(A, s)), wrap_big(1n+lo, SC.length(A, s), eb)) : {rot(A, s, _) == SC.snoc(A, SC.tail(A, rot(A, s, lo)), h) : List<&2, A>}
      %Equal.sym(Nat, Nat.sub(1n+lo, SC.length(A, s)), 0n, ez) : {rot(A, s, _) == SC.snoc(A, SC.tail(A, rot(A, s, lo)), h) : List<&2, A>}
      rot_step_wrap(A, s, lo, h, e, ec)

# moving the offset one slot right rotates the ring by one position
def rot_step(-A: Data, +s: List<&2, A>, +lo: Nat, +h: A, +e: {SC.nth(A, s, lo) == Some{h} : Maybe<&2, A>}, +hlo: {Nat.is_lt(lo, SC.length(A, s)) == True{} : Bool}) -> {rot(A, s, DQ.wrap(1n+lo, SC.length(A, s))) == SC.snoc(A, SC.tail(A, rot(A, s, lo)), h) : List<&2, A>}:
  rot_step_go(A, s, lo, h, e, hlo, Nat.is_lt(1n+lo, SC.length(A, s)), {==})

# ---- take / snoc / tail / init / last ----

def take_update_at(-A: Data, +r: List<&2, A>, +n: Nat, +v: A, +h: {Nat.is_lt(n, SC.length(A, r)) == True{} : Bool}) -> {SC.take(A, SC.update(A, r, n, v), 1n+n) == SC.snoc(A, SC.take(A, r, n), v) : List<&2, A>}:
  match r n:
    case Nil{} _:
      Empty.absurd({SC.take(A, SC.update(A, Nil{}, n, v), 1n+n) == SC.snoc(A, SC.take(A, Nil{}, n), v) : List<&2, A>}, N.lt_zero_absurd(n, h))
    case Con{+x, +t} 0n:
      %Equal.sym(List<&2, A>, SC.take(A, t, 0n), Nil{}, LL.sc_take_zero(A, t)) : {Con{v, _} == Con{v, Nil{}} : List<&2, A>}
      {==}
    case Con{+x, +t} 1n+ +p:
      LL.cons_cong(A, x, SC.take(A, SC.update(A, t, p, v), 1n+p), SC.snoc(A, SC.take(A, t, p), v), take_update_at(A, t, p, v, h))

def take_snoc_le(-A: Data, +ys: List<&2, A>, +x: A, +m: Nat, +h: {Nat.is_le(m, SC.length(A, ys)) == True{} : Bool}) -> {SC.take(A, SC.snoc(A, ys, x), m) == SC.take(A, ys, m) : List<&2, A>}:
  match ys m:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+q:
      Empty.absurd({SC.take(A, SC.snoc(A, Nil{}, x), 1n+q) == SC.take(A, Nil{}, 1n+q) : List<&2, A>}, L.false_true(h))
    case Con{h0, t} 0n:
      {==}
    case Con{+h0, +t} 1n+ +p:
      LL.cons_cong(A, h0, SC.take(A, SC.snoc(A, t, x), p), SC.take(A, t, p), take_snoc_le(A, t, x, p, h))

def take_tail(-A: Data, +r: List<&2, A>, +m: Nat) -> {SC.take(A, SC.tail(A, r), m) == SC.tail(A, SC.take(A, r, 1n+m)) : List<&2, A>}:
  match r:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

def init_take_con(-A: Data, +x: A, +t: List<&2, A>, +p: Nat, +h: {Nat.is_le(2n+p, SC.length(A, Con{x, t})) == True{} : Bool}, ih: @+ys: List<&2, A> -> @+hy: {Nat.is_le(1n+p, SC.length(A, ys)) == True{} : Bool} -> {SC.init(A, SC.take(A, ys, 1n+p)) == SC.take(A, ys, p) : List<&2, A>}) -> {SC.init(A, SC.take(A, Con{x, t}, 2n+p)) == SC.take(A, Con{x, t}, 1n+p) : List<&2, A>}:
  match t:
    case Nil{}:
      Empty.absurd({SC.init(A, SC.take(A, Con{x, Nil{}}, 2n+p)) == SC.take(A, Con{x, Nil{}}, 1n+p) : List<&2, A>}, L.false_true(h))
    case Con{+x2, +t2}:
      LL.cons_cong(A, x, SC.init(A, SC.take(A, Con{x2, t2}, 1n+p)), SC.take(A, Con{x2, t2}, p), ih(Con{x2, t2}, h))

def init_take0(-A: Data, +r: List<&2, A>, +h: {Nat.is_le(1n, SC.length(A, r)) == True{} : Bool}) -> {SC.init(A, SC.take(A, r, 1n)) == SC.take(A, r, 0n) : List<&2, A>}:
  match r:
    case Nil{}:
      Empty.absurd({SC.init(A, SC.take(A, Nil{}, 1n)) == SC.take(A, Nil{}, 0n) : List<&2, A>}, L.false_true(h))
    case Con{+x, +t}:
      %Equal.sym(List<&2, A>, SC.take(A, t, 0n), Nil{}, LL.sc_take_zero(A, t)) : {SC.init(A, Con{x, _}) == Nil{} : List<&2, A>}
      {==}

def init_take_s(-A: Data, +r: List<&2, A>, +p: Nat, +h: {Nat.is_le(2n+p, SC.length(A, r)) == True{} : Bool}, ih: @+ys: List<&2, A> -> @+hy: {Nat.is_le(1n+p, SC.length(A, ys)) == True{} : Bool} -> {SC.init(A, SC.take(A, ys, 1n+p)) == SC.take(A, ys, p) : List<&2, A>}) -> {SC.init(A, SC.take(A, r, 2n+p)) == SC.take(A, r, 1n+p) : List<&2, A>}:
  match r:
    case Nil{}:
      Empty.absurd({SC.init(A, SC.take(A, Nil{}, 2n+p)) == SC.take(A, Nil{}, 1n+p) : List<&2, A>}, L.false_true(h))
    case Con{+x, +t}:
      init_take_con(A, x, t, p, h, ih)

def init_take(-A: Data, +m: Nat, +r: List<&2, A>, +h: {Nat.is_le(1n+m, SC.length(A, r)) == True{} : Bool}) -> {SC.init(A, SC.take(A, r, 1n+m)) == SC.take(A, r, m) : List<&2, A>}:
  match m:
    case 0n:
      init_take0(A, r, h)
    case 1n+ +p:
      init_take_s(A, r, p, h, ys => hy => init_take(A, p, ys, hy))

def last_one(-A: Data, +x: A, +t: List<&2, A>, +h: {SC.length(A, Con{x, t}) == 1n : Nat}) -> {SC.last(A, Con{x, t}) == SC.nth(A, Con{x, t}, 0n) : Maybe<&2, A>}:
  match t:
    case Nil{}:
      {==}
    case Con{x2, t2}:
      Empty.absurd({SC.last(A, Con{x, Con{x2, t2}}) == SC.nth(A, Con{x, Con{x2, t2}}, 0n) : Maybe<&2, A>}, N.succ_zero(SC.length(A, t2), N.succ_inj(1n+SC.length(A, t2), 0n, h)))

def last_more(-A: Data, +x: A, +t: List<&2, A>, +p: Nat, +h: {SC.length(A, Con{x, t}) == 2n+p : Nat}, ih: @+ys: List<&2, A> -> @+hy: {SC.length(A, ys) == 1n+p : Nat} -> {SC.last(A, ys) == SC.nth(A, ys, p) : Maybe<&2, A>}) -> {SC.last(A, Con{x, t}) == SC.nth(A, Con{x, t}, 1n+p) : Maybe<&2, A>}:
  match t:
    case Nil{}:
      Empty.absurd({SC.last(A, Con{x, Nil{}}) == SC.nth(A, Con{x, Nil{}}, 1n+p) : Maybe<&2, A>}, N.zero_succ(p, N.succ_inj(0n, 1n+p, h)))
    case Con{+x2, +t2}:
      ih(Con{x2, t2}, N.succ_inj(1n+SC.length(A, t2), 1n+p, h))

def last_nth0(-A: Data, +ys: List<&2, A>, +h: {SC.length(A, ys) == 1n : Nat}) -> {SC.last(A, ys) == SC.nth(A, ys, 0n) : Maybe<&2, A>}:
  match ys:
    case Nil{}:
      Empty.absurd({SC.last(A, Nil{}) == SC.nth(A, Nil{}, 0n) : Maybe<&2, A>}, N.zero_succ(0n, h))
    case Con{+x, +t}:
      last_one(A, x, t, h)

def last_nth_s(-A: Data, +ys: List<&2, A>, +p: Nat, +h: {SC.length(A, ys) == 2n+p : Nat}, ih: @+zs: List<&2, A> -> @+hz: {SC.length(A, zs) == 1n+p : Nat} -> {SC.last(A, zs) == SC.nth(A, zs, p) : Maybe<&2, A>}) -> {SC.last(A, ys) == SC.nth(A, ys, 1n+p) : Maybe<&2, A>}:
  match ys:
    case Nil{}:
      Empty.absurd({SC.last(A, Nil{}) == SC.nth(A, Nil{}, 1n+p) : Maybe<&2, A>}, N.zero_succ(1n+p, h))
    case Con{+x, +t}:
      last_more(A, x, t, p, h, ih)

def last_nth(-A: Data, +m: Nat, +ys: List<&2, A>, +h: {SC.length(A, ys) == 1n+m : Nat}) -> {SC.last(A, ys) == SC.nth(A, ys, m) : Maybe<&2, A>}:
  match m:
    case 0n:
      last_nth0(A, ys, h)
    case 1n+ +p:
      last_nth_s(A, ys, p, h, zs => hz => last_nth(A, p, zs, hz))

def cons_head(-A: Data, +ys: List<&2, A>, +h: A, +e: {SC.nth(A, ys, 0n) == Some{h} : Maybe<&2, A>}) -> {ys == Con{h, SC.tail(A, ys)} : List<&2, A>}:
  match ys:
    case Nil{}:
      Empty.absurd({Nil{} == Con{h, SC.tail(A, Nil{})} : List<&2, A>}, L.none_some(A, h, e))
    case Con{+x, +t}:
      %L.some_inj(A, x, h, e) : {Con{x, t} == Con{_, t} : List<&2, A>}
      {==}
