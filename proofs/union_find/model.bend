import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../../spec/common.bend as SC
import ../../spec/union_find.bend as S
import ../../src/union_find.bend as U
import ./cells.bend as CL

# List-level model of the union-find cells (cl = the vector's slot list).
#   rt(cl, x)    representative stored for x
#   labs(cl, n)  labels of 0 .. n-1 (the abstraction)
#   good         every x < n: rt x < n, rt (rt x) = rt x, and every
#                representative r lists exactly its class as members (all
#                < n) and stores its exact class size

def lc(cl: List<&2, CL.Cell>, +x: Nat) -> CL.Cell:
  CL.cell_of(SC.nth(CL.Cell, cl, x), x)

def rt(cl: List<&2, CL.Cell>, +x: Nat) -> Nat:
  CL.croot(lc(cl, x))

def sz(cl: List<&2, CL.Cell>, +x: Nat) -> Nat:
  CL.csize(lc(cl, x))

def ms(cl: List<&2, CL.Cell>, +x: Nat) -> List<&2, Nat>:
  CL.cmembers(lc(cl, x))

def labs(+cl: List<&2, CL.Cell>, n: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+ +k:
      SC.snoc(Nat, labs(cl, k), rt(cl, k))

def elem(m: List<&2, Nat>, +y: Nat) -> Bool:
  match m:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(Nat.is_eq(h, y), elem(t, y))

def below(m: List<&2, Nat>, +n: Nat) -> Bool:
  match m:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(Nat.is_lt(h, n), below(t, n))

def beq(a: Bool, b: Bool) -> Bool:
  match a b:
    case True{} True{}:
      True{}
    case False{} False{}:
      True{}
    case True{} False{}:
      False{}
    case False{} True{}:
      False{}

def cnt_r(+cl: List<&2, CL.Cell>, +r: Nat, k: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+ +j:
      Nat.add(cnt_r(cl, r, j), S.eq_bit(Nat.is_eq(rt(cl, j), r)))

def cnt_fix(+cl: List<&2, CL.Cell>, k: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+ +j:
      Nat.add(cnt_fix(cl, j), S.eq_bit(Nat.is_eq(rt(cl, j), j)))

def mem_ok(+cl: List<&2, CL.Cell>, +r: Nat, +m: List<&2, Nat>, k: Nat) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n+ +j:
      Bool.and(mem_ok(cl, r, m, j), beq(elem(m, j), Nat.is_eq(rt(cl, j), r)))

def root_ok(isr: Bool, +cl: List<&2, CL.Cell>, +n: Nat, +y: Nat) -> Bool:
  match isr:
    case False{}:
      True{}
    case True{}:
      Bool.and(below(ms(cl, y), n), Bool.and(mem_ok(cl, y, ms(cl, y), n), Nat.is_eq(sz(cl, y), cnt_r(cl, y, n))))

def good_at(+cl: List<&2, CL.Cell>, +n: Nat, +y: Nat) -> Bool:
  Bool.and(Nat.is_lt(rt(cl, y), n), Bool.and(Nat.is_eq(rt(cl, rt(cl, y)), rt(cl, y)), root_ok(Nat.is_eq(rt(cl, y), y), cl, n, y)))

def good(+cl: List<&2, CL.Cell>, +n: Nat, k: Nat) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n+ +j:
      Bool.and(good(cl, n, j), good_at(cl, n, j))

# ---- Bool helpers ----

def beq_eq(+a: Bool, +b: Bool, +h: {beq(a, b) == True{} : Bool}) -> {a == b : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case False{} False{}:
      {==}
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, L.false_true(h))
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, L.false_true(h))

def beq_refl(+a: Bool) -> {beq(a, a) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def beq_of(+a: Bool, +b: Bool, +e: {a == b : Bool}) -> {beq(a, b) == True{} : Bool}:
  %e : {beq(a, _) == True{} : Bool}
  beq_refl(a)

def eq_true(+a: Nat, +b: Nat, +e: {a == b : Nat}) -> {Nat.is_eq(a, b) == True{} : Bool}:
  %e : {Nat.is_eq(a, _) == True{} : Bool}
  N.is_eq_refl(a)

def is_eq_sym(+a: Nat, +b: Nat) -> {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      is_eq_sym(p, q)

# is_eq(a, c) is False when a == b and b != c.
def neq_trans(+a: Nat, +b: Nat, +c: Nat, +e: {a == b : Nat}, +ne: {Nat.is_eq(b, c) == False{} : Bool}) -> {Nat.is_eq(a, c) == False{} : Bool}:
  %Equal.sym(Nat, a, b, e) : {Nat.is_eq(_, c) == False{} : Bool}
  ne

# ---- eliminating the invariant ----

def elim_case(+cl: List<&2, CL.Cell>, +n: Nat, +j: Nat, +y: Nat, b: Bool, +eb: {Nat.is_eq(y, j) == b : Bool}, +g1: {good(cl, n, j) == True{} : Bool}, +g2: {good_at(cl, n, j) == True{} : Bool}, +hy: {Nat.is_lt(y, 1n+j) == True{} : Bool}, ih: @+h2: {Nat.is_lt(y, j) == True{} : Bool} -> {good_at(cl, n, y) == True{} : Bool}) -> {good_at(cl, n, y) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Nat, y, j, N.eq_from_is_eq(y, j, eb)) : {good_at(cl, n, _) == True{} : Bool}
      g2
    case False{}:
      ih(N.lt_or_eq(y, j, N.lt_succ_le(y, j, hy), eb))

def good_elim(+cl: List<&2, CL.Cell>, +n: Nat, +k: Nat, +y: Nat, +g: {good(cl, n, k) == True{} : Bool}, +hy: {Nat.is_lt(y, k) == True{} : Bool}) -> {good_at(cl, n, y) == True{} : Bool}:
  match k:
    case 0n:
      Empty.absurd({good_at(cl, n, y) == True{} : Bool}, N.lt_zero_absurd(y, hy))
    case 1n+ +j:
      +g1 = L.and_left(good(cl, n, j), good_at(cl, n, j), g)
      +g2 = L.and_right(good(cl, n, j), good_at(cl, n, j), g)
      elim_case(cl, n, j, y, Nat.is_eq(y, j), {==}, g1, g2, hy, h2 => good_elim(cl, n, j, y, g1, h2))

def at_lt(+cl: List<&2, CL.Cell>, +n: Nat, +y: Nat, +g: {good_at(cl, n, y) == True{} : Bool}) -> {Nat.is_lt(rt(cl, y), n) == True{} : Bool}:
  L.and_left(Nat.is_lt(rt(cl, y), n), Bool.and(Nat.is_eq(rt(cl, rt(cl, y)), rt(cl, y)), root_ok(Nat.is_eq(rt(cl, y), y), cl, n, y)), g)

def at_rest(+cl: List<&2, CL.Cell>, +n: Nat, +y: Nat, +g: {good_at(cl, n, y) == True{} : Bool}) -> {Bool.and(Nat.is_eq(rt(cl, rt(cl, y)), rt(cl, y)), root_ok(Nat.is_eq(rt(cl, y), y), cl, n, y)) == True{} : Bool}:
  L.and_right(Nat.is_lt(rt(cl, y), n), Bool.and(Nat.is_eq(rt(cl, rt(cl, y)), rt(cl, y)), root_ok(Nat.is_eq(rt(cl, y), y), cl, n, y)), g)

def at_idem(+cl: List<&2, CL.Cell>, +n: Nat, +y: Nat, +g: {good_at(cl, n, y) == True{} : Bool}) -> {rt(cl, rt(cl, y)) == rt(cl, y) : Nat}:
  N.eq_from_is_eq(rt(cl, rt(cl, y)), rt(cl, y), L.and_left(Nat.is_eq(rt(cl, rt(cl, y)), rt(cl, y)), root_ok(Nat.is_eq(rt(cl, y), y), cl, n, y), at_rest(cl, n, y, g)))

def at_root(+cl: List<&2, CL.Cell>, +n: Nat, +y: Nat, +g: {good_at(cl, n, y) == True{} : Bool}, +isr: {Nat.is_eq(rt(cl, y), y) == True{} : Bool}) -> {root_ok(True{}, cl, n, y) == True{} : Bool}:
  %isr : {root_ok(_, cl, n, y) == True{} : Bool}
  L.and_right(Nat.is_eq(rt(cl, rt(cl, y)), rt(cl, y)), root_ok(Nat.is_eq(rt(cl, y), y), cl, n, y), at_rest(cl, n, y, g))

def root_below(+cl: List<&2, CL.Cell>, +n: Nat, +y: Nat, +h: {root_ok(True{}, cl, n, y) == True{} : Bool}) -> {below(ms(cl, y), n) == True{} : Bool}:
  L.and_left(below(ms(cl, y), n), Bool.and(mem_ok(cl, y, ms(cl, y), n), Nat.is_eq(sz(cl, y), cnt_r(cl, y, n))), h)

def root_mem(+cl: List<&2, CL.Cell>, +n: Nat, +y: Nat, +h: {root_ok(True{}, cl, n, y) == True{} : Bool}) -> {mem_ok(cl, y, ms(cl, y), n) == True{} : Bool}:
  L.and_left(mem_ok(cl, y, ms(cl, y), n), Nat.is_eq(sz(cl, y), cnt_r(cl, y, n)), L.and_right(below(ms(cl, y), n), Bool.and(mem_ok(cl, y, ms(cl, y), n), Nat.is_eq(sz(cl, y), cnt_r(cl, y, n))), h))

def root_size(+cl: List<&2, CL.Cell>, +n: Nat, +y: Nat, +h: {root_ok(True{}, cl, n, y) == True{} : Bool}) -> {sz(cl, y) == cnt_r(cl, y, n) : Nat}:
  N.eq_from_is_eq(sz(cl, y), cnt_r(cl, y, n), L.and_right(mem_ok(cl, y, ms(cl, y), n), Nat.is_eq(sz(cl, y), cnt_r(cl, y, n)), L.and_right(below(ms(cl, y), n), Bool.and(mem_ok(cl, y, ms(cl, y), n), Nat.is_eq(sz(cl, y), cnt_r(cl, y, n))), h)))

def root_mk(+cl: List<&2, CL.Cell>, +n: Nat, +y: Nat, +a: {below(ms(cl, y), n) == True{} : Bool}, +b: {mem_ok(cl, y, ms(cl, y), n) == True{} : Bool}, +c: {sz(cl, y) == cnt_r(cl, y, n) : Nat}) -> {root_ok(True{}, cl, n, y) == True{} : Bool}:
  L.and_intro(below(ms(cl, y), n), Bool.and(mem_ok(cl, y, ms(cl, y), n), Nat.is_eq(sz(cl, y), cnt_r(cl, y, n))), a, L.and_intro(mem_ok(cl, y, ms(cl, y), n), Nat.is_eq(sz(cl, y), cnt_r(cl, y, n)), b, eq_true(sz(cl, y), cnt_r(cl, y, n), c)))

def mem_case(+cl: List<&2, CL.Cell>, +r: Nat, +m: List<&2, Nat>, +j: Nat, +y: Nat, b: Bool, +eb: {Nat.is_eq(y, j) == b : Bool}, +h2: {beq(elem(m, j), Nat.is_eq(rt(cl, j), r)) == True{} : Bool}, +hy: {Nat.is_lt(y, 1n+j) == True{} : Bool}, ih: @+q: {Nat.is_lt(y, j) == True{} : Bool} -> {elem(m, y) == Nat.is_eq(rt(cl, y), r) : Bool}) -> {elem(m, y) == Nat.is_eq(rt(cl, y), r) : Bool}:
  match b:
    case True{}:
      %Equal.sym(Nat, y, j, N.eq_from_is_eq(y, j, eb)) : {elem(m, _) == Nat.is_eq(rt(cl, _), r) : Bool}
      beq_eq(elem(m, j), Nat.is_eq(rt(cl, j), r), h2)
    case False{}:
      ih(N.lt_or_eq(y, j, N.lt_succ_le(y, j, hy), eb))

def mem_elim(+cl: List<&2, CL.Cell>, +r: Nat, +m: List<&2, Nat>, +k: Nat, +y: Nat, +h: {mem_ok(cl, r, m, k) == True{} : Bool}, +hy: {Nat.is_lt(y, k) == True{} : Bool}) -> {elem(m, y) == Nat.is_eq(rt(cl, y), r) : Bool}:
  match k:
    case 0n:
      Empty.absurd({elem(m, y) == Nat.is_eq(rt(cl, y), r) : Bool}, N.lt_zero_absurd(y, hy))
    case 1n+ +j:
      +h1 = L.and_left(mem_ok(cl, r, m, j), beq(elem(m, j), Nat.is_eq(rt(cl, j), r)), h)
      +h2 = L.and_right(mem_ok(cl, r, m, j), beq(elem(m, j), Nat.is_eq(rt(cl, j), r)), h)
      mem_case(cl, r, m, j, y, Nat.is_eq(y, j), {==}, h2, hy, q => mem_elim(cl, r, m, j, y, h1, q))

def bel_case(+x: Nat, +t: List<&2, Nat>, +n: Nat, +y: Nat, b: Bool, +eb: {Nat.is_eq(x, y) == b : Bool}, +h: {below(Con{x, t}, n) == True{} : Bool}, +hy: {elem(Con{x, t}, y) == True{} : Bool}, ih: @+q: {elem(t, y) == True{} : Bool} -> {Nat.is_lt(y, n) == True{} : Bool}) -> {Nat.is_lt(y, n) == True{} : Bool}:
  match b:
    case True{}:
      %N.eq_from_is_eq(x, y, eb) : {Nat.is_lt(_, n) == True{} : Bool}
      L.and_left(Nat.is_lt(x, n), below(t, n), h)
    case False{}:
      ih(L.subst(Bool, q => {Bool.or(q, elem(t, y)) == True{} : Bool}, Nat.is_eq(x, y), False{}, eb, hy))

def below_elim(+m: List<&2, Nat>, +n: Nat, +y: Nat, +h: {below(m, n) == True{} : Bool}, +hy: {elem(m, y) == True{} : Bool}) -> {Nat.is_lt(y, n) == True{} : Bool}:
  match m:
    case Nil{}:
      Empty.absurd({Nat.is_lt(y, n) == True{} : Bool}, L.false_true(hy))
    case Con{x, t}:
      bel_case(x, t, n, y, Nat.is_eq(x, y), {==}, h, hy, q => below_elim(t, n, y, L.and_right(Nat.is_lt(x, n), below(t, n), h), q))

# ---- the abstraction ----

def length_labs(+cl: List<&2, CL.Cell>, +n: Nat) -> {SC.length(Nat, labs(cl, n)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+ +k:
      %Equal.sym(Nat, SC.length(Nat, SC.snoc(Nat, labs(cl, k), rt(cl, k))), 1n+SC.length(Nat, labs(cl, k)), LL.length_snoc(Nat, labs(cl, k), rt(cl, k))) : {_ == 1n+k : Nat}
      N.succ_cong(SC.length(Nat, labs(cl, k)), k, length_labs(cl, k))

def nth_snoc_lt(-A: Data, +xs: List<&2, A>, +x: A, +i: Nat, +h: {Nat.is_lt(i, SC.length(A, xs)) == True{} : Bool}) -> {SC.nth(A, SC.snoc(A, xs, x), i) == SC.nth(A, xs, i) : Maybe<&2, A>}:
  %Equal.sym(List<&2, A>, SC.snoc(A, xs, x), SC.append(A, xs, Con{x, Nil{}}), LL.snoc_append(A, xs, x)) : {SC.nth(A, _, i) == SC.nth(A, xs, i) : Maybe<&2, A>}
  LL.nth_append_left(A, xs, Con{x, Nil{}}, i, h)

def nth_snoc_at(-A: Data, +xs: List<&2, A>, +x: A) -> {SC.nth(A, SC.snoc(A, xs, x), SC.length(A, xs)) == Some{x} : Maybe<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      nth_snoc_at(A, t, x)

def nl_case(+cl: List<&2, CL.Cell>, +k: Nat, +x: Nat, b: Bool, +eb: {Nat.is_eq(x, k) == b : Bool}, +h: {Nat.is_lt(x, 1n+k) == True{} : Bool}, ih: @+q: {Nat.is_lt(x, k) == True{} : Bool} -> {SC.nth(Nat, labs(cl, k), x) == Some{rt(cl, x)} : Maybe<&2, Nat>}) -> {SC.nth(Nat, SC.snoc(Nat, labs(cl, k), rt(cl, k)), x) == Some{rt(cl, x)} : Maybe<&2, Nat>}:
  match b:
    case True{}:
      %Equal.sym(Nat, x, k, N.eq_from_is_eq(x, k, eb)) : {SC.nth(Nat, SC.snoc(Nat, labs(cl, k), rt(cl, k)), _) == Some{rt(cl, _)} : Maybe<&2, Nat>}
      %length_labs(cl, k) : {SC.nth(Nat, SC.snoc(Nat, labs(cl, k), rt(cl, k)), _) == Some{rt(cl, k)} : Maybe<&2, Nat>}
      nth_snoc_at(Nat, labs(cl, k), rt(cl, k))
    case False{}:
      +hx = N.lt_or_eq(x, k, N.lt_succ_le(x, k, h), eb)
      Equal.trans(Maybe<&2, Nat>, SC.nth(Nat, SC.snoc(Nat, labs(cl, k), rt(cl, k)), x), SC.nth(Nat, labs(cl, k), x), Some{rt(cl, x)},
        nth_snoc_lt(Nat, labs(cl, k), rt(cl, k), x, L.subst(Nat, q => {Nat.is_lt(x, q) == True{} : Bool}, k, SC.length(Nat, labs(cl, k)), Equal.sym(Nat, SC.length(Nat, labs(cl, k)), k, length_labs(cl, k)), hx)),
        ih(hx))

def nth_labs(+cl: List<&2, CL.Cell>, +n: Nat, +x: Nat, +h: {Nat.is_lt(x, n) == True{} : Bool}) -> {SC.nth(Nat, labs(cl, n), x) == Some{rt(cl, x)} : Maybe<&2, Nat>}:
  match n:
    case 0n:
      Empty.absurd({SC.nth(Nat, Nil{}, x) == Some{rt(cl, x)} : Maybe<&2, Nat>}, N.lt_zero_absurd(x, h))
    case 1n+ +k:
      nl_case(cl, k, x, Nat.is_eq(x, k), {==}, h, q => nth_labs(cl, k, x, q))

def nth_labs_out(+cl: List<&2, CL.Cell>, +n: Nat, +x: Nat, +h: {Nat.is_lt(x, n) == False{} : Bool}) -> {SC.nth(Nat, labs(cl, n), x) == None{} : Maybe<&2, Nat>}:
  LL.nth_none(Nat, labs(cl, n), x, L.subst(Nat, q => {Nat.is_le(q, x) == True{} : Bool}, n, SC.length(Nat, labs(cl, n)), Equal.sym(Nat, SC.length(Nat, labs(cl, n)), n, length_labs(cl, n)), N.not_lt_le(x, n, h)))

def count_eq_snoc(+xs: List<&2, Nat>, +x: Nat, +v: Nat) -> {S.count_eq(SC.snoc(Nat, xs, x), v) == Nat.add(S.count_eq(xs, v), S.eq_bit(Nat.is_eq(x, v))) : Nat}:
  match xs:
    case Nil{}:
      N.add_zero(S.eq_bit(Nat.is_eq(x, v)))
    case Con{h, t}:
      %Equal.sym(Nat, S.count_eq(SC.snoc(Nat, t, x), v), Nat.add(S.count_eq(t, v), S.eq_bit(Nat.is_eq(x, v))), count_eq_snoc(t, x, v)) : {Nat.add(S.eq_bit(Nat.is_eq(h, v)), _) == Nat.add(Nat.add(S.eq_bit(Nat.is_eq(h, v)), S.count_eq(t, v)), S.eq_bit(Nat.is_eq(x, v))) : Nat}
      Equal.sym(Nat, Nat.add(Nat.add(S.eq_bit(Nat.is_eq(h, v)), S.count_eq(t, v)), S.eq_bit(Nat.is_eq(x, v))), Nat.add(S.eq_bit(Nat.is_eq(h, v)), Nat.add(S.count_eq(t, v), S.eq_bit(Nat.is_eq(x, v)))), N.add_assoc(S.eq_bit(Nat.is_eq(h, v)), S.count_eq(t, v), S.eq_bit(Nat.is_eq(x, v))))

def count_labs(+cl: List<&2, CL.Cell>, +v: Nat, +n: Nat) -> {S.count_eq(labs(cl, n), v) == cnt_r(cl, v, n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+ +k:
      %Equal.sym(Nat, S.count_eq(SC.snoc(Nat, labs(cl, k), rt(cl, k)), v), Nat.add(S.count_eq(labs(cl, k), v), S.eq_bit(Nat.is_eq(rt(cl, k), v))), count_eq_snoc(labs(cl, k), rt(cl, k), v)) : {_ == Nat.add(cnt_r(cl, v, k), S.eq_bit(Nat.is_eq(rt(cl, k), v))) : Nat}
      %Equal.sym(Nat, S.count_eq(labs(cl, k), v), cnt_r(cl, v, k), count_labs(cl, v, k)) : {Nat.add(_, S.eq_bit(Nat.is_eq(rt(cl, k), v))) == Nat.add(cnt_r(cl, v, k), S.eq_bit(Nat.is_eq(rt(cl, k), v))) : Nat}
      {==}

def fixed_snoc(+xs: List<&2, Nat>, +x: Nat, +off: Nat) -> {S.fixed(SC.snoc(Nat, xs, x), off) == Nat.add(S.fixed(xs, off), S.eq_bit(Nat.is_eq(x, Nat.add(SC.length(Nat, xs), off)))) : Nat}:
  match xs:
    case Nil{}:
      N.add_zero(S.eq_bit(Nat.is_eq(x, off)))
    case Con{h, t}:
      %Equal.sym(Nat, S.fixed(SC.snoc(Nat, t, x), 1n+off), Nat.add(S.fixed(t, 1n+off), S.eq_bit(Nat.is_eq(x, Nat.add(SC.length(Nat, t), 1n+off)))), fixed_snoc(t, x, 1n+off)) : {Nat.add(S.eq_bit(Nat.is_eq(h, off)), _) == Nat.add(Nat.add(S.eq_bit(Nat.is_eq(h, off)), S.fixed(t, 1n+off)), S.eq_bit(Nat.is_eq(x, 1n+Nat.add(SC.length(Nat, t), off)))) : Nat}
      %Equal.sym(Nat, Nat.add(SC.length(Nat, t), 1n+off), 1n+Nat.add(SC.length(Nat, t), off), N.add_succ(SC.length(Nat, t), off)) : {Nat.add(S.eq_bit(Nat.is_eq(h, off)), Nat.add(S.fixed(t, 1n+off), S.eq_bit(Nat.is_eq(x, _)))) == Nat.add(Nat.add(S.eq_bit(Nat.is_eq(h, off)), S.fixed(t, 1n+off)), S.eq_bit(Nat.is_eq(x, 1n+Nat.add(SC.length(Nat, t), off)))) : Nat}
      Equal.sym(Nat, Nat.add(Nat.add(S.eq_bit(Nat.is_eq(h, off)), S.fixed(t, 1n+off)), S.eq_bit(Nat.is_eq(x, 1n+Nat.add(SC.length(Nat, t), off)))), Nat.add(S.eq_bit(Nat.is_eq(h, off)), Nat.add(S.fixed(t, 1n+off), S.eq_bit(Nat.is_eq(x, 1n+Nat.add(SC.length(Nat, t), off))))), N.add_assoc(S.eq_bit(Nat.is_eq(h, off)), S.fixed(t, 1n+off), S.eq_bit(Nat.is_eq(x, 1n+Nat.add(SC.length(Nat, t), off)))))

def fixed_labs(+cl: List<&2, CL.Cell>, +n: Nat) -> {S.fixed(labs(cl, n), 0n) == cnt_fix(cl, n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+ +k:
      %Equal.sym(Nat, S.fixed(SC.snoc(Nat, labs(cl, k), rt(cl, k)), 0n), Nat.add(S.fixed(labs(cl, k), 0n), S.eq_bit(Nat.is_eq(rt(cl, k), Nat.add(SC.length(Nat, labs(cl, k)), 0n)))), fixed_snoc(labs(cl, k), rt(cl, k), 0n)) : {_ == Nat.add(cnt_fix(cl, k), S.eq_bit(Nat.is_eq(rt(cl, k), k))) : Nat}
      %Equal.sym(Nat, Nat.add(SC.length(Nat, labs(cl, k)), 0n), SC.length(Nat, labs(cl, k)), N.add_zero(SC.length(Nat, labs(cl, k)))) : {Nat.add(S.fixed(labs(cl, k), 0n), S.eq_bit(Nat.is_eq(rt(cl, k), _))) == Nat.add(cnt_fix(cl, k), S.eq_bit(Nat.is_eq(rt(cl, k), k))) : Nat}
      %Equal.sym(Nat, SC.length(Nat, labs(cl, k)), k, length_labs(cl, k)) : {Nat.add(S.fixed(labs(cl, k), 0n), S.eq_bit(Nat.is_eq(rt(cl, k), _))) == Nat.add(cnt_fix(cl, k), S.eq_bit(Nat.is_eq(rt(cl, k), k))) : Nat}
      %Equal.sym(Nat, S.fixed(labs(cl, k), 0n), cnt_fix(cl, k), fixed_labs(cl, k)) : {Nat.add(_, S.eq_bit(Nat.is_eq(rt(cl, k), k))) == Nat.add(cnt_fix(cl, k), S.eq_bit(Nat.is_eq(rt(cl, k), k))) : Nat}
      {==}

def relabel_snoc(+xs: List<&2, Nat>, +x: Nat, +from: Nat, +to: Nat) -> {S.relabel(SC.snoc(Nat, xs, x), from, to) == SC.snoc(Nat, S.relabel(xs, from, to), S.swap_label(Nat.is_eq(x, from), to, x)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      LL.cons_cong(Nat, S.swap_label(Nat.is_eq(h, from), to, h), S.relabel(SC.snoc(Nat, t, x), from, to), SC.snoc(Nat, S.relabel(t, from, to), S.swap_label(Nat.is_eq(x, from), to, x)), relabel_snoc(t, x, from, to))
