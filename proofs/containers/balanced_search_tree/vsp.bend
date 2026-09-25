import Base
import ../../lib/logic.bend as L
import ../../lib/order.bend as O
import ../../lib/list.bend as LL
import ../../../spec/lib/common.bend as SC
import ../../../spec/containers/balanced_search_tree/main.bend as S
import ../../../src/containers/balanced_search_tree.bend as M
import ./state.bend as ST
import ./ord.bend as OR
import ./navl.bend as NV

# A view's entries in sorted entries, for a lawful comparator: the bounds are
# monotone, so the entries within them are a run; its first (last) is the
# first entry above the lower bound (the last below the upper), when in
# range, and a strict search from a key inside the view is the search in the
# whole map, checked against the range. (source: tools/generators/tm_hand/vsp.src)


# ---- generic ----

def pk_t(-T: Type, +b: Bool, -x: T, -y: T, +h: {b == True{} : Bool}) -> {S.pick(T, b, x, y) == x : T}:
  %Equal.sym(Bool, b, True{}, h) : {S.pick(T, _, x, y) == x : T}
  {==}

def pk_f(-T: Type, +b: Bool, -x: T, -y: T, +h: {b == False{} : Bool}) -> {S.pick(T, b, x, y) == y : T}:
  %Equal.sym(Bool, b, False{}, h) : {S.pick(T, _, x, y) == y : T}
  {==}

def cong(-A: Type, -B: Type, -f: A -> B, -a: A, -b: A, e: {a == b : A}) -> {f(a) == f(b) : B}:
  L.subst(A, z => {f(a) == f(z) : B}, a, b, e, {==})

def and_f(+a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def lt_tr(+c: Cmp, +h: {c == LT{} : Cmp}) -> {Cmp.is_lt(c) == True{} : Bool}:
  L.subst(Cmp, z => {Cmp.is_lt(z) == True{} : Bool}, LT{}, c, Equal.sym(Cmp, c, LT{}, h), {==})

def lt_okf(+c: Cmp, +h: {Cmp.is_lt(c) == True{} : Bool}) -> {S.ordering_ok(c, False{}) == True{} : Bool}:
  L.subst(Cmp, z => {S.ordering_ok(z, False{}) == True{} : Bool}, LT{}, c, Equal.sym(Cmp, c, LT{}, O.lt_is(c, h)), {==})

# ---- comparisons ----

def okw_l(+c: Cmp, +i: Bool, +j: Bool, +h: {S.ordering_ok(c, Bool.and(i, j)) == True{} : Bool}) -> {S.ordering_ok(c, i) == True{} : Bool}:
  match c i:
    case LT{} True{}:
      {==}
    case LT{} False{}:
      {==}
    case EQ{} True{}:
      {==}
    case EQ{} False{}:
      Empty.absurd({False{} == True{} : Bool}, L.false_true(h))
    case GT{} True{}:
      Empty.absurd({False{} == True{} : Bool}, L.false_true(h))
    case GT{} False{}:
      Empty.absurd({False{} == True{} : Bool}, L.false_true(h))

def okw_r(+c: Cmp, +i: Bool, +j: Bool, +h: {S.ordering_ok(c, Bool.and(i, j)) == True{} : Bool}) -> {S.ordering_ok(c, j) == True{} : Bool}:
  match c i:
    case LT{} True{}:
      {==}
    case LT{} False{}:
      {==}
    case EQ{} True{}:
      h
    case EQ{} False{}:
      Empty.absurd({j == True{} : Bool}, L.false_true(h))
    case GT{} True{}:
      Empty.absurd({False{} == True{} : Bool}, L.false_true(h))
    case GT{} False{}:
      Empty.absurd({False{} == True{} : Bool}, L.false_true(h))

def okflip(+c: Cmp, +i: Bool, +h: {S.ordering_ok(c, i) == False{} : Bool}) -> {S.ordering_ok(O.flipc(c), Bool.not(i)) == True{} : Bool}:
  match c i:
    case LT{} True{}:
      Empty.absurd({False{} == True{} : Bool}, L.true_false(h))
    case LT{} False{}:
      Empty.absurd({False{} == True{} : Bool}, L.true_false(h))
    case EQ{} True{}:
      Empty.absurd({False{} == True{} : Bool}, L.true_false(h))
    case EQ{} False{}:
      {==}
    case GT{} True{}:
      {==}
    case GT{} False{}:
      {==}

def okf0(+c: Cmp, +h: {S.ordering_ok(c, False{}) == True{} : Bool}) -> {c == LT{} : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({EQ{} == LT{} : Cmp}, L.false_true(h))
    case GT{}:
      Empty.absurd({GT{} == LT{} : Cmp}, L.false_true(h))

def ok_tl(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +a: K, +b: K, +c: K, +i1: Bool, +i2: Bool, +hx: {cmp(a, b) == LT{} : Cmp}, +y: Cmp, +hy: {cmp(b, c) == y : Cmp}, +h2: {S.ordering_ok(y, i2) == True{} : Bool}) -> {S.ordering_ok(cmp(a, c), Bool.and(i1, i2)) == True{} : Bool}:
  match y:
    case LT{}:
      +lab = lt_tr(cmp(a, b), hx)
      +lbc = lt_tr(cmp(b, c), hy)
      %Equal.sym(Cmp, cmp(a, c), LT{}, O.lt_is(cmp(a, c), OR.slt_trans(~K, ~cmp, ~o, a, b, c, lab, lbc))) : {S.ordering_ok(_, Bool.and(i1, i2)) == True{} : Bool}
      {==}
    case EQ{}:
      +ebc = O.antisym(~K, ~cmp, o, b, c, hy)
      L.subst(K, z => {S.ordering_ok(cmp(a, z), Bool.and(i1, i2)) == True{} : Bool}, b, c, ebc, L.subst(Cmp, z => {S.ordering_ok(z, Bool.and(i1, i2)) == True{} : Bool}, LT{}, cmp(a, b), Equal.sym(Cmp, cmp(a, b), LT{}, hx), {==}))
    case GT{}:
      Empty.absurd({S.ordering_ok(cmp(a, c), Bool.and(i1, i2)) == True{} : Bool}, L.false_true(h2))

def ok_te(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +a: K, +b: K, +c: K, +i1: Bool, +i2: Bool, +hx: {cmp(a, b) == EQ{} : Cmp}, +h1: {i1 == True{} : Bool}, +h2: {S.ordering_ok(cmp(b, c), i2) == True{} : Bool}) -> {S.ordering_ok(cmp(a, c), Bool.and(i1, i2)) == True{} : Bool}:
  +eab = O.antisym(~K, ~cmp, o, a, b, hx)
  %Equal.sym(Bool, i1, True{}, h1) : {S.ordering_ok(cmp(a, c), Bool.and(_, i2)) == True{} : Bool}
  L.subst(K, z => {S.ordering_ok(cmp(z, c), i2) == True{} : Bool}, b, a, Equal.sym(K, a, b, eab), h2)

def ok_tc(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +a: K, +b: K, +c: K, +i1: Bool, +i2: Bool, +x: Cmp, +hx: {cmp(a, b) == x : Cmp}, +h1: {S.ordering_ok(x, i1) == True{} : Bool}, +h2: {S.ordering_ok(cmp(b, c), i2) == True{} : Bool}) -> {S.ordering_ok(cmp(a, c), Bool.and(i1, i2)) == True{} : Bool}:
  match x:
    case LT{}:
      ok_tl(~K, ~cmp, ~o, a, b, c, i1, i2, hx, cmp(b, c), {==}, h2)
    case EQ{}:
      ok_te(~K, ~cmp, ~o, a, b, c, i1, i2, hx, h1, h2)
    case GT{}:
      Empty.absurd({S.ordering_ok(cmp(a, c), Bool.and(i1, i2)) == True{} : Bool}, L.false_true(h1))

# a <= b <= c (each strict or not): a <= c, strict when either is
def ok_trans(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +a: K, +b: K, +c: K, +i1: Bool, +i2: Bool, +h1: {S.ordering_ok(cmp(a, b), i1) == True{} : Bool}, +h2: {S.ordering_ok(cmp(b, c), i2) == True{} : Bool}) -> {S.ordering_ok(cmp(a, c), Bool.and(i1, i2)) == True{} : Bool}:
  ok_tc(~K, ~cmp, ~o, a, b, c, i1, i2, cmp(a, b), {==}, h1, h2)

def fl_ok(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +x: K, +k: K, +i: Bool, +h: {S.ordering_ok(cmp(x, k), i) == False{} : Bool}) -> {S.ordering_ok(cmp(k, x), Bool.not(i)) == True{} : Bool}:
  L.subst(Cmp, z => {S.ordering_ok(z, Bool.not(i)) == True{} : Bool}, O.flipc(cmp(x, k)), cmp(k, x), Equal.sym(Cmp, cmp(k, x), O.flipc(cmp(x, k)), O.flip(~K, ~cmp, o, x, k)), okflip(cmp(x, k), i, h))

def lt_both(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +a: K, +b: K, +h1: {cmp(a, b) == LT{} : Cmp}, +h2: {cmp(b, a) == LT{} : Cmp}) -> Empty:
  +e1 = L.subst(Cmp, z => {cmp(b, a) == O.flipc(z) : Cmp}, cmp(a, b), LT{}, h1, O.flip(~K, ~cmp, o, a, b))
  L.cmp_lt_gt(Equal.trans(Cmp, LT{}, cmp(b, a), GT{}, Equal.sym(Cmp, cmp(b, a), LT{}, h2), e1))

# ---- the bounds are monotone ----

def al_mono(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +lw: M.Bound<K>, +a: K, +e: K, +i: Bool, +ha: {S.above_lower(~K, ~cmp, a, lw) == True{} : Bool}, +hp: {S.ordering_ok(cmp(a, e), i) == True{} : Bool}) -> {S.above_lower(~K, ~cmp, e, lw) == True{} : Bool}:
  match lw:
    case M.Unbounded{}:
      {==}
    case M.Inclusive{+x}:
      okw_l(cmp(x, e), True{}, i, ok_trans(~K, ~cmp, ~o, x, a, e, True{}, i, ha, hp))
    case M.Exclusive{+x}:
      okw_l(cmp(x, e), False{}, i, ok_trans(~K, ~cmp, ~o, x, a, e, False{}, i, ha, hp))

def bu_mono(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +up: M.Bound<K>, +a: K, +e: K, +i: Bool, +ha: {S.below_upper(~K, ~cmp, a, up) == True{} : Bool}, +hq: {S.ordering_ok(cmp(e, a), i) == True{} : Bool}) -> {S.below_upper(~K, ~cmp, e, up) == True{} : Bool}:
  match up:
    case M.Unbounded{}:
      {==}
    case M.Inclusive{+y}:
      okw_r(cmp(e, y), i, True{}, ok_trans(~K, ~cmp, ~o, e, a, y, i, True{}, hq, ha))
    case M.Exclusive{+y}:
      okw_r(cmp(e, y), i, False{}, ok_trans(~K, ~cmp, ~o, e, a, y, i, False{}, hq, ha))

# below the lower bound, above it: strictly less
def al_lt(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +lw: M.Bound<K>, +k: K, +e: K, +hk: {S.above_lower(~K, ~cmp, k, lw) == False{} : Bool}, +he: {S.above_lower(~K, ~cmp, e, lw) == True{} : Bool}) -> {cmp(k, e) == LT{} : Cmp}:
  match lw:
    case M.Unbounded{}:
      Empty.absurd({cmp(k, e) == LT{} : Cmp}, L.true_false(hk))
    case M.Inclusive{+x}:
      okf0(cmp(k, e), ok_trans(~K, ~cmp, ~o, k, x, e, False{}, True{}, fl_ok(~K, ~cmp, ~o, x, k, True{}, hk), he))
    case M.Exclusive{+x}:
      okf0(cmp(k, e), ok_trans(~K, ~cmp, ~o, k, x, e, True{}, False{}, fl_ok(~K, ~cmp, ~o, x, k, False{}, hk), he))

def bu_lt(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +up: M.Bound<K>, +k: K, +e: K, +hk: {S.below_upper(~K, ~cmp, k, up) == False{} : Bool}, +he: {S.below_upper(~K, ~cmp, e, up) == True{} : Bool}) -> {cmp(e, k) == LT{} : Cmp}:
  match up:
    case M.Unbounded{}:
      Empty.absurd({cmp(e, k) == LT{} : Cmp}, L.true_false(hk))
    case M.Inclusive{+y}:
      okf0(cmp(e, k), ok_trans(~K, ~cmp, ~o, e, y, k, True{}, False{}, he, fl_ok(~K, ~cmp, ~o, k, y, True{}, hk)))
    case M.Exclusive{+y}:
      okf0(cmp(e, k), ok_trans(~K, ~cmp, ~o, e, y, k, False{}, True{}, he, fl_ok(~K, ~cmp, ~o, k, y, False{}, hk)))

def bu_fc(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +up: M.Bound<K>, +k: K, +f: K, +hk: {S.below_upper(~K, ~cmp, k, up) == False{} : Bool}, +hlt: {Cmp.is_lt(cmp(k, f)) == True{} : Bool}, +b: Bool, +hb: {S.below_upper(~K, ~cmp, f, up) == b : Bool}) -> {S.below_upper(~K, ~cmp, f, up) == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({S.below_upper(~K, ~cmp, f, up) == False{} : Bool}, lt_both(~K, ~cmp, ~o, f, k, bu_lt(~K, ~cmp, ~o, up, k, f, hk, hb), O.lt_is(cmp(k, f), hlt)))
    case False{}:
      hb

# past a key above the upper bound: above it
def bu_false(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +up: M.Bound<K>, +k: K, +f: K, +hk: {S.below_upper(~K, ~cmp, k, up) == False{} : Bool}, +hlt: {Cmp.is_lt(cmp(k, f)) == True{} : Bool}) -> {S.below_upper(~K, ~cmp, f, up) == False{} : Bool}:
  bu_fc(~K, ~cmp, ~o, up, k, f, hk, hlt, S.below_upper(~K, ~cmp, f, up), {==})

def al_fc(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +lw: M.Bound<K>, +k: K, +f: K, +hk: {S.above_lower(~K, ~cmp, k, lw) == False{} : Bool}, +hlt: {Cmp.is_lt(cmp(f, k)) == True{} : Bool}, +b: Bool, +hb: {S.above_lower(~K, ~cmp, f, lw) == b : Bool}) -> {S.above_lower(~K, ~cmp, f, lw) == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({S.above_lower(~K, ~cmp, f, lw) == False{} : Bool}, L.true_false(Equal.trans(Bool, True{}, S.above_lower(~K, ~cmp, k, lw), False{}, Equal.sym(Bool, S.above_lower(~K, ~cmp, k, lw), True{}, al_mono(~K, ~cmp, ~o, lw, f, k, False{}, hb, lt_okf(cmp(f, k), hlt))), hk)))
    case False{}:
      hb

# before a key below the lower bound: below it
def al_false(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +lw: M.Bound<K>, +k: K, +f: K, +hk: {S.above_lower(~K, ~cmp, k, lw) == False{} : Bool}, +hlt: {Cmp.is_lt(cmp(f, k)) == True{} : Bool}) -> {S.above_lower(~K, ~cmp, f, lw) == False{} : Bool}:
  al_fc(~K, ~cmp, ~o, lw, k, f, hk, hlt, S.above_lower(~K, ~cmp, f, lw), {==})

def ir_t(~K: Data, ~cmp: K -> K -> Cmp, +lw: M.Bound<K>, +up: M.Bound<K>, +k: K, +ha: {S.above_lower(~K, ~cmp, k, lw) == True{} : Bool}, +hb: {S.below_upper(~K, ~cmp, k, up) == True{} : Bool}) -> {S.in_range(~K, ~cmp, k, lw, up) == True{} : Bool}:
  L.and_intro(S.above_lower(~K, ~cmp, k, lw), S.below_upper(~K, ~cmp, k, up), ha, hb)

def ir_fb(~K: Data, ~cmp: K -> K -> Cmp, +lw: M.Bound<K>, +up: M.Bound<K>, +k: K, +hb: {S.below_upper(~K, ~cmp, k, up) == False{} : Bool}) -> {S.in_range(~K, ~cmp, k, lw, up) == False{} : Bool}:
  %Equal.sym(Bool, S.below_upper(~K, ~cmp, k, up), False{}, hb) : {Bool.and(S.above_lower(~K, ~cmp, k, lw), _) == False{} : Bool}
  and_f(S.above_lower(~K, ~cmp, k, lw))

def ir_fa(~K: Data, ~cmp: K -> K -> Cmp, +lw: M.Bound<K>, +up: M.Bound<K>, +k: K, +ha: {S.above_lower(~K, ~cmp, k, lw) == False{} : Bool}) -> {S.in_range(~K, ~cmp, k, lw, up) == False{} : Bool}:
  %Equal.sym(Bool, S.above_lower(~K, ~cmp, k, lw), False{}, ha) : {Bool.and(_, S.below_upper(~K, ~cmp, k, up)) == False{} : Bool}
  {==}

# ---- the entries within ----

def w_in(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +lw: M.Bound<K>, +up: M.Bound<K>, +e: M.Entry<K, V>, +t: List<&2, M.Entry<K, V>>, +h: {S.in_range(~K, ~cmp, S.key(K, V, e), lw, up) == True{} : Bool}) -> {S.within(~K, ~V, ~cmp, lw, up, Con{e, t}) == Con{e, S.within(~K, ~V, ~cmp, lw, up, t)} : List<&2, M.Entry<K, V>>}:
  pk_t(List<&2, M.Entry<K, V>>, S.in_range(~K, ~cmp, S.key(K, V, e), lw, up), Con{e, S.within(~K, ~V, ~cmp, lw, up, t)}, S.within(~K, ~V, ~cmp, lw, up, t), h)

def w_out(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +lw: M.Bound<K>, +up: M.Bound<K>, +e: M.Entry<K, V>, +t: List<&2, M.Entry<K, V>>, +h: {S.in_range(~K, ~cmp, S.key(K, V, e), lw, up) == False{} : Bool}) -> {S.within(~K, ~V, ~cmp, lw, up, Con{e, t}) == S.within(~K, ~V, ~cmp, lw, up, t) : List<&2, M.Entry<K, V>>}:
  pk_f(List<&2, M.Entry<K, V>>, S.in_range(~K, ~cmp, S.key(K, V, e), lw, up), Con{e, S.within(~K, ~V, ~cmp, lw, up, t)}, S.within(~K, ~V, ~cmp, lw, up, t), h)

def chk(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +lw: M.Bound<K>, +up: M.Bound<K>, m: Maybe<&2, M.Entry<K, V>>) -> Maybe<&2, M.Entry<K, V>>:
  match m:
    case None{}:
      None{}
    case Some{+e}:
      S.pick(Maybe<&2, M.Entry<K, V>>, S.in_range(~K, ~cmp, S.key(K, V, e), lw, up), Some{e}, None{})

def chk_in(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +lw: M.Bound<K>, +up: M.Bound<K>, +e: M.Entry<K, V>, +h: {S.in_range(~K, ~cmp, S.key(K, V, e), lw, up) == True{} : Bool}) -> {chk(~K, ~V, ~cmp, lw, up, Some{e}) == Some{e} : Maybe<&2, M.Entry<K, V>>}:
  pk_t(Maybe<&2, M.Entry<K, V>>, S.in_range(~K, ~cmp, S.key(K, V, e), lw, up), Some{e}, None{}, h)

def chk_out(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +lw: M.Bound<K>, +up: M.Bound<K>, +e: M.Entry<K, V>, +h: {S.in_range(~K, ~cmp, S.key(K, V, e), lw, up) == False{} : Bool}) -> {chk(~K, ~V, ~cmp, lw, up, Some{e}) == None{} : Maybe<&2, M.Entry<K, V>>}:
  pk_f(Maybe<&2, M.Entry<K, V>>, S.in_range(~K, ~cmp, S.key(K, V, e), lw, up), Some{e}, None{}, h)

# above a key past the upper bound, nothing is within
def wnil(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +lw: M.Bound<K>, +up: M.Bound<K>, +k: K, +t: List<&2, M.Entry<K, V>>, +hk: {S.below_upper(~K, ~cmp, k, up) == False{} : Bool}, +hg: {OR.gtall(~K, ~V, ~cmp, k, t) == True{} : Bool}) -> {S.within(~K, ~V, ~cmp, lw, up, t) == Nil{} : List<&2, M.Entry<K, V>>}:
  match t:
    case Nil{}:
      {==}
    case Con{+e, +u}:
      +h1 = L.and_left(Cmp.is_lt(cmp(k, S.key(K, V, e))), OR.gtall(~K, ~V, ~cmp, k, u), hg)
      +h2 = L.and_right(Cmp.is_lt(cmp(k, S.key(K, V, e))), OR.gtall(~K, ~V, ~cmp, k, u), hg)
      Equal.trans(List<&2, M.Entry<K, V>>, S.within(~K, ~V, ~cmp, lw, up, Con{e, u}), S.within(~K, ~V, ~cmp, lw, up, u), Nil{}, w_out(~K, ~V, ~cmp, lw, up, e, u, ir_fb(~K, ~cmp, lw, up, S.key(K, V, e), bu_false(~K, ~cmp, ~o, up, k, S.key(K, V, e), hk, h1))), wnil(~K, ~V, ~cmp, ~o, lw, up, k, u, hk, h2))

def gt_wc(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +lw: M.Bound<K>, +up: M.Bound<K>, +k: K, +e: M.Entry<K, V>, +u: List<&2, M.Entry<K, V>>, +h1: {Cmp.is_lt(cmp(k, S.key(K, V, e))) == True{} : Bool}, +hu: {OR.gtall(~K, ~V, ~cmp, k, S.within(~K, ~V, ~cmp, lw, up, u)) == True{} : Bool}, +b: Bool) -> {OR.gtall(~K, ~V, ~cmp, k, S.pick(List<&2, M.Entry<K, V>>, b, Con{e, S.within(~K, ~V, ~cmp, lw, up, u)}, S.within(~K, ~V, ~cmp, lw, up, u))) == True{} : Bool}:
  match b:
    case True{}:
      L.and_intro(Cmp.is_lt(cmp(k, S.key(K, V, e))), OR.gtall(~K, ~V, ~cmp, k, S.within(~K, ~V, ~cmp, lw, up, u)), h1, hu)
    case False{}:
      hu

def gt_w(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +lw: M.Bound<K>, +up: M.Bound<K>, +k: K, +t: List<&2, M.Entry<K, V>>, +h: {OR.gtall(~K, ~V, ~cmp, k, t) == True{} : Bool}) -> {OR.gtall(~K, ~V, ~cmp, k, S.within(~K, ~V, ~cmp, lw, up, t)) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{+e, +u}:
      gt_wc(~K, ~V, ~cmp, lw, up, k, e, u, L.and_left(Cmp.is_lt(cmp(k, S.key(K, V, e))), OR.gtall(~K, ~V, ~cmp, k, u), h), gt_w(~K, ~V, ~cmp, lw, up, k, u, L.and_right(Cmp.is_lt(cmp(k, S.key(K, V, e))), OR.gtall(~K, ~V, ~cmp, k, u), h)), S.in_range(~K, ~cmp, S.key(K, V, e), lw, up))

def wgt_c(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +lw: M.Bound<K>, +up: M.Bound<K>, +k: K, +e: M.Entry<K, V>, +u: List<&2, M.Entry<K, V>>, +hk: {S.above_lower(~K, ~cmp, k, lw) == False{} : Bool}, +hu: {OR.gtall(~K, ~V, ~cmp, k, S.within(~K, ~V, ~cmp, lw, up, u)) == True{} : Bool}, +b: Bool, +hb: {S.in_range(~K, ~cmp, S.key(K, V, e), lw, up) == b : Bool}) -> {OR.gtall(~K, ~V, ~cmp, k, S.pick(List<&2, M.Entry<K, V>>, b, Con{e, S.within(~K, ~V, ~cmp, lw, up, u)}, S.within(~K, ~V, ~cmp, lw, up, u))) == True{} : Bool}:
  match b:
    case True{}:
      L.and_intro(Cmp.is_lt(cmp(k, S.key(K, V, e))), OR.gtall(~K, ~V, ~cmp, k, S.within(~K, ~V, ~cmp, lw, up, u)), lt_tr(cmp(k, S.key(K, V, e)), al_lt(~K, ~cmp, ~o, lw, k, S.key(K, V, e), hk, L.and_left(S.above_lower(~K, ~cmp, S.key(K, V, e), lw), S.below_upper(~K, ~cmp, S.key(K, V, e), up), hb))), hu)
    case False{}:
      hu

# a key below the lower bound is below everything within
def wgt(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +lw: M.Bound<K>, +up: M.Bound<K>, +k: K, +es: List<&2, M.Entry<K, V>>, +hk: {S.above_lower(~K, ~cmp, k, lw) == False{} : Bool}) -> {OR.gtall(~K, ~V, ~cmp, k, S.within(~K, ~V, ~cmp, lw, up, es)) == True{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +u}:
      wgt_c(~K, ~V, ~cmp, ~o, lw, up, k, e, u, hk, wgt(~K, ~V, ~cmp, ~o, lw, up, k, u, hk), S.in_range(~K, ~cmp, S.key(K, V, e), lw, up), {==})

def wlt_c(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +lw: M.Bound<K>, +up: M.Bound<K>, +k: K, +e: M.Entry<K, V>, +u: List<&2, M.Entry<K, V>>, +hk: {S.below_upper(~K, ~cmp, k, up) == False{} : Bool}, +hu: {OR.ltall(~K, ~V, ~cmp, k, S.within(~K, ~V, ~cmp, lw, up, u)) == True{} : Bool}, +b: Bool, +hb: {S.in_range(~K, ~cmp, S.key(K, V, e), lw, up) == b : Bool}) -> {OR.ltall(~K, ~V, ~cmp, k, S.pick(List<&2, M.Entry<K, V>>, b, Con{e, S.within(~K, ~V, ~cmp, lw, up, u)}, S.within(~K, ~V, ~cmp, lw, up, u))) == True{} : Bool}:
  match b:
    case True{}:
      L.and_intro(Cmp.is_lt(cmp(S.key(K, V, e), k)), OR.ltall(~K, ~V, ~cmp, k, S.within(~K, ~V, ~cmp, lw, up, u)), lt_tr(cmp(S.key(K, V, e), k), bu_lt(~K, ~cmp, ~o, up, k, S.key(K, V, e), hk, L.and_right(S.above_lower(~K, ~cmp, S.key(K, V, e), lw), S.below_upper(~K, ~cmp, S.key(K, V, e), up), hb))), hu)
    case False{}:
      hu

# a key above the upper bound is above everything within
def wlt(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +lw: M.Bound<K>, +up: M.Bound<K>, +k: K, +es: List<&2, M.Entry<K, V>>, +hk: {S.below_upper(~K, ~cmp, k, up) == False{} : Bool}) -> {OR.ltall(~K, ~V, ~cmp, k, S.within(~K, ~V, ~cmp, lw, up, es)) == True{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +u}:
      wlt_c(~K, ~V, ~cmp, ~o, lw, up, k, e, u, hk, wlt(~K, ~V, ~cmp, ~o, lw, up, k, u, hk), S.in_range(~K, ~cmp, S.key(K, V, e), lw, up), {==})

# ---- the first within: the first above the lower bound, checked ----

def fal(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +lw: M.Bound<K>, es: List<&2, M.Entry<K, V>>) -> Maybe<&2, M.Entry<K, V>>:
  match es:
    case Nil{}:
      None{}
    case Con{+e, +t}:
      S.pick(Maybe<&2, M.Entry<K, V>>, S.above_lower(~K, ~cmp, S.key(K, V, e), lw), Some{e}, fal(~K, ~V, ~cmp, lw, t))


def e1_c(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +lw: M.Bound<K>, +up: M.Bound<K>, +e: M.Entry<K, V>, +t: List<&2, M.Entry<K, V>>, +h: {ST.ordered(~K, ~V, ~cmp, Con{e, t}) == True{} : Bool}, +ih: {S.head(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, t)) == chk(~K, ~V, ~cmp, lw, up, fal(~K, ~V, ~cmp, lw, t)) : Maybe<&2, M.Entry<K, V>>}, +a: Bool, +ha: {S.above_lower(~K, ~cmp, S.key(K, V, e), lw) == a : Bool}, +b: Bool, +hb: {S.below_upper(~K, ~cmp, S.key(K, V, e), up) == b : Bool}) -> {S.head(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, Con{e, t})) == chk(~K, ~V, ~cmp, lw, up, fal(~K, ~V, ~cmp, lw, Con{e, t})) : Maybe<&2, M.Entry<K, V>>}:
  match a b:
    case True{} True{}:
      +hir = ir_t(~K, ~cmp, lw, up, S.key(K, V, e), ha, hb)
      +l1 = cong(List<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => S.head(M.Entry<K, V>, z), S.within(~K, ~V, ~cmp, lw, up, Con{e, t}), Con{e, S.within(~K, ~V, ~cmp, lw, up, t)}, w_in(~K, ~V, ~cmp, lw, up, e, t, hir))
      +r1 = cong(Maybe<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => chk(~K, ~V, ~cmp, lw, up, z), fal(~K, ~V, ~cmp, lw, Con{e, t}), Some{e}, pk_t(Maybe<&2, M.Entry<K, V>>, S.above_lower(~K, ~cmp, S.key(K, V, e), lw), Some{e}, fal(~K, ~V, ~cmp, lw, t), ha))
      Equal.trans(Maybe<&2, M.Entry<K, V>>, S.head(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, Con{e, t})), Some{e}, chk(~K, ~V, ~cmp, lw, up, fal(~K, ~V, ~cmp, lw, Con{e, t})), l1, Equal.sym(Maybe<&2, M.Entry<K, V>>, chk(~K, ~V, ~cmp, lw, up, fal(~K, ~V, ~cmp, lw, Con{e, t})), Some{e}, Equal.trans(Maybe<&2, M.Entry<K, V>>, chk(~K, ~V, ~cmp, lw, up, fal(~K, ~V, ~cmp, lw, Con{e, t})), chk(~K, ~V, ~cmp, lw, up, Some{e}), Some{e}, r1, chk_in(~K, ~V, ~cmp, lw, up, e, hir))))
    case True{} False{}:
      +hir = ir_fb(~K, ~cmp, lw, up, S.key(K, V, e), hb)
      +l1 = cong(List<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => S.head(M.Entry<K, V>, z), S.within(~K, ~V, ~cmp, lw, up, Con{e, t}), S.within(~K, ~V, ~cmp, lw, up, t), w_out(~K, ~V, ~cmp, lw, up, e, t, hir))
      +l2 = cong(List<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => S.head(M.Entry<K, V>, z), S.within(~K, ~V, ~cmp, lw, up, t), Nil{}, wnil(~K, ~V, ~cmp, ~o, lw, up, S.key(K, V, e), t, hb, OR.ord_gt(~K, ~V, ~cmp, ~o, t, e, h)))
      +r1 = cong(Maybe<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => chk(~K, ~V, ~cmp, lw, up, z), fal(~K, ~V, ~cmp, lw, Con{e, t}), Some{e}, pk_t(Maybe<&2, M.Entry<K, V>>, S.above_lower(~K, ~cmp, S.key(K, V, e), lw), Some{e}, fal(~K, ~V, ~cmp, lw, t), ha))
      Equal.trans(Maybe<&2, M.Entry<K, V>>, S.head(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, Con{e, t})), None{}, chk(~K, ~V, ~cmp, lw, up, fal(~K, ~V, ~cmp, lw, Con{e, t})), Equal.trans(Maybe<&2, M.Entry<K, V>>, S.head(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, Con{e, t})), S.head(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, t)), None{}, l1, l2), Equal.sym(Maybe<&2, M.Entry<K, V>>, chk(~K, ~V, ~cmp, lw, up, fal(~K, ~V, ~cmp, lw, Con{e, t})), None{}, Equal.trans(Maybe<&2, M.Entry<K, V>>, chk(~K, ~V, ~cmp, lw, up, fal(~K, ~V, ~cmp, lw, Con{e, t})), chk(~K, ~V, ~cmp, lw, up, Some{e}), None{}, r1, chk_out(~K, ~V, ~cmp, lw, up, e, hir))))
    case False{} True{}:
      +l1 = cong(List<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => S.head(M.Entry<K, V>, z), S.within(~K, ~V, ~cmp, lw, up, Con{e, t}), S.within(~K, ~V, ~cmp, lw, up, t), w_out(~K, ~V, ~cmp, lw, up, e, t, ir_fa(~K, ~cmp, lw, up, S.key(K, V, e), ha)))
      +r1 = cong(Maybe<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => chk(~K, ~V, ~cmp, lw, up, z), fal(~K, ~V, ~cmp, lw, Con{e, t}), fal(~K, ~V, ~cmp, lw, t), pk_f(Maybe<&2, M.Entry<K, V>>, S.above_lower(~K, ~cmp, S.key(K, V, e), lw), Some{e}, fal(~K, ~V, ~cmp, lw, t), ha))
      Equal.trans(Maybe<&2, M.Entry<K, V>>, S.head(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, Con{e, t})), chk(~K, ~V, ~cmp, lw, up, fal(~K, ~V, ~cmp, lw, t)), chk(~K, ~V, ~cmp, lw, up, fal(~K, ~V, ~cmp, lw, Con{e, t})), Equal.trans(Maybe<&2, M.Entry<K, V>>, S.head(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, Con{e, t})), S.head(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, t)), chk(~K, ~V, ~cmp, lw, up, fal(~K, ~V, ~cmp, lw, t)), l1, ih), Equal.sym(Maybe<&2, M.Entry<K, V>>, chk(~K, ~V, ~cmp, lw, up, fal(~K, ~V, ~cmp, lw, Con{e, t})), chk(~K, ~V, ~cmp, lw, up, fal(~K, ~V, ~cmp, lw, t)), r1))
    case False{} False{}:
      +l1 = cong(List<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => S.head(M.Entry<K, V>, z), S.within(~K, ~V, ~cmp, lw, up, Con{e, t}), S.within(~K, ~V, ~cmp, lw, up, t), w_out(~K, ~V, ~cmp, lw, up, e, t, ir_fa(~K, ~cmp, lw, up, S.key(K, V, e), ha)))
      +r1 = cong(Maybe<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => chk(~K, ~V, ~cmp, lw, up, z), fal(~K, ~V, ~cmp, lw, Con{e, t}), fal(~K, ~V, ~cmp, lw, t), pk_f(Maybe<&2, M.Entry<K, V>>, S.above_lower(~K, ~cmp, S.key(K, V, e), lw), Some{e}, fal(~K, ~V, ~cmp, lw, t), ha))
      Equal.trans(Maybe<&2, M.Entry<K, V>>, S.head(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, Con{e, t})), chk(~K, ~V, ~cmp, lw, up, fal(~K, ~V, ~cmp, lw, t)), chk(~K, ~V, ~cmp, lw, up, fal(~K, ~V, ~cmp, lw, Con{e, t})), Equal.trans(Maybe<&2, M.Entry<K, V>>, S.head(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, Con{e, t})), S.head(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, t)), chk(~K, ~V, ~cmp, lw, up, fal(~K, ~V, ~cmp, lw, t)), l1, ih), Equal.sym(Maybe<&2, M.Entry<K, V>>, chk(~K, ~V, ~cmp, lw, up, fal(~K, ~V, ~cmp, lw, Con{e, t})), chk(~K, ~V, ~cmp, lw, up, fal(~K, ~V, ~cmp, lw, t)), r1))

def first_within(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +lw: M.Bound<K>, +up: M.Bound<K>, +es: List<&2, M.Entry<K, V>>, +h: {ST.ordered(~K, ~V, ~cmp, es) == True{} : Bool}) -> {S.head(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, es)) == chk(~K, ~V, ~cmp, lw, up, fal(~K, ~V, ~cmp, lw, es)) : Maybe<&2, M.Entry<K, V>>}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      e1_c(~K, ~V, ~cmp, ~o, lw, up, e, t, h, first_within(~K, ~V, ~cmp, ~o, lw, up, t, OR.ord_tail(~K, ~V, ~cmp, e, t, h)), S.above_lower(~K, ~cmp, S.key(K, V, e), lw), {==}, S.below_upper(~K, ~cmp, S.key(K, V, e), up), {==})

# ---- the last within: the last below the upper bound, checked ----

def lbu(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +up: M.Bound<K>, es: List<&2, M.Entry<K, V>>, +best: Maybe<&2, M.Entry<K, V>>) -> Maybe<&2, M.Entry<K, V>>:
  match es:
    case Nil{}:
      best
    case Con{+e, t}:
      lbu(~K, ~V, ~cmp, up, t, S.pick(Maybe<&2, M.Entry<K, V>>, S.below_upper(~K, ~cmp, S.key(K, V, e), up), Some{e}, best))

# a candidate before every entry
def bgood(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, m: Maybe<&2, M.Entry<K, V>>, +es: List<&2, M.Entry<K, V>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{+b}:
      OR.gtall(~K, ~V, ~cmp, S.key(K, V, b), es)

def bg_tail(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +m: Maybe<&2, M.Entry<K, V>>, +e: M.Entry<K, V>, +t: List<&2, M.Entry<K, V>>, +h: {bgood(~K, ~V, ~cmp, m, Con{e, t}) == True{} : Bool}) -> {bgood(~K, ~V, ~cmp, m, t) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+b}:
      L.and_right(Cmp.is_lt(cmp(S.key(K, V, b), S.key(K, V, e))), OR.gtall(~K, ~V, ~cmp, S.key(K, V, b), t), h)

# a candidate before an entry below the lower bound is out of range
def chk_none(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +lw: M.Bound<K>, +up: M.Bound<K>, +m: Maybe<&2, M.Entry<K, V>>, +e: M.Entry<K, V>, +t: List<&2, M.Entry<K, V>>, +hbg: {bgood(~K, ~V, ~cmp, m, Con{e, t}) == True{} : Bool}, +hal: {S.above_lower(~K, ~cmp, S.key(K, V, e), lw) == False{} : Bool}) -> {chk(~K, ~V, ~cmp, lw, up, m) == None{} : Maybe<&2, M.Entry<K, V>>}:
  match m:
    case None{}:
      {==}
    case Some{+b}:
      chk_out(~K, ~V, ~cmp, lw, up, b, ir_fa(~K, ~cmp, lw, up, S.key(K, V, b), al_false(~K, ~cmp, ~o, lw, S.key(K, V, e), S.key(K, V, b), hal, L.and_left(Cmp.is_lt(cmp(S.key(K, V, b), S.key(K, V, e))), OR.gtall(~K, ~V, ~cmp, S.key(K, V, b), t), hbg))))

# past a key above the upper bound, no entry is a candidate
def lbu_none(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +up: M.Bound<K>, +k: K, +t: List<&2, M.Entry<K, V>>, +best: Maybe<&2, M.Entry<K, V>>, +hk: {S.below_upper(~K, ~cmp, k, up) == False{} : Bool}, +hg: {OR.gtall(~K, ~V, ~cmp, k, t) == True{} : Bool}) -> {lbu(~K, ~V, ~cmp, up, t, best) == best : Maybe<&2, M.Entry<K, V>>}:
  match t:
    case Nil{}:
      {==}
    case Con{+f, +u}:
      +h1 = L.and_left(Cmp.is_lt(cmp(k, S.key(K, V, f))), OR.gtall(~K, ~V, ~cmp, k, u), hg)
      +h2 = L.and_right(Cmp.is_lt(cmp(k, S.key(K, V, f))), OR.gtall(~K, ~V, ~cmp, k, u), hg)
      %Equal.sym(Maybe<&2, M.Entry<K, V>>, S.pick(Maybe<&2, M.Entry<K, V>>, S.below_upper(~K, ~cmp, S.key(K, V, f), up), Some{f}, best), best, pk_f(Maybe<&2, M.Entry<K, V>>, S.below_upper(~K, ~cmp, S.key(K, V, f), up), Some{f}, best, bu_false(~K, ~cmp, ~o, up, k, S.key(K, V, f), hk, h1))) : {lbu(~K, ~V, ~cmp, up, u, _) == best : Maybe<&2, M.Entry<K, V>>}
      lbu_none(~K, ~V, ~cmp, ~o, up, k, u, best, hk, h2)


def e2_c(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +lw: M.Bound<K>, +up: M.Bound<K>, +e: M.Entry<K, V>, +t: List<&2, M.Entry<K, V>>, +bst: Maybe<&2, M.Entry<K, V>>, +h: {ST.ordered(~K, ~V, ~cmp, Con{e, t}) == True{} : Bool}, +hbg: {bgood(~K, ~V, ~cmp, bst, Con{e, t}) == True{} : Bool}, +ih: {OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, t)), chk(~K, ~V, ~cmp, lw, up, Some{e})) == chk(~K, ~V, ~cmp, lw, up, lbu(~K, ~V, ~cmp, up, t, Some{e})) : Maybe<&2, M.Entry<K, V>>}, +a: Bool, +ha: {S.above_lower(~K, ~cmp, S.key(K, V, e), lw) == a : Bool}, +b: Bool, +hb: {S.below_upper(~K, ~cmp, S.key(K, V, e), up) == b : Bool}) -> {OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, Con{e, t})), chk(~K, ~V, ~cmp, lw, up, bst)) == chk(~K, ~V, ~cmp, lw, up, lbu(~K, ~V, ~cmp, up, Con{e, t}, bst)) : Maybe<&2, M.Entry<K, V>>}:
  match a b:
    case True{} True{}:
      +hir = ir_t(~K, ~cmp, lw, up, S.key(K, V, e), ha, hb)
      +l1 = cong(List<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, z), chk(~K, ~V, ~cmp, lw, up, bst)), S.within(~K, ~V, ~cmp, lw, up, Con{e, t}), Con{e, S.within(~K, ~V, ~cmp, lw, up, t)}, w_in(~K, ~V, ~cmp, lw, up, e, t, hir))
      +l2 = Equal.sym(Maybe<&2, M.Entry<K, V>>, OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, t)), Some{e}), OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, Con{e, S.within(~K, ~V, ~cmp, lw, up, t)}), chk(~K, ~V, ~cmp, lw, up, bst)), NV.lw_all_c(K, V, e, S.within(~K, ~V, ~cmp, lw, up, t), chk(~K, ~V, ~cmp, lw, up, bst)))
      +l3 = cong(Maybe<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, t)), z), Some{e}, chk(~K, ~V, ~cmp, lw, up, Some{e}), Equal.sym(Maybe<&2, M.Entry<K, V>>, chk(~K, ~V, ~cmp, lw, up, Some{e}), Some{e}, chk_in(~K, ~V, ~cmp, lw, up, e, hir)))
      +r1 = cong(Maybe<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => chk(~K, ~V, ~cmp, lw, up, lbu(~K, ~V, ~cmp, up, t, z)), S.pick(Maybe<&2, M.Entry<K, V>>, S.below_upper(~K, ~cmp, S.key(K, V, e), up), Some{e}, bst), Some{e}, pk_t(Maybe<&2, M.Entry<K, V>>, S.below_upper(~K, ~cmp, S.key(K, V, e), up), Some{e}, bst, hb))
      Equal.trans(Maybe<&2, M.Entry<K, V>>, OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, Con{e, t})), chk(~K, ~V, ~cmp, lw, up, bst)), OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, Con{e, S.within(~K, ~V, ~cmp, lw, up, t)}), chk(~K, ~V, ~cmp, lw, up, bst)), chk(~K, ~V, ~cmp, lw, up, lbu(~K, ~V, ~cmp, up, Con{e, t}, bst)), l1, Equal.trans(Maybe<&2, M.Entry<K, V>>, OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, Con{e, S.within(~K, ~V, ~cmp, lw, up, t)}), chk(~K, ~V, ~cmp, lw, up, bst)), OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, t)), Some{e}), chk(~K, ~V, ~cmp, lw, up, lbu(~K, ~V, ~cmp, up, Con{e, t}, bst)), l2, Equal.trans(Maybe<&2, M.Entry<K, V>>, OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, t)), Some{e}), OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, t)), chk(~K, ~V, ~cmp, lw, up, Some{e})), chk(~K, ~V, ~cmp, lw, up, lbu(~K, ~V, ~cmp, up, Con{e, t}, bst)), l3, Equal.trans(Maybe<&2, M.Entry<K, V>>, OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, t)), chk(~K, ~V, ~cmp, lw, up, Some{e})), chk(~K, ~V, ~cmp, lw, up, lbu(~K, ~V, ~cmp, up, t, Some{e})), chk(~K, ~V, ~cmp, lw, up, lbu(~K, ~V, ~cmp, up, Con{e, t}, bst)), ih, Equal.sym(Maybe<&2, M.Entry<K, V>>, chk(~K, ~V, ~cmp, lw, up, lbu(~K, ~V, ~cmp, up, Con{e, t}, bst)), chk(~K, ~V, ~cmp, lw, up, lbu(~K, ~V, ~cmp, up, t, Some{e})), r1)))))
    case True{} False{}:
      +hir = ir_fb(~K, ~cmp, lw, up, S.key(K, V, e), hb)
      +hgt = OR.ord_gt(~K, ~V, ~cmp, ~o, t, e, h)
      +l1 = cong(List<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, z), chk(~K, ~V, ~cmp, lw, up, bst)), S.within(~K, ~V, ~cmp, lw, up, Con{e, t}), Nil{}, Equal.trans(List<&2, M.Entry<K, V>>, S.within(~K, ~V, ~cmp, lw, up, Con{e, t}), S.within(~K, ~V, ~cmp, lw, up, t), Nil{}, w_out(~K, ~V, ~cmp, lw, up, e, t, hir), wnil(~K, ~V, ~cmp, ~o, lw, up, S.key(K, V, e), t, hb, hgt)))
      +r1 = cong(Maybe<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => chk(~K, ~V, ~cmp, lw, up, lbu(~K, ~V, ~cmp, up, t, z)), S.pick(Maybe<&2, M.Entry<K, V>>, S.below_upper(~K, ~cmp, S.key(K, V, e), up), Some{e}, bst), bst, pk_f(Maybe<&2, M.Entry<K, V>>, S.below_upper(~K, ~cmp, S.key(K, V, e), up), Some{e}, bst, hb))
      +r2 = cong(Maybe<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => chk(~K, ~V, ~cmp, lw, up, z), lbu(~K, ~V, ~cmp, up, t, bst), bst, lbu_none(~K, ~V, ~cmp, ~o, up, S.key(K, V, e), t, bst, hb, hgt))
      Equal.trans(Maybe<&2, M.Entry<K, V>>, OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, Con{e, t})), chk(~K, ~V, ~cmp, lw, up, bst)), chk(~K, ~V, ~cmp, lw, up, bst), chk(~K, ~V, ~cmp, lw, up, lbu(~K, ~V, ~cmp, up, Con{e, t}, bst)), l1, Equal.sym(Maybe<&2, M.Entry<K, V>>, chk(~K, ~V, ~cmp, lw, up, lbu(~K, ~V, ~cmp, up, Con{e, t}, bst)), chk(~K, ~V, ~cmp, lw, up, bst), Equal.trans(Maybe<&2, M.Entry<K, V>>, chk(~K, ~V, ~cmp, lw, up, lbu(~K, ~V, ~cmp, up, Con{e, t}, bst)), chk(~K, ~V, ~cmp, lw, up, lbu(~K, ~V, ~cmp, up, t, bst)), chk(~K, ~V, ~cmp, lw, up, bst), r1, r2)))
    case False{} True{}:
      +hir = ir_fa(~K, ~cmp, lw, up, S.key(K, V, e), ha)
      +l1 = cong(List<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, z), chk(~K, ~V, ~cmp, lw, up, bst)), S.within(~K, ~V, ~cmp, lw, up, Con{e, t}), S.within(~K, ~V, ~cmp, lw, up, t), w_out(~K, ~V, ~cmp, lw, up, e, t, hir))
      +l2 = cong(Maybe<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, t)), z), chk(~K, ~V, ~cmp, lw, up, bst), None{}, chk_none(~K, ~V, ~cmp, ~o, lw, up, bst, e, t, hbg, ha))
      +l3 = cong(Maybe<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, t)), z), None{}, chk(~K, ~V, ~cmp, lw, up, Some{e}), Equal.sym(Maybe<&2, M.Entry<K, V>>, chk(~K, ~V, ~cmp, lw, up, Some{e}), None{}, chk_out(~K, ~V, ~cmp, lw, up, e, hir)))
      +r1 = cong(Maybe<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => chk(~K, ~V, ~cmp, lw, up, lbu(~K, ~V, ~cmp, up, t, z)), S.pick(Maybe<&2, M.Entry<K, V>>, S.below_upper(~K, ~cmp, S.key(K, V, e), up), Some{e}, bst), Some{e}, pk_t(Maybe<&2, M.Entry<K, V>>, S.below_upper(~K, ~cmp, S.key(K, V, e), up), Some{e}, bst, hb))
      Equal.trans(Maybe<&2, M.Entry<K, V>>, OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, Con{e, t})), chk(~K, ~V, ~cmp, lw, up, bst)), OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, t)), chk(~K, ~V, ~cmp, lw, up, bst)), chk(~K, ~V, ~cmp, lw, up, lbu(~K, ~V, ~cmp, up, Con{e, t}, bst)), l1, Equal.trans(Maybe<&2, M.Entry<K, V>>, OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, t)), chk(~K, ~V, ~cmp, lw, up, bst)), OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, t)), None{}), chk(~K, ~V, ~cmp, lw, up, lbu(~K, ~V, ~cmp, up, Con{e, t}, bst)), l2, Equal.trans(Maybe<&2, M.Entry<K, V>>, OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, t)), None{}), OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, t)), chk(~K, ~V, ~cmp, lw, up, Some{e})), chk(~K, ~V, ~cmp, lw, up, lbu(~K, ~V, ~cmp, up, Con{e, t}, bst)), l3, Equal.trans(Maybe<&2, M.Entry<K, V>>, OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, t)), chk(~K, ~V, ~cmp, lw, up, Some{e})), chk(~K, ~V, ~cmp, lw, up, lbu(~K, ~V, ~cmp, up, t, Some{e})), chk(~K, ~V, ~cmp, lw, up, lbu(~K, ~V, ~cmp, up, Con{e, t}, bst)), ih, Equal.sym(Maybe<&2, M.Entry<K, V>>, chk(~K, ~V, ~cmp, lw, up, lbu(~K, ~V, ~cmp, up, Con{e, t}, bst)), chk(~K, ~V, ~cmp, lw, up, lbu(~K, ~V, ~cmp, up, t, Some{e})), r1)))))
    case False{} False{}:
      +hir = ir_fb(~K, ~cmp, lw, up, S.key(K, V, e), hb)
      +hgt = OR.ord_gt(~K, ~V, ~cmp, ~o, t, e, h)
      +l1 = cong(List<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, z), chk(~K, ~V, ~cmp, lw, up, bst)), S.within(~K, ~V, ~cmp, lw, up, Con{e, t}), Nil{}, Equal.trans(List<&2, M.Entry<K, V>>, S.within(~K, ~V, ~cmp, lw, up, Con{e, t}), S.within(~K, ~V, ~cmp, lw, up, t), Nil{}, w_out(~K, ~V, ~cmp, lw, up, e, t, hir), wnil(~K, ~V, ~cmp, ~o, lw, up, S.key(K, V, e), t, hb, hgt)))
      +r1 = cong(Maybe<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => chk(~K, ~V, ~cmp, lw, up, lbu(~K, ~V, ~cmp, up, t, z)), S.pick(Maybe<&2, M.Entry<K, V>>, S.below_upper(~K, ~cmp, S.key(K, V, e), up), Some{e}, bst), bst, pk_f(Maybe<&2, M.Entry<K, V>>, S.below_upper(~K, ~cmp, S.key(K, V, e), up), Some{e}, bst, hb))
      +r2 = cong(Maybe<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => chk(~K, ~V, ~cmp, lw, up, z), lbu(~K, ~V, ~cmp, up, t, bst), bst, lbu_none(~K, ~V, ~cmp, ~o, up, S.key(K, V, e), t, bst, hb, hgt))
      Equal.trans(Maybe<&2, M.Entry<K, V>>, OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, Con{e, t})), chk(~K, ~V, ~cmp, lw, up, bst)), chk(~K, ~V, ~cmp, lw, up, bst), chk(~K, ~V, ~cmp, lw, up, lbu(~K, ~V, ~cmp, up, Con{e, t}, bst)), l1, Equal.sym(Maybe<&2, M.Entry<K, V>>, chk(~K, ~V, ~cmp, lw, up, lbu(~K, ~V, ~cmp, up, Con{e, t}, bst)), chk(~K, ~V, ~cmp, lw, up, bst), Equal.trans(Maybe<&2, M.Entry<K, V>>, chk(~K, ~V, ~cmp, lw, up, lbu(~K, ~V, ~cmp, up, Con{e, t}, bst)), chk(~K, ~V, ~cmp, lw, up, lbu(~K, ~V, ~cmp, up, t, bst)), chk(~K, ~V, ~cmp, lw, up, bst), r1, r2)))

def e2g(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +lw: M.Bound<K>, +up: M.Bound<K>, +es: List<&2, M.Entry<K, V>>, +bst: Maybe<&2, M.Entry<K, V>>, +h: {ST.ordered(~K, ~V, ~cmp, es) == True{} : Bool}, +hbg: {bgood(~K, ~V, ~cmp, bst, es) == True{} : Bool}) -> {OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, es)), chk(~K, ~V, ~cmp, lw, up, bst)) == chk(~K, ~V, ~cmp, lw, up, lbu(~K, ~V, ~cmp, up, es, bst)) : Maybe<&2, M.Entry<K, V>>}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      e2_c(~K, ~V, ~cmp, ~o, lw, up, e, t, bst, h, hbg, e2g(~K, ~V, ~cmp, ~o, lw, up, t, Some{e}, OR.ord_tail(~K, ~V, ~cmp, e, t, h), OR.ord_gt(~K, ~V, ~cmp, ~o, t, e, h)), S.above_lower(~K, ~cmp, S.key(K, V, e), lw), {==}, S.below_upper(~K, ~cmp, S.key(K, V, e), up), {==})

def last_within(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +lw: M.Bound<K>, +up: M.Bound<K>, +es: List<&2, M.Entry<K, V>>, +h: {ST.ordered(~K, ~V, ~cmp, es) == True{} : Bool}) -> {S.last(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, es)) == chk(~K, ~V, ~cmp, lw, up, lbu(~K, ~V, ~cmp, up, es, None{})) : Maybe<&2, M.Entry<K, V>>}:
  Equal.trans(Maybe<&2, M.Entry<K, V>>, S.last(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, es)), OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, es)), None{}), chk(~K, ~V, ~cmp, lw, up, lbu(~K, ~V, ~cmp, up, es, None{})), Equal.sym(Maybe<&2, M.Entry<K, V>>, OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, es)), None{}), S.last(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, es)), OR.orm_none(M.Entry<K, V>, S.last(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, es)))), e2g(~K, ~V, ~cmp, ~o, lw, up, es, None{}, h, {==}))

# ---- a search from a key inside the view: the whole map's, checked ----


# a failing first entry skipped, within or not
def fw_skip(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +lw: M.Bound<K>, +up: M.Bound<K>, +k: K, +incl: Bool, +e: M.Entry<K, V>, +t: List<&2, M.Entry<K, V>>, +hp: {S.ordering_ok(cmp(k, S.key(K, V, e)), incl) == False{} : Bool}, +c: Bool, +hc: {S.in_range(~K, ~cmp, S.key(K, V, e), lw, up) == c : Bool}) -> {S.first_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, Con{e, t})) == S.first_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, t)) : Maybe<&2, M.Entry<K, V>>}:
  match c:
    case True{}:
      Equal.trans(Maybe<&2, M.Entry<K, V>>, S.first_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, Con{e, t})), S.first_where(~K, ~V, ~cmp, k, incl, Con{e, S.within(~K, ~V, ~cmp, lw, up, t)}), S.first_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, t)), cong(List<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => S.first_where(~K, ~V, ~cmp, k, incl, z), S.within(~K, ~V, ~cmp, lw, up, Con{e, t}), Con{e, S.within(~K, ~V, ~cmp, lw, up, t)}, w_in(~K, ~V, ~cmp, lw, up, e, t, hc)), pk_f(Maybe<&2, M.Entry<K, V>>, S.ordering_ok(cmp(k, S.key(K, V, e)), incl), Some{e}, S.first_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, t)), hp))
    case False{}:
      cong(List<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => S.first_where(~K, ~V, ~cmp, k, incl, z), S.within(~K, ~V, ~cmp, lw, up, Con{e, t}), S.within(~K, ~V, ~cmp, lw, up, t), w_out(~K, ~V, ~cmp, lw, up, e, t, hc))

def n1_c(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +lw: M.Bound<K>, +up: M.Bound<K>, +k: K, +incl: Bool, +e: M.Entry<K, V>, +t: List<&2, M.Entry<K, V>>, +h: {ST.ordered(~K, ~V, ~cmp, Con{e, t}) == True{} : Bool}, +hk: {S.above_lower(~K, ~cmp, k, lw) == True{} : Bool}, +ih: {S.first_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, t)) == chk(~K, ~V, ~cmp, lw, up, S.first_where(~K, ~V, ~cmp, k, incl, t)) : Maybe<&2, M.Entry<K, V>>}, +pv: Bool, +hp: {S.ordering_ok(cmp(k, S.key(K, V, e)), incl) == pv : Bool}, +b: Bool, +hb: {S.below_upper(~K, ~cmp, S.key(K, V, e), up) == b : Bool}) -> {S.first_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, Con{e, t})) == chk(~K, ~V, ~cmp, lw, up, S.first_where(~K, ~V, ~cmp, k, incl, Con{e, t})) : Maybe<&2, M.Entry<K, V>>}:
  match pv b:
    case True{} True{}:
      +hir = ir_t(~K, ~cmp, lw, up, S.key(K, V, e), al_mono(~K, ~cmp, ~o, lw, k, S.key(K, V, e), incl, hk, hp), hb)
      +l1 = Equal.trans(Maybe<&2, M.Entry<K, V>>, S.first_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, Con{e, t})), S.first_where(~K, ~V, ~cmp, k, incl, Con{e, S.within(~K, ~V, ~cmp, lw, up, t)}), Some{e}, cong(List<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => S.first_where(~K, ~V, ~cmp, k, incl, z), S.within(~K, ~V, ~cmp, lw, up, Con{e, t}), Con{e, S.within(~K, ~V, ~cmp, lw, up, t)}, w_in(~K, ~V, ~cmp, lw, up, e, t, hir)), pk_t(Maybe<&2, M.Entry<K, V>>, S.ordering_ok(cmp(k, S.key(K, V, e)), incl), Some{e}, S.first_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, t)), hp))
      +r1 = Equal.trans(Maybe<&2, M.Entry<K, V>>, chk(~K, ~V, ~cmp, lw, up, S.first_where(~K, ~V, ~cmp, k, incl, Con{e, t})), chk(~K, ~V, ~cmp, lw, up, Some{e}), Some{e}, cong(Maybe<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => chk(~K, ~V, ~cmp, lw, up, z), S.first_where(~K, ~V, ~cmp, k, incl, Con{e, t}), Some{e}, pk_t(Maybe<&2, M.Entry<K, V>>, S.ordering_ok(cmp(k, S.key(K, V, e)), incl), Some{e}, S.first_where(~K, ~V, ~cmp, k, incl, t), hp)), chk_in(~K, ~V, ~cmp, lw, up, e, hir))
      Equal.trans(Maybe<&2, M.Entry<K, V>>, S.first_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, Con{e, t})), Some{e}, chk(~K, ~V, ~cmp, lw, up, S.first_where(~K, ~V, ~cmp, k, incl, Con{e, t})), l1, Equal.sym(Maybe<&2, M.Entry<K, V>>, chk(~K, ~V, ~cmp, lw, up, S.first_where(~K, ~V, ~cmp, k, incl, Con{e, t})), Some{e}, r1))
    case True{} False{}:
      +hir = ir_fb(~K, ~cmp, lw, up, S.key(K, V, e), hb)
      +l1 = Equal.trans(Maybe<&2, M.Entry<K, V>>, S.first_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, Con{e, t})), S.first_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, t)), None{}, cong(List<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => S.first_where(~K, ~V, ~cmp, k, incl, z), S.within(~K, ~V, ~cmp, lw, up, Con{e, t}), S.within(~K, ~V, ~cmp, lw, up, t), w_out(~K, ~V, ~cmp, lw, up, e, t, hir)), cong(List<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => S.first_where(~K, ~V, ~cmp, k, incl, z), S.within(~K, ~V, ~cmp, lw, up, t), Nil{}, wnil(~K, ~V, ~cmp, ~o, lw, up, S.key(K, V, e), t, hb, OR.ord_gt(~K, ~V, ~cmp, ~o, t, e, h))))
      +r1 = Equal.trans(Maybe<&2, M.Entry<K, V>>, chk(~K, ~V, ~cmp, lw, up, S.first_where(~K, ~V, ~cmp, k, incl, Con{e, t})), chk(~K, ~V, ~cmp, lw, up, Some{e}), None{}, cong(Maybe<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => chk(~K, ~V, ~cmp, lw, up, z), S.first_where(~K, ~V, ~cmp, k, incl, Con{e, t}), Some{e}, pk_t(Maybe<&2, M.Entry<K, V>>, S.ordering_ok(cmp(k, S.key(K, V, e)), incl), Some{e}, S.first_where(~K, ~V, ~cmp, k, incl, t), hp)), chk_out(~K, ~V, ~cmp, lw, up, e, hir))
      Equal.trans(Maybe<&2, M.Entry<K, V>>, S.first_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, Con{e, t})), None{}, chk(~K, ~V, ~cmp, lw, up, S.first_where(~K, ~V, ~cmp, k, incl, Con{e, t})), l1, Equal.sym(Maybe<&2, M.Entry<K, V>>, chk(~K, ~V, ~cmp, lw, up, S.first_where(~K, ~V, ~cmp, k, incl, Con{e, t})), None{}, r1))
    case False{} True{}:
      +r1 = cong(Maybe<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => chk(~K, ~V, ~cmp, lw, up, z), S.first_where(~K, ~V, ~cmp, k, incl, Con{e, t}), S.first_where(~K, ~V, ~cmp, k, incl, t), pk_f(Maybe<&2, M.Entry<K, V>>, S.ordering_ok(cmp(k, S.key(K, V, e)), incl), Some{e}, S.first_where(~K, ~V, ~cmp, k, incl, t), hp))
      Equal.trans(Maybe<&2, M.Entry<K, V>>, S.first_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, Con{e, t})), chk(~K, ~V, ~cmp, lw, up, S.first_where(~K, ~V, ~cmp, k, incl, t)), chk(~K, ~V, ~cmp, lw, up, S.first_where(~K, ~V, ~cmp, k, incl, Con{e, t})), Equal.trans(Maybe<&2, M.Entry<K, V>>, S.first_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, Con{e, t})), S.first_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, t)), chk(~K, ~V, ~cmp, lw, up, S.first_where(~K, ~V, ~cmp, k, incl, t)), fw_skip(~K, ~V, ~cmp, ~o, lw, up, k, incl, e, t, hp, S.in_range(~K, ~cmp, S.key(K, V, e), lw, up), {==}), ih), Equal.sym(Maybe<&2, M.Entry<K, V>>, chk(~K, ~V, ~cmp, lw, up, S.first_where(~K, ~V, ~cmp, k, incl, Con{e, t})), chk(~K, ~V, ~cmp, lw, up, S.first_where(~K, ~V, ~cmp, k, incl, t)), r1))
    case False{} False{}:
      +r1 = cong(Maybe<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => chk(~K, ~V, ~cmp, lw, up, z), S.first_where(~K, ~V, ~cmp, k, incl, Con{e, t}), S.first_where(~K, ~V, ~cmp, k, incl, t), pk_f(Maybe<&2, M.Entry<K, V>>, S.ordering_ok(cmp(k, S.key(K, V, e)), incl), Some{e}, S.first_where(~K, ~V, ~cmp, k, incl, t), hp))
      Equal.trans(Maybe<&2, M.Entry<K, V>>, S.first_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, Con{e, t})), chk(~K, ~V, ~cmp, lw, up, S.first_where(~K, ~V, ~cmp, k, incl, t)), chk(~K, ~V, ~cmp, lw, up, S.first_where(~K, ~V, ~cmp, k, incl, Con{e, t})), Equal.trans(Maybe<&2, M.Entry<K, V>>, S.first_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, Con{e, t})), S.first_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, t)), chk(~K, ~V, ~cmp, lw, up, S.first_where(~K, ~V, ~cmp, k, incl, t)), fw_skip(~K, ~V, ~cmp, ~o, lw, up, k, incl, e, t, hp, S.in_range(~K, ~cmp, S.key(K, V, e), lw, up), {==}), ih), Equal.sym(Maybe<&2, M.Entry<K, V>>, chk(~K, ~V, ~cmp, lw, up, S.first_where(~K, ~V, ~cmp, k, incl, Con{e, t})), chk(~K, ~V, ~cmp, lw, up, S.first_where(~K, ~V, ~cmp, k, incl, t)), r1))

# from a key above the lower bound, the first at or past it within is the
# first in the map, when in range
def fw_within(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +lw: M.Bound<K>, +up: M.Bound<K>, +k: K, +incl: Bool, +es: List<&2, M.Entry<K, V>>, +h: {ST.ordered(~K, ~V, ~cmp, es) == True{} : Bool}, +hk: {S.above_lower(~K, ~cmp, k, lw) == True{} : Bool}) -> {S.first_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, es)) == chk(~K, ~V, ~cmp, lw, up, S.first_where(~K, ~V, ~cmp, k, incl, es)) : Maybe<&2, M.Entry<K, V>>}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      n1_c(~K, ~V, ~cmp, ~o, lw, up, k, incl, e, t, h, hk, fw_within(~K, ~V, ~cmp, ~o, lw, up, k, incl, t, OR.ord_tail(~K, ~V, ~cmp, e, t, h), hk), S.ordering_ok(cmp(k, S.key(K, V, e)), incl), {==}, S.below_upper(~K, ~cmp, S.key(K, V, e), up), {==})

# from a key below the lower bound, the first within
def fw_below(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +lw: M.Bound<K>, +up: M.Bound<K>, +k: K, +incl: Bool, +es: List<&2, M.Entry<K, V>>, +hk: {S.above_lower(~K, ~cmp, k, lw) == False{} : Bool}) -> {S.first_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, es)) == S.head(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, es)) : Maybe<&2, M.Entry<K, V>>}:
  NV.fw_head(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, es), wgt(~K, ~V, ~cmp, ~o, lw, up, k, es, hk))

def lw_skip(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +lw: M.Bound<K>, +up: M.Bound<K>, +k: K, +incl: Bool, +e: M.Entry<K, V>, +t: List<&2, M.Entry<K, V>>, +m: Maybe<&2, M.Entry<K, V>>, +hq: {S.ordering_ok(cmp(S.key(K, V, e), k), incl) == False{} : Bool}, +c: Bool, +hc: {S.in_range(~K, ~cmp, S.key(K, V, e), lw, up) == c : Bool}) -> {S.last_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, Con{e, t}), m) == S.last_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, t), m) : Maybe<&2, M.Entry<K, V>>}:
  match c:
    case True{}:
      Equal.trans(Maybe<&2, M.Entry<K, V>>, S.last_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, Con{e, t}), m), S.last_where(~K, ~V, ~cmp, k, incl, Con{e, S.within(~K, ~V, ~cmp, lw, up, t)}, m), S.last_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, t), m), cong(List<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => S.last_where(~K, ~V, ~cmp, k, incl, z, m), S.within(~K, ~V, ~cmp, lw, up, Con{e, t}), Con{e, S.within(~K, ~V, ~cmp, lw, up, t)}, w_in(~K, ~V, ~cmp, lw, up, e, t, hc)), cong(Maybe<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => S.last_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, t), z), S.pick(Maybe<&2, M.Entry<K, V>>, S.ordering_ok(cmp(S.key(K, V, e), k), incl), Some{e}, m), m, pk_f(Maybe<&2, M.Entry<K, V>>, S.ordering_ok(cmp(S.key(K, V, e), k), incl), Some{e}, m, hq)))
    case False{}:
      cong(List<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => S.last_where(~K, ~V, ~cmp, k, incl, z, m), S.within(~K, ~V, ~cmp, lw, up, Con{e, t}), S.within(~K, ~V, ~cmp, lw, up, t), w_out(~K, ~V, ~cmp, lw, up, e, t, hc))


def n3_c(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +lw: M.Bound<K>, +up: M.Bound<K>, +k: K, +incl: Bool, +e: M.Entry<K, V>, +t: List<&2, M.Entry<K, V>>, +bst: Maybe<&2, M.Entry<K, V>>, +h: {ST.ordered(~K, ~V, ~cmp, Con{e, t}) == True{} : Bool}, +hbg: {bgood(~K, ~V, ~cmp, bst, Con{e, t}) == True{} : Bool}, +hk: {S.below_upper(~K, ~cmp, k, up) == True{} : Bool}, +ih1: {S.last_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, t), chk(~K, ~V, ~cmp, lw, up, Some{e})) == chk(~K, ~V, ~cmp, lw, up, S.last_where(~K, ~V, ~cmp, k, incl, t, Some{e})) : Maybe<&2, M.Entry<K, V>>}, +ih2: {S.last_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, t), chk(~K, ~V, ~cmp, lw, up, bst)) == chk(~K, ~V, ~cmp, lw, up, S.last_where(~K, ~V, ~cmp, k, incl, t, bst)) : Maybe<&2, M.Entry<K, V>>}, +qv: Bool, +hq: {S.ordering_ok(cmp(S.key(K, V, e), k), incl) == qv : Bool}, +a: Bool, +ha: {S.above_lower(~K, ~cmp, S.key(K, V, e), lw) == a : Bool}) -> {S.last_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, Con{e, t}), chk(~K, ~V, ~cmp, lw, up, bst)) == chk(~K, ~V, ~cmp, lw, up, S.last_where(~K, ~V, ~cmp, k, incl, Con{e, t}, bst)) : Maybe<&2, M.Entry<K, V>>}:
  match qv a:
    case True{} True{}:
      +hir = ir_t(~K, ~cmp, lw, up, S.key(K, V, e), ha, bu_mono(~K, ~cmp, ~o, up, k, S.key(K, V, e), incl, hk, hq))
      +l1 = cong(List<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => S.last_where(~K, ~V, ~cmp, k, incl, z, chk(~K, ~V, ~cmp, lw, up, bst)), S.within(~K, ~V, ~cmp, lw, up, Con{e, t}), Con{e, S.within(~K, ~V, ~cmp, lw, up, t)}, w_in(~K, ~V, ~cmp, lw, up, e, t, hir))
      +l2 = cong(Maybe<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => S.last_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, t), z), S.pick(Maybe<&2, M.Entry<K, V>>, S.ordering_ok(cmp(S.key(K, V, e), k), incl), Some{e}, chk(~K, ~V, ~cmp, lw, up, bst)), chk(~K, ~V, ~cmp, lw, up, Some{e}), Equal.trans(Maybe<&2, M.Entry<K, V>>, S.pick(Maybe<&2, M.Entry<K, V>>, S.ordering_ok(cmp(S.key(K, V, e), k), incl), Some{e}, chk(~K, ~V, ~cmp, lw, up, bst)), Some{e}, chk(~K, ~V, ~cmp, lw, up, Some{e}), pk_t(Maybe<&2, M.Entry<K, V>>, S.ordering_ok(cmp(S.key(K, V, e), k), incl), Some{e}, chk(~K, ~V, ~cmp, lw, up, bst), hq), Equal.sym(Maybe<&2, M.Entry<K, V>>, chk(~K, ~V, ~cmp, lw, up, Some{e}), Some{e}, chk_in(~K, ~V, ~cmp, lw, up, e, hir))))
      +r1 = cong(Maybe<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => chk(~K, ~V, ~cmp, lw, up, S.last_where(~K, ~V, ~cmp, k, incl, t, z)), S.pick(Maybe<&2, M.Entry<K, V>>, S.ordering_ok(cmp(S.key(K, V, e), k), incl), Some{e}, bst), Some{e}, pk_t(Maybe<&2, M.Entry<K, V>>, S.ordering_ok(cmp(S.key(K, V, e), k), incl), Some{e}, bst, hq))
      Equal.trans(Maybe<&2, M.Entry<K, V>>, S.last_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, Con{e, t}), chk(~K, ~V, ~cmp, lw, up, bst)), S.last_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, t), chk(~K, ~V, ~cmp, lw, up, Some{e})), chk(~K, ~V, ~cmp, lw, up, S.last_where(~K, ~V, ~cmp, k, incl, Con{e, t}, bst)), Equal.trans(Maybe<&2, M.Entry<K, V>>, S.last_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, Con{e, t}), chk(~K, ~V, ~cmp, lw, up, bst)), S.last_where(~K, ~V, ~cmp, k, incl, Con{e, S.within(~K, ~V, ~cmp, lw, up, t)}, chk(~K, ~V, ~cmp, lw, up, bst)), S.last_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, t), chk(~K, ~V, ~cmp, lw, up, Some{e})), l1, l2), Equal.trans(Maybe<&2, M.Entry<K, V>>, S.last_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, t), chk(~K, ~V, ~cmp, lw, up, Some{e})), chk(~K, ~V, ~cmp, lw, up, S.last_where(~K, ~V, ~cmp, k, incl, t, Some{e})), chk(~K, ~V, ~cmp, lw, up, S.last_where(~K, ~V, ~cmp, k, incl, Con{e, t}, bst)), ih1, Equal.sym(Maybe<&2, M.Entry<K, V>>, chk(~K, ~V, ~cmp, lw, up, S.last_where(~K, ~V, ~cmp, k, incl, Con{e, t}, bst)), chk(~K, ~V, ~cmp, lw, up, S.last_where(~K, ~V, ~cmp, k, incl, t, Some{e})), r1)))
    case True{} False{}:
      +hir = ir_fa(~K, ~cmp, lw, up, S.key(K, V, e), ha)
      +l1 = cong(List<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => S.last_where(~K, ~V, ~cmp, k, incl, z, chk(~K, ~V, ~cmp, lw, up, bst)), S.within(~K, ~V, ~cmp, lw, up, Con{e, t}), S.within(~K, ~V, ~cmp, lw, up, t), w_out(~K, ~V, ~cmp, lw, up, e, t, hir))
      +l2 = cong(Maybe<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => S.last_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, t), z), chk(~K, ~V, ~cmp, lw, up, bst), chk(~K, ~V, ~cmp, lw, up, Some{e}), Equal.trans(Maybe<&2, M.Entry<K, V>>, chk(~K, ~V, ~cmp, lw, up, bst), None{}, chk(~K, ~V, ~cmp, lw, up, Some{e}), chk_none(~K, ~V, ~cmp, ~o, lw, up, bst, e, t, hbg, ha), Equal.sym(Maybe<&2, M.Entry<K, V>>, chk(~K, ~V, ~cmp, lw, up, Some{e}), None{}, chk_out(~K, ~V, ~cmp, lw, up, e, hir))))
      +r1 = cong(Maybe<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => chk(~K, ~V, ~cmp, lw, up, S.last_where(~K, ~V, ~cmp, k, incl, t, z)), S.pick(Maybe<&2, M.Entry<K, V>>, S.ordering_ok(cmp(S.key(K, V, e), k), incl), Some{e}, bst), Some{e}, pk_t(Maybe<&2, M.Entry<K, V>>, S.ordering_ok(cmp(S.key(K, V, e), k), incl), Some{e}, bst, hq))
      Equal.trans(Maybe<&2, M.Entry<K, V>>, S.last_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, Con{e, t}), chk(~K, ~V, ~cmp, lw, up, bst)), S.last_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, t), chk(~K, ~V, ~cmp, lw, up, Some{e})), chk(~K, ~V, ~cmp, lw, up, S.last_where(~K, ~V, ~cmp, k, incl, Con{e, t}, bst)), Equal.trans(Maybe<&2, M.Entry<K, V>>, S.last_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, Con{e, t}), chk(~K, ~V, ~cmp, lw, up, bst)), S.last_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, t), chk(~K, ~V, ~cmp, lw, up, bst)), S.last_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, t), chk(~K, ~V, ~cmp, lw, up, Some{e})), l1, l2), Equal.trans(Maybe<&2, M.Entry<K, V>>, S.last_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, t), chk(~K, ~V, ~cmp, lw, up, Some{e})), chk(~K, ~V, ~cmp, lw, up, S.last_where(~K, ~V, ~cmp, k, incl, t, Some{e})), chk(~K, ~V, ~cmp, lw, up, S.last_where(~K, ~V, ~cmp, k, incl, Con{e, t}, bst)), ih1, Equal.sym(Maybe<&2, M.Entry<K, V>>, chk(~K, ~V, ~cmp, lw, up, S.last_where(~K, ~V, ~cmp, k, incl, Con{e, t}, bst)), chk(~K, ~V, ~cmp, lw, up, S.last_where(~K, ~V, ~cmp, k, incl, t, Some{e})), r1)))
    case False{} True{}:
      +r1 = cong(Maybe<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => chk(~K, ~V, ~cmp, lw, up, S.last_where(~K, ~V, ~cmp, k, incl, t, z)), S.pick(Maybe<&2, M.Entry<K, V>>, S.ordering_ok(cmp(S.key(K, V, e), k), incl), Some{e}, bst), bst, pk_f(Maybe<&2, M.Entry<K, V>>, S.ordering_ok(cmp(S.key(K, V, e), k), incl), Some{e}, bst, hq))
      Equal.trans(Maybe<&2, M.Entry<K, V>>, S.last_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, Con{e, t}), chk(~K, ~V, ~cmp, lw, up, bst)), chk(~K, ~V, ~cmp, lw, up, S.last_where(~K, ~V, ~cmp, k, incl, t, bst)), chk(~K, ~V, ~cmp, lw, up, S.last_where(~K, ~V, ~cmp, k, incl, Con{e, t}, bst)), Equal.trans(Maybe<&2, M.Entry<K, V>>, S.last_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, Con{e, t}), chk(~K, ~V, ~cmp, lw, up, bst)), S.last_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, t), chk(~K, ~V, ~cmp, lw, up, bst)), chk(~K, ~V, ~cmp, lw, up, S.last_where(~K, ~V, ~cmp, k, incl, t, bst)), lw_skip(~K, ~V, ~cmp, ~o, lw, up, k, incl, e, t, chk(~K, ~V, ~cmp, lw, up, bst), hq, S.in_range(~K, ~cmp, S.key(K, V, e), lw, up), {==}), ih2), Equal.sym(Maybe<&2, M.Entry<K, V>>, chk(~K, ~V, ~cmp, lw, up, S.last_where(~K, ~V, ~cmp, k, incl, Con{e, t}, bst)), chk(~K, ~V, ~cmp, lw, up, S.last_where(~K, ~V, ~cmp, k, incl, t, bst)), r1))
    case False{} False{}:
      +r1 = cong(Maybe<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => chk(~K, ~V, ~cmp, lw, up, S.last_where(~K, ~V, ~cmp, k, incl, t, z)), S.pick(Maybe<&2, M.Entry<K, V>>, S.ordering_ok(cmp(S.key(K, V, e), k), incl), Some{e}, bst), bst, pk_f(Maybe<&2, M.Entry<K, V>>, S.ordering_ok(cmp(S.key(K, V, e), k), incl), Some{e}, bst, hq))
      Equal.trans(Maybe<&2, M.Entry<K, V>>, S.last_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, Con{e, t}), chk(~K, ~V, ~cmp, lw, up, bst)), chk(~K, ~V, ~cmp, lw, up, S.last_where(~K, ~V, ~cmp, k, incl, t, bst)), chk(~K, ~V, ~cmp, lw, up, S.last_where(~K, ~V, ~cmp, k, incl, Con{e, t}, bst)), Equal.trans(Maybe<&2, M.Entry<K, V>>, S.last_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, Con{e, t}), chk(~K, ~V, ~cmp, lw, up, bst)), S.last_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, t), chk(~K, ~V, ~cmp, lw, up, bst)), chk(~K, ~V, ~cmp, lw, up, S.last_where(~K, ~V, ~cmp, k, incl, t, bst)), lw_skip(~K, ~V, ~cmp, ~o, lw, up, k, incl, e, t, chk(~K, ~V, ~cmp, lw, up, bst), hq, S.in_range(~K, ~cmp, S.key(K, V, e), lw, up), {==}), ih2), Equal.sym(Maybe<&2, M.Entry<K, V>>, chk(~K, ~V, ~cmp, lw, up, S.last_where(~K, ~V, ~cmp, k, incl, Con{e, t}, bst)), chk(~K, ~V, ~cmp, lw, up, S.last_where(~K, ~V, ~cmp, k, incl, t, bst)), r1))

def n3g(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +lw: M.Bound<K>, +up: M.Bound<K>, +k: K, +incl: Bool, +es: List<&2, M.Entry<K, V>>, +bst: Maybe<&2, M.Entry<K, V>>, +h: {ST.ordered(~K, ~V, ~cmp, es) == True{} : Bool}, +hbg: {bgood(~K, ~V, ~cmp, bst, es) == True{} : Bool}, +hk: {S.below_upper(~K, ~cmp, k, up) == True{} : Bool}) -> {S.last_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, es), chk(~K, ~V, ~cmp, lw, up, bst)) == chk(~K, ~V, ~cmp, lw, up, S.last_where(~K, ~V, ~cmp, k, incl, es, bst)) : Maybe<&2, M.Entry<K, V>>}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      n3_c(~K, ~V, ~cmp, ~o, lw, up, k, incl, e, t, bst, h, hbg, hk, n3g(~K, ~V, ~cmp, ~o, lw, up, k, incl, t, Some{e}, OR.ord_tail(~K, ~V, ~cmp, e, t, h), OR.ord_gt(~K, ~V, ~cmp, ~o, t, e, h), hk), n3g(~K, ~V, ~cmp, ~o, lw, up, k, incl, t, bst, OR.ord_tail(~K, ~V, ~cmp, e, t, h), bg_tail(~K, ~V, ~cmp, bst, e, t, hbg), hk), S.ordering_ok(cmp(S.key(K, V, e), k), incl), {==}, S.above_lower(~K, ~cmp, S.key(K, V, e), lw), {==})

# from a key below the upper bound, the last at or before it within is the
# last in the map, when in range
def lw_within(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +lw: M.Bound<K>, +up: M.Bound<K>, +k: K, +incl: Bool, +es: List<&2, M.Entry<K, V>>, +h: {ST.ordered(~K, ~V, ~cmp, es) == True{} : Bool}, +hk: {S.below_upper(~K, ~cmp, k, up) == True{} : Bool}) -> {S.last_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, es), None{}) == chk(~K, ~V, ~cmp, lw, up, S.last_where(~K, ~V, ~cmp, k, incl, es, None{})) : Maybe<&2, M.Entry<K, V>>}:
  n3g(~K, ~V, ~cmp, ~o, lw, up, k, incl, es, None{}, h, {==}, hk)

# from a key above the upper bound, the last within
def lw_above(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +lw: M.Bound<K>, +up: M.Bound<K>, +k: K, +incl: Bool, +es: List<&2, M.Entry<K, V>>, +hk: {S.below_upper(~K, ~cmp, k, up) == False{} : Bool}) -> {S.last_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, es), None{}) == S.last(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, es)) : Maybe<&2, M.Entry<K, V>>}:
  Equal.trans(Maybe<&2, M.Entry<K, V>>, S.last_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, es), None{}), OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, es)), None{}), S.last(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, es)), NV.lw_all(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lw, up, es), None{}, wlt(~K, ~V, ~cmp, ~o, lw, up, k, es, hk)), OR.orm_none(M.Entry<K, V>, S.last(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, es))))

# ---- the bounds' own searches ----

def fal_u(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +es: List<&2, M.Entry<K, V>>) -> {fal(~K, ~V, ~cmp, M.Unbounded{}, es) == S.head(M.Entry<K, V>, es) : Maybe<&2, M.Entry<K, V>>}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      {==}

def fal_i(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +x: K, +es: List<&2, M.Entry<K, V>>) -> {fal(~K, ~V, ~cmp, M.Inclusive{x}, es) == S.first_where(~K, ~V, ~cmp, x, True{}, es) : Maybe<&2, M.Entry<K, V>>}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      cong(Maybe<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => S.pick(Maybe<&2, M.Entry<K, V>>, S.ordering_ok(cmp(x, S.key(K, V, e)), True{}), Some{e}, z), fal(~K, ~V, ~cmp, M.Inclusive{x}, t), S.first_where(~K, ~V, ~cmp, x, True{}, t), fal_i(~K, ~V, ~cmp, x, t))

def fal_x(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +x: K, +es: List<&2, M.Entry<K, V>>) -> {fal(~K, ~V, ~cmp, M.Exclusive{x}, es) == S.first_where(~K, ~V, ~cmp, x, False{}, es) : Maybe<&2, M.Entry<K, V>>}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      cong(Maybe<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => S.pick(Maybe<&2, M.Entry<K, V>>, S.ordering_ok(cmp(x, S.key(K, V, e)), False{}), Some{e}, z), fal(~K, ~V, ~cmp, M.Exclusive{x}, t), S.first_where(~K, ~V, ~cmp, x, False{}, t), fal_x(~K, ~V, ~cmp, x, t))

def lbu_u(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +es: List<&2, M.Entry<K, V>>, +b: Maybe<&2, M.Entry<K, V>>) -> {lbu(~K, ~V, ~cmp, M.Unbounded{}, es, b) == OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, es), b) : Maybe<&2, M.Entry<K, V>>}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      Equal.trans(Maybe<&2, M.Entry<K, V>>, lbu(~K, ~V, ~cmp, M.Unbounded{}, t, Some{e}), OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, t), Some{e}), OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, Con{e, t}), b), lbu_u(~K, ~V, ~cmp, t, Some{e}), NV.lw_all_c(K, V, e, t, b))

def lbu_i(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +y: K, +es: List<&2, M.Entry<K, V>>, +b: Maybe<&2, M.Entry<K, V>>) -> {lbu(~K, ~V, ~cmp, M.Inclusive{y}, es, b) == S.last_where(~K, ~V, ~cmp, y, True{}, es, b) : Maybe<&2, M.Entry<K, V>>}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      lbu_i(~K, ~V, ~cmp, y, t, S.pick(Maybe<&2, M.Entry<K, V>>, S.ordering_ok(cmp(S.key(K, V, e), y), True{}), Some{e}, b))

def lbu_x(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +y: K, +es: List<&2, M.Entry<K, V>>, +b: Maybe<&2, M.Entry<K, V>>) -> {lbu(~K, ~V, ~cmp, M.Exclusive{y}, es, b) == S.last_where(~K, ~V, ~cmp, y, False{}, es, b) : Maybe<&2, M.Entry<K, V>>}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      lbu_x(~K, ~V, ~cmp, y, t, S.pick(Maybe<&2, M.Entry<K, V>>, S.ordering_ok(cmp(S.key(K, V, e), y), False{}), Some{e}, b))

# ---- runs of entries ----


def wapp_c(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +lw: M.Bound<K>, +up: M.Bound<K>, +e: M.Entry<K, V>, +t: List<&2, M.Entry<K, V>>, +ys: List<&2, M.Entry<K, V>>, +ih: {S.within(~K, ~V, ~cmp, lw, up, SC.append(M.Entry<K, V>, t, ys)) == SC.append(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, t), S.within(~K, ~V, ~cmp, lw, up, ys)) : List<&2, M.Entry<K, V>>}, +b: Bool, +hb: {S.in_range(~K, ~cmp, S.key(K, V, e), lw, up) == b : Bool}) -> {S.within(~K, ~V, ~cmp, lw, up, SC.append(M.Entry<K, V>, Con{e, t}, ys)) == SC.append(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, Con{e, t}), S.within(~K, ~V, ~cmp, lw, up, ys)) : List<&2, M.Entry<K, V>>}:
  match b:
    case True{}:
      +l1 = w_in(~K, ~V, ~cmp, lw, up, e, SC.append(M.Entry<K, V>, t, ys), hb)
      +r1 = cong(List<&2, M.Entry<K, V>>, List<&2, M.Entry<K, V>>, z => SC.append(M.Entry<K, V>, z, S.within(~K, ~V, ~cmp, lw, up, ys)), S.within(~K, ~V, ~cmp, lw, up, Con{e, t}), Con{e, S.within(~K, ~V, ~cmp, lw, up, t)}, w_in(~K, ~V, ~cmp, lw, up, e, t, hb))
      Equal.trans(List<&2, M.Entry<K, V>>, S.within(~K, ~V, ~cmp, lw, up, SC.append(M.Entry<K, V>, Con{e, t}, ys)), Con{e, SC.append(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, t), S.within(~K, ~V, ~cmp, lw, up, ys))}, SC.append(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, Con{e, t}), S.within(~K, ~V, ~cmp, lw, up, ys)), Equal.trans(List<&2, M.Entry<K, V>>, S.within(~K, ~V, ~cmp, lw, up, SC.append(M.Entry<K, V>, Con{e, t}, ys)), Con{e, S.within(~K, ~V, ~cmp, lw, up, SC.append(M.Entry<K, V>, t, ys))}, Con{e, SC.append(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, t), S.within(~K, ~V, ~cmp, lw, up, ys))}, l1, cong(List<&2, M.Entry<K, V>>, List<&2, M.Entry<K, V>>, z => Con{e, z}, S.within(~K, ~V, ~cmp, lw, up, SC.append(M.Entry<K, V>, t, ys)), SC.append(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, t), S.within(~K, ~V, ~cmp, lw, up, ys)), ih)), Equal.sym(List<&2, M.Entry<K, V>>, SC.append(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, Con{e, t}), S.within(~K, ~V, ~cmp, lw, up, ys)), Con{e, SC.append(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, t), S.within(~K, ~V, ~cmp, lw, up, ys))}, r1))
    case False{}:
      +l1 = w_out(~K, ~V, ~cmp, lw, up, e, SC.append(M.Entry<K, V>, t, ys), hb)
      +r1 = cong(List<&2, M.Entry<K, V>>, List<&2, M.Entry<K, V>>, z => SC.append(M.Entry<K, V>, z, S.within(~K, ~V, ~cmp, lw, up, ys)), S.within(~K, ~V, ~cmp, lw, up, Con{e, t}), S.within(~K, ~V, ~cmp, lw, up, t), w_out(~K, ~V, ~cmp, lw, up, e, t, hb))
      Equal.trans(List<&2, M.Entry<K, V>>, S.within(~K, ~V, ~cmp, lw, up, SC.append(M.Entry<K, V>, Con{e, t}, ys)), SC.append(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, t), S.within(~K, ~V, ~cmp, lw, up, ys)), SC.append(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, Con{e, t}), S.within(~K, ~V, ~cmp, lw, up, ys)), Equal.trans(List<&2, M.Entry<K, V>>, S.within(~K, ~V, ~cmp, lw, up, SC.append(M.Entry<K, V>, Con{e, t}, ys)), S.within(~K, ~V, ~cmp, lw, up, SC.append(M.Entry<K, V>, t, ys)), SC.append(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, t), S.within(~K, ~V, ~cmp, lw, up, ys)), l1, ih), Equal.sym(List<&2, M.Entry<K, V>>, SC.append(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, Con{e, t}), S.within(~K, ~V, ~cmp, lw, up, ys)), SC.append(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, t), S.within(~K, ~V, ~cmp, lw, up, ys)), r1))

def within_app(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +lw: M.Bound<K>, +up: M.Bound<K>, +xs: List<&2, M.Entry<K, V>>, +ys: List<&2, M.Entry<K, V>>) -> {S.within(~K, ~V, ~cmp, lw, up, SC.append(M.Entry<K, V>, xs, ys)) == SC.append(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lw, up, xs), S.within(~K, ~V, ~cmp, lw, up, ys)) : List<&2, M.Entry<K, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      wapp_c(~K, ~V, ~cmp, lw, up, e, t, ys, within_app(~K, ~V, ~cmp, lw, up, t, ys), S.in_range(~K, ~cmp, S.key(K, V, e), lw, up), {==})

# every entry above the lower bound / below the upper bound
def allal(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +lw: M.Bound<K>, es: List<&2, M.Entry<K, V>>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{+e, t}:
      Bool.and(S.above_lower(~K, ~cmp, S.key(K, V, e), lw), allal(~K, ~V, ~cmp, lw, t))

def allbu(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +up: M.Bound<K>, es: List<&2, M.Entry<K, V>>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{+e, t}:
      Bool.and(S.below_upper(~K, ~cmp, S.key(K, V, e), up), allbu(~K, ~V, ~cmp, up, t))

# sorted, the first above the lower bound: all are
def al_all(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +lw: M.Bound<K>, +t: List<&2, M.Entry<K, V>>, +e: M.Entry<K, V>, +h: {ST.ordered(~K, ~V, ~cmp, Con{e, t}) == True{} : Bool}, +ha: {S.above_lower(~K, ~cmp, S.key(K, V, e), lw) == True{} : Bool}) -> {allal(~K, ~V, ~cmp, lw, Con{e, t}) == True{} : Bool}:
  match t:
    case Nil{}:
      L.and_intro(S.above_lower(~K, ~cmp, S.key(K, V, e), lw), True{}, ha, {==})
    case Con{+f, +u}:
      +hlt = L.and_left(Cmp.is_lt(cmp(S.key(K, V, e), S.key(K, V, f))), ST.ordered(~K, ~V, ~cmp, Con{f, u}), h)
      +hf = al_mono(~K, ~cmp, ~o, lw, S.key(K, V, e), S.key(K, V, f), False{}, ha, lt_okf(cmp(S.key(K, V, e), S.key(K, V, f)), hlt))
      L.and_intro(S.above_lower(~K, ~cmp, S.key(K, V, e), lw), allal(~K, ~V, ~cmp, lw, Con{f, u}), ha, al_all(~K, ~V, ~cmp, ~o, lw, u, f, L.and_right(Cmp.is_lt(cmp(S.key(K, V, e), S.key(K, V, f))), ST.ordered(~K, ~V, ~cmp, Con{f, u}), h), hf))

def allbu_app(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +up: M.Bound<K>, +xs: List<&2, M.Entry<K, V>>, +ys: List<&2, M.Entry<K, V>>, +hx: {allbu(~K, ~V, ~cmp, up, xs) == True{} : Bool}, +hy: {allbu(~K, ~V, ~cmp, up, ys) == True{} : Bool}) -> {allbu(~K, ~V, ~cmp, up, SC.append(M.Entry<K, V>, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case Con{+e, +t}:
      L.and_intro(S.below_upper(~K, ~cmp, S.key(K, V, e), up), allbu(~K, ~V, ~cmp, up, SC.append(M.Entry<K, V>, t, ys)), L.and_left(S.below_upper(~K, ~cmp, S.key(K, V, e), up), allbu(~K, ~V, ~cmp, up, t), hx), allbu_app(~K, ~V, ~cmp, up, t, ys, L.and_right(S.below_upper(~K, ~cmp, S.key(K, V, e), up), allbu(~K, ~V, ~cmp, up, t), hx), hy))

def allbu_rev(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +up: M.Bound<K>, +xs: List<&2, M.Entry<K, V>>, +h: {allbu(~K, ~V, ~cmp, up, xs) == True{} : Bool}) -> {allbu(~K, ~V, ~cmp, up, SC.reverse(M.Entry<K, V>, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      +h1 = allbu_app(~K, ~V, ~cmp, up, SC.reverse(M.Entry<K, V>, t), Con{e, Nil{}}, allbu_rev(~K, ~V, ~cmp, up, t, L.and_right(S.below_upper(~K, ~cmp, S.key(K, V, e), up), allbu(~K, ~V, ~cmp, up, t), h)), L.and_intro(S.below_upper(~K, ~cmp, S.key(K, V, e), up), True{}, L.and_left(S.below_upper(~K, ~cmp, S.key(K, V, e), up), allbu(~K, ~V, ~cmp, up, t), h), {==}))
      L.subst(List<&2, M.Entry<K, V>>, z => {allbu(~K, ~V, ~cmp, up, z) == True{} : Bool}, SC.append(M.Entry<K, V>, SC.reverse(M.Entry<K, V>, t), Con{e, Nil{}}), SC.snoc(M.Entry<K, V>, SC.reverse(M.Entry<K, V>, t), e), Equal.sym(List<&2, M.Entry<K, V>>, SC.snoc(M.Entry<K, V>, SC.reverse(M.Entry<K, V>, t), e), SC.append(M.Entry<K, V>, SC.reverse(M.Entry<K, V>, t), Con{e, Nil{}}), LL.snoc_append(M.Entry<K, V>, SC.reverse(M.Entry<K, V>, t), e)), h1)

# below a key under the lower bound, nothing is within
def wnil_lt(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +lw: M.Bound<K>, +up: M.Bound<K>, +k: K, +xs: List<&2, M.Entry<K, V>>, +hk: {S.above_lower(~K, ~cmp, k, lw) == False{} : Bool}, +hl: {OR.ltall(~K, ~V, ~cmp, k, xs) == True{} : Bool}) -> {S.within(~K, ~V, ~cmp, lw, up, xs) == Nil{} : List<&2, M.Entry<K, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+e, +u}:
      +h1 = L.and_left(Cmp.is_lt(cmp(S.key(K, V, e), k)), OR.ltall(~K, ~V, ~cmp, k, u), hl)
      +h2 = L.and_right(Cmp.is_lt(cmp(S.key(K, V, e), k)), OR.ltall(~K, ~V, ~cmp, k, u), hl)
      Equal.trans(List<&2, M.Entry<K, V>>, S.within(~K, ~V, ~cmp, lw, up, Con{e, u}), S.within(~K, ~V, ~cmp, lw, up, u), Nil{}, w_out(~K, ~V, ~cmp, lw, up, e, u, ir_fa(~K, ~cmp, lw, up, S.key(K, V, e), al_false(~K, ~cmp, ~o, lw, k, S.key(K, V, e), hk, h1))), wnil_lt(~K, ~V, ~cmp, ~o, lw, up, k, u, hk, h2))

def bu_of(~K: Data, ~cmp: K -> K -> Cmp, +lw: M.Bound<K>, +up: M.Bound<K>, +k: K, +ha: {S.above_lower(~K, ~cmp, k, lw) == True{} : Bool}, +hir: {S.in_range(~K, ~cmp, k, lw, up) == False{} : Bool}) -> {S.below_upper(~K, ~cmp, k, up) == False{} : Bool}:
  L.subst(Bool, z => {Bool.and(z, S.below_upper(~K, ~cmp, k, up)) == False{} : Bool}, S.above_lower(~K, ~cmp, k, lw), True{}, ha, hir)

def al_oc(~K: Data, ~cmp: K -> K -> Cmp, +lw: M.Bound<K>, +up: M.Bound<K>, +k: K, +hb: {S.below_upper(~K, ~cmp, k, up) == True{} : Bool}, +hir: {S.in_range(~K, ~cmp, k, lw, up) == False{} : Bool}, +a: Bool, +ha: {S.above_lower(~K, ~cmp, k, lw) == a : Bool}) -> {S.above_lower(~K, ~cmp, k, lw) == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({S.above_lower(~K, ~cmp, k, lw) == False{} : Bool}, L.true_false(Equal.trans(Bool, True{}, S.below_upper(~K, ~cmp, k, up), False{}, Equal.sym(Bool, S.below_upper(~K, ~cmp, k, up), True{}, hb), bu_of(~K, ~cmp, lw, up, k, ha, hir))))
    case False{}:
      ha

def al_of(~K: Data, ~cmp: K -> K -> Cmp, +lw: M.Bound<K>, +up: M.Bound<K>, +k: K, +hb: {S.below_upper(~K, ~cmp, k, up) == True{} : Bool}, +hir: {S.in_range(~K, ~cmp, k, lw, up) == False{} : Bool}) -> {S.above_lower(~K, ~cmp, k, lw) == False{} : Bool}:
  al_oc(~K, ~cmp, lw, up, k, hb, hir, S.above_lower(~K, ~cmp, k, lw), {==})

# ---- a sorted list split at a bound ----


def spf_up2(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +lw: M.Bound<K>, +up: M.Bound<K>, +e: M.Entry<K, V>, +t: List<&2, M.Entry<K, V>>, +hf: {S.above_lower(~K, ~cmp, S.key(K, V, e), lw) == False{} : Bool}, +xa: List<&2, M.Entry<K, V>>, +xb: List<&2, M.Entry<K, V>>, +h1: {t == SC.append(M.Entry<K, V>, xa, xb) : List<&2, M.Entry<K, V>>}, r: {allal(~K, ~V, ~cmp, lw, xb) == True{} : Bool} & ({S.within(~K, ~V, ~cmp, lw, up, xa) == Nil{} : List<&2, M.Entry<K, V>>} & {fal(~K, ~V, ~cmp, lw, t) == S.head(M.Entry<K, V>, xb) : Maybe<&2, M.Entry<K, V>>})) -> Sigma<&1, &1, List<&2, M.Entry<K, V>>, xa => Sigma<&1, &1, List<&2, M.Entry<K, V>>, xb => {Con{e, t} == SC.append(M.Entry<K, V>, xa, xb) : List<&2, M.Entry<K, V>>} & ({allal(~K, ~V, ~cmp, lw, xb) == True{} : Bool} & ({S.within(~K, ~V, ~cmp, lw, up, xa) == Nil{} : List<&2, M.Entry<K, V>>} & {fal(~K, ~V, ~cmp, lw, Con{e, t}) == S.head(M.Entry<K, V>, xb) : Maybe<&2, M.Entry<K, V>>}))>>:
  match r:
    case Tuple{h2, Tuple{h3, h4}}:
      (Con{e, xa}, (xb, (cong(List<&2, M.Entry<K, V>>, List<&2, M.Entry<K, V>>, z => Con{e, z}, t, SC.append(M.Entry<K, V>, xa, xb), h1), (h2, (Equal.trans(List<&2, M.Entry<K, V>>, S.within(~K, ~V, ~cmp, lw, up, Con{e, xa}), S.within(~K, ~V, ~cmp, lw, up, xa), Nil{}, w_out(~K, ~V, ~cmp, lw, up, e, xa, ir_fa(~K, ~cmp, lw, up, S.key(K, V, e), hf)), h3), Equal.trans(Maybe<&2, M.Entry<K, V>>, fal(~K, ~V, ~cmp, lw, Con{e, t}), fal(~K, ~V, ~cmp, lw, t), S.head(M.Entry<K, V>, xb), pk_f(Maybe<&2, M.Entry<K, V>>, S.above_lower(~K, ~cmp, S.key(K, V, e), lw), Some{e}, fal(~K, ~V, ~cmp, lw, t), hf), h4))))))

def spf_up(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +lw: M.Bound<K>, +up: M.Bound<K>, +e: M.Entry<K, V>, +t: List<&2, M.Entry<K, V>>, +hf: {S.above_lower(~K, ~cmp, S.key(K, V, e), lw) == False{} : Bool}, r: Sigma<&1, &1, List<&2, M.Entry<K, V>>, xa => Sigma<&1, &1, List<&2, M.Entry<K, V>>, xb => {t == SC.append(M.Entry<K, V>, xa, xb) : List<&2, M.Entry<K, V>>} & ({allal(~K, ~V, ~cmp, lw, xb) == True{} : Bool} & ({S.within(~K, ~V, ~cmp, lw, up, xa) == Nil{} : List<&2, M.Entry<K, V>>} & {fal(~K, ~V, ~cmp, lw, t) == S.head(M.Entry<K, V>, xb) : Maybe<&2, M.Entry<K, V>>}))>>) -> Sigma<&1, &1, List<&2, M.Entry<K, V>>, xa => Sigma<&1, &1, List<&2, M.Entry<K, V>>, xb => {Con{e, t} == SC.append(M.Entry<K, V>, xa, xb) : List<&2, M.Entry<K, V>>} & ({allal(~K, ~V, ~cmp, lw, xb) == True{} : Bool} & ({S.within(~K, ~V, ~cmp, lw, up, xa) == Nil{} : List<&2, M.Entry<K, V>>} & {fal(~K, ~V, ~cmp, lw, Con{e, t}) == S.head(M.Entry<K, V>, xb) : Maybe<&2, M.Entry<K, V>>}))>>:
  match r:
    case Tuple{+xa, Tuple{+xb, Tuple{+h1, r2}}}:
      spf_up2(~K, ~V, ~cmp, ~o, lw, up, e, t, hf, xa, xb, h1, r2)

def spf_c(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +lw: M.Bound<K>, +up: M.Bound<K>, +e: M.Entry<K, V>, +t: List<&2, M.Entry<K, V>>, +h: {ST.ordered(~K, ~V, ~cmp, Con{e, t}) == True{} : Bool}, r: Sigma<&1, &1, List<&2, M.Entry<K, V>>, xa => Sigma<&1, &1, List<&2, M.Entry<K, V>>, xb => {t == SC.append(M.Entry<K, V>, xa, xb) : List<&2, M.Entry<K, V>>} & ({allal(~K, ~V, ~cmp, lw, xb) == True{} : Bool} & ({S.within(~K, ~V, ~cmp, lw, up, xa) == Nil{} : List<&2, M.Entry<K, V>>} & {fal(~K, ~V, ~cmp, lw, t) == S.head(M.Entry<K, V>, xb) : Maybe<&2, M.Entry<K, V>>}))>>, +a: Bool, +ha: {S.above_lower(~K, ~cmp, S.key(K, V, e), lw) == a : Bool}) -> Sigma<&1, &1, List<&2, M.Entry<K, V>>, xa => Sigma<&1, &1, List<&2, M.Entry<K, V>>, xb => {Con{e, t} == SC.append(M.Entry<K, V>, xa, xb) : List<&2, M.Entry<K, V>>} & ({allal(~K, ~V, ~cmp, lw, xb) == True{} : Bool} & ({S.within(~K, ~V, ~cmp, lw, up, xa) == Nil{} : List<&2, M.Entry<K, V>>} & {fal(~K, ~V, ~cmp, lw, Con{e, t}) == S.head(M.Entry<K, V>, xb) : Maybe<&2, M.Entry<K, V>>}))>>:
  match a:
    case True{}:
      (Nil{}, (Con{e, t}, ({==}, (al_all(~K, ~V, ~cmp, ~o, lw, t, e, h, ha), ({==}, pk_t(Maybe<&2, M.Entry<K, V>>, S.above_lower(~K, ~cmp, S.key(K, V, e), lw), Some{e}, fal(~K, ~V, ~cmp, lw, t), ha))))))
    case False{}:
      spf_up(~K, ~V, ~cmp, ~o, lw, up, e, t, ha, r)

# the entries below the lower bound, then those above it
def split_fal(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +lw: M.Bound<K>, +up: M.Bound<K>, +es: List<&2, M.Entry<K, V>>, +h: {ST.ordered(~K, ~V, ~cmp, es) == True{} : Bool}) -> Sigma<&1, &1, List<&2, M.Entry<K, V>>, xa => Sigma<&1, &1, List<&2, M.Entry<K, V>>, xb => {es == SC.append(M.Entry<K, V>, xa, xb) : List<&2, M.Entry<K, V>>} & ({allal(~K, ~V, ~cmp, lw, xb) == True{} : Bool} & ({S.within(~K, ~V, ~cmp, lw, up, xa) == Nil{} : List<&2, M.Entry<K, V>>} & {fal(~K, ~V, ~cmp, lw, es) == S.head(M.Entry<K, V>, xb) : Maybe<&2, M.Entry<K, V>>}))>>:
  match es:
    case Nil{}:
      (Nil{}, (Nil{}, ({==}, ({==}, ({==}, {==})))))
    case Con{+e, +t}:
      spf_c(~K, ~V, ~cmp, ~o, lw, up, e, t, h, split_fal(~K, ~V, ~cmp, ~o, lw, up, t, OR.ord_tail(~K, ~V, ~cmp, e, t, h)), S.above_lower(~K, ~cmp, S.key(K, V, e), lw), {==})


def spb_up2(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +lw: M.Bound<K>, +up: M.Bound<K>, +e: M.Entry<K, V>, +t: List<&2, M.Entry<K, V>>, +bst: Maybe<&2, M.Entry<K, V>>, +hb: {S.below_upper(~K, ~cmp, S.key(K, V, e), up) == True{} : Bool}, +xa: List<&2, M.Entry<K, V>>, +xb: List<&2, M.Entry<K, V>>, +h1: {t == SC.append(M.Entry<K, V>, xa, xb) : List<&2, M.Entry<K, V>>}, r: {allbu(~K, ~V, ~cmp, up, xa) == True{} : Bool} & ({S.within(~K, ~V, ~cmp, lw, up, xb) == Nil{} : List<&2, M.Entry<K, V>>} & {lbu(~K, ~V, ~cmp, up, t, Some{e}) == OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, xa), Some{e}) : Maybe<&2, M.Entry<K, V>>})) -> Sigma<&1, &1, List<&2, M.Entry<K, V>>, xa => Sigma<&1, &1, List<&2, M.Entry<K, V>>, xb => {Con{e, t} == SC.append(M.Entry<K, V>, xa, xb) : List<&2, M.Entry<K, V>>} & ({allbu(~K, ~V, ~cmp, up, xa) == True{} : Bool} & ({S.within(~K, ~V, ~cmp, lw, up, xb) == Nil{} : List<&2, M.Entry<K, V>>} & {lbu(~K, ~V, ~cmp, up, Con{e, t}, bst) == OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, xa), bst) : Maybe<&2, M.Entry<K, V>>}))>>:
  match r:
    case Tuple{h2, Tuple{h3, h4}}:
      +e1 = cong(Maybe<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => lbu(~K, ~V, ~cmp, up, t, z), S.pick(Maybe<&2, M.Entry<K, V>>, S.below_upper(~K, ~cmp, S.key(K, V, e), up), Some{e}, bst), Some{e}, pk_t(Maybe<&2, M.Entry<K, V>>, S.below_upper(~K, ~cmp, S.key(K, V, e), up), Some{e}, bst, hb))
      (Con{e, xa}, (xb, (cong(List<&2, M.Entry<K, V>>, List<&2, M.Entry<K, V>>, z => Con{e, z}, t, SC.append(M.Entry<K, V>, xa, xb), h1), (L.and_intro(S.below_upper(~K, ~cmp, S.key(K, V, e), up), allbu(~K, ~V, ~cmp, up, xa), hb, h2), (h3, Equal.trans(Maybe<&2, M.Entry<K, V>>, lbu(~K, ~V, ~cmp, up, Con{e, t}, bst), OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, xa), Some{e}), OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, Con{e, xa}), bst), Equal.trans(Maybe<&2, M.Entry<K, V>>, lbu(~K, ~V, ~cmp, up, Con{e, t}, bst), lbu(~K, ~V, ~cmp, up, t, Some{e}), OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, xa), Some{e}), e1, h4), NV.lw_all_c(K, V, e, xa, bst)))))))

def spb_up(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +lw: M.Bound<K>, +up: M.Bound<K>, +e: M.Entry<K, V>, +t: List<&2, M.Entry<K, V>>, +bst: Maybe<&2, M.Entry<K, V>>, +hb: {S.below_upper(~K, ~cmp, S.key(K, V, e), up) == True{} : Bool}, r: Sigma<&1, &1, List<&2, M.Entry<K, V>>, xa => Sigma<&1, &1, List<&2, M.Entry<K, V>>, xb => {t == SC.append(M.Entry<K, V>, xa, xb) : List<&2, M.Entry<K, V>>} & ({allbu(~K, ~V, ~cmp, up, xa) == True{} : Bool} & ({S.within(~K, ~V, ~cmp, lw, up, xb) == Nil{} : List<&2, M.Entry<K, V>>} & {lbu(~K, ~V, ~cmp, up, t, Some{e}) == OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, xa), Some{e}) : Maybe<&2, M.Entry<K, V>>}))>>) -> Sigma<&1, &1, List<&2, M.Entry<K, V>>, xa => Sigma<&1, &1, List<&2, M.Entry<K, V>>, xb => {Con{e, t} == SC.append(M.Entry<K, V>, xa, xb) : List<&2, M.Entry<K, V>>} & ({allbu(~K, ~V, ~cmp, up, xa) == True{} : Bool} & ({S.within(~K, ~V, ~cmp, lw, up, xb) == Nil{} : List<&2, M.Entry<K, V>>} & {lbu(~K, ~V, ~cmp, up, Con{e, t}, bst) == OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, xa), bst) : Maybe<&2, M.Entry<K, V>>}))>>:
  match r:
    case Tuple{+xa, Tuple{+xb, Tuple{+h1, r2}}}:
      spb_up2(~K, ~V, ~cmp, ~o, lw, up, e, t, bst, hb, xa, xb, h1, r2)

def spb_c(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +lw: M.Bound<K>, +up: M.Bound<K>, +e: M.Entry<K, V>, +t: List<&2, M.Entry<K, V>>, +bst: Maybe<&2, M.Entry<K, V>>, +h: {ST.ordered(~K, ~V, ~cmp, Con{e, t}) == True{} : Bool}, r: Sigma<&1, &1, List<&2, M.Entry<K, V>>, xa => Sigma<&1, &1, List<&2, M.Entry<K, V>>, xb => {t == SC.append(M.Entry<K, V>, xa, xb) : List<&2, M.Entry<K, V>>} & ({allbu(~K, ~V, ~cmp, up, xa) == True{} : Bool} & ({S.within(~K, ~V, ~cmp, lw, up, xb) == Nil{} : List<&2, M.Entry<K, V>>} & {lbu(~K, ~V, ~cmp, up, t, Some{e}) == OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, xa), Some{e}) : Maybe<&2, M.Entry<K, V>>}))>>, +b: Bool, +hb: {S.below_upper(~K, ~cmp, S.key(K, V, e), up) == b : Bool}) -> Sigma<&1, &1, List<&2, M.Entry<K, V>>, xa => Sigma<&1, &1, List<&2, M.Entry<K, V>>, xb => {Con{e, t} == SC.append(M.Entry<K, V>, xa, xb) : List<&2, M.Entry<K, V>>} & ({allbu(~K, ~V, ~cmp, up, xa) == True{} : Bool} & ({S.within(~K, ~V, ~cmp, lw, up, xb) == Nil{} : List<&2, M.Entry<K, V>>} & {lbu(~K, ~V, ~cmp, up, Con{e, t}, bst) == OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, xa), bst) : Maybe<&2, M.Entry<K, V>>}))>>:
  match b:
    case True{}:
      spb_up(~K, ~V, ~cmp, ~o, lw, up, e, t, bst, hb, r)
    case False{}:
      +hgt = OR.ord_gt(~K, ~V, ~cmp, ~o, t, e, h)
      +hw = Equal.trans(List<&2, M.Entry<K, V>>, S.within(~K, ~V, ~cmp, lw, up, Con{e, t}), S.within(~K, ~V, ~cmp, lw, up, t), Nil{}, w_out(~K, ~V, ~cmp, lw, up, e, t, ir_fb(~K, ~cmp, lw, up, S.key(K, V, e), hb)), wnil(~K, ~V, ~cmp, ~o, lw, up, S.key(K, V, e), t, hb, hgt))
      +hl = Equal.trans(Maybe<&2, M.Entry<K, V>>, lbu(~K, ~V, ~cmp, up, Con{e, t}, bst), lbu(~K, ~V, ~cmp, up, t, bst), bst, cong(Maybe<&2, M.Entry<K, V>>, Maybe<&2, M.Entry<K, V>>, z => lbu(~K, ~V, ~cmp, up, t, z), S.pick(Maybe<&2, M.Entry<K, V>>, S.below_upper(~K, ~cmp, S.key(K, V, e), up), Some{e}, bst), bst, pk_f(Maybe<&2, M.Entry<K, V>>, S.below_upper(~K, ~cmp, S.key(K, V, e), up), Some{e}, bst, hb)), lbu_none(~K, ~V, ~cmp, ~o, up, S.key(K, V, e), t, bst, hb, hgt))
      (Nil{}, (Con{e, t}, ({==}, ({==}, (hw, hl)))))

# the entries below the upper bound, then those above it
def split_lbu(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +lw: M.Bound<K>, +up: M.Bound<K>, +es: List<&2, M.Entry<K, V>>, +bst: Maybe<&2, M.Entry<K, V>>, +h: {ST.ordered(~K, ~V, ~cmp, es) == True{} : Bool}) -> Sigma<&1, &1, List<&2, M.Entry<K, V>>, xa => Sigma<&1, &1, List<&2, M.Entry<K, V>>, xb => {es == SC.append(M.Entry<K, V>, xa, xb) : List<&2, M.Entry<K, V>>} & ({allbu(~K, ~V, ~cmp, up, xa) == True{} : Bool} & ({S.within(~K, ~V, ~cmp, lw, up, xb) == Nil{} : List<&2, M.Entry<K, V>>} & {lbu(~K, ~V, ~cmp, up, es, bst) == OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, xa), bst) : Maybe<&2, M.Entry<K, V>>}))>>:
  match es:
    case Nil{}:
      (Nil{}, (Nil{}, ({==}, ({==}, ({==}, {==})))))
    case Con{+e, +t}:
      spb_c(~K, ~V, ~cmp, ~o, lw, up, e, t, bst, h, split_lbu(~K, ~V, ~cmp, ~o, lw, up, t, Some{e}, OR.ord_tail(~K, ~V, ~cmp, e, t, h)), S.below_upper(~K, ~cmp, S.key(K, V, e), up), {==})

def start_fal(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +lw: M.Bound<K>, +es: List<&2, M.Entry<K, V>>) -> {S.start(~K, ~V, ~cmp, lw, True{}, es) == S.key_m(K, V, fal(~K, ~V, ~cmp, lw, es)) : Maybe<&2, K>}:
  match lw:
    case M.Unbounded{}:
      cong(Maybe<&2, M.Entry<K, V>>, Maybe<&2, K>, z => S.key_m(K, V, z), S.head(M.Entry<K, V>, es), fal(~K, ~V, ~cmp, M.Unbounded{}, es), Equal.sym(Maybe<&2, M.Entry<K, V>>, fal(~K, ~V, ~cmp, M.Unbounded{}, es), S.head(M.Entry<K, V>, es), fal_u(~K, ~V, ~cmp, es)))
    case M.Inclusive{+x}:
      cong(Maybe<&2, M.Entry<K, V>>, Maybe<&2, K>, z => S.key_m(K, V, z), S.first_where(~K, ~V, ~cmp, x, True{}, es), fal(~K, ~V, ~cmp, M.Inclusive{x}, es), Equal.sym(Maybe<&2, M.Entry<K, V>>, fal(~K, ~V, ~cmp, M.Inclusive{x}, es), S.first_where(~K, ~V, ~cmp, x, True{}, es), fal_i(~K, ~V, ~cmp, x, es)))
    case M.Exclusive{+x}:
      cong(Maybe<&2, M.Entry<K, V>>, Maybe<&2, K>, z => S.key_m(K, V, z), S.first_where(~K, ~V, ~cmp, x, False{}, es), fal(~K, ~V, ~cmp, M.Exclusive{x}, es), Equal.sym(Maybe<&2, M.Entry<K, V>>, fal(~K, ~V, ~cmp, M.Exclusive{x}, es), S.first_where(~K, ~V, ~cmp, x, False{}, es), fal_x(~K, ~V, ~cmp, x, es)))

def start_lbu(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +up: M.Bound<K>, +es: List<&2, M.Entry<K, V>>) -> {S.start(~K, ~V, ~cmp, up, False{}, es) == S.key_m(K, V, lbu(~K, ~V, ~cmp, up, es, None{})) : Maybe<&2, K>}:
  match up:
    case M.Unbounded{}:
      cong(Maybe<&2, M.Entry<K, V>>, Maybe<&2, K>, z => S.key_m(K, V, z), S.last(M.Entry<K, V>, es), lbu(~K, ~V, ~cmp, M.Unbounded{}, es, None{}), Equal.sym(Maybe<&2, M.Entry<K, V>>, lbu(~K, ~V, ~cmp, M.Unbounded{}, es, None{}), S.last(M.Entry<K, V>, es), Equal.trans(Maybe<&2, M.Entry<K, V>>, lbu(~K, ~V, ~cmp, M.Unbounded{}, es, None{}), OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, es), None{}), S.last(M.Entry<K, V>, es), lbu_u(~K, ~V, ~cmp, es, None{}), OR.orm_none(M.Entry<K, V>, S.last(M.Entry<K, V>, es)))))
    case M.Inclusive{+y}:
      cong(Maybe<&2, M.Entry<K, V>>, Maybe<&2, K>, z => S.key_m(K, V, z), S.last_where(~K, ~V, ~cmp, y, True{}, es, None{}), lbu(~K, ~V, ~cmp, M.Inclusive{y}, es, None{}), Equal.sym(Maybe<&2, M.Entry<K, V>>, lbu(~K, ~V, ~cmp, M.Inclusive{y}, es, None{}), S.last_where(~K, ~V, ~cmp, y, True{}, es, None{}), lbu_i(~K, ~V, ~cmp, y, es, None{})))
    case M.Exclusive{+y}:
      cong(Maybe<&2, M.Entry<K, V>>, Maybe<&2, K>, z => S.key_m(K, V, z), S.last_where(~K, ~V, ~cmp, y, False{}, es, None{}), lbu(~K, ~V, ~cmp, M.Exclusive{y}, es, None{}), Equal.sym(Maybe<&2, M.Entry<K, V>>, lbu(~K, ~V, ~cmp, M.Exclusive{y}, es, None{}), S.last_where(~K, ~V, ~cmp, y, False{}, es, None{}), lbu_x(~K, ~V, ~cmp, y, es, None{})))
