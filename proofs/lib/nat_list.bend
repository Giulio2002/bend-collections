import Base
import ../spec/common.bend as SC
import ./logic.bend as L
import ./nat.bend as N
import ./list.bend as LL

# Lists of Nat (ids, slots): membership, duplicate-freedom and how both
# split over appends; the last of a list; splitting a list at a member; the
# reversed append. Shared by every structure that threads ids through arrays.

def memn(+s: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+x, t}:
      Bool.or(Nat.is_eq(x, s), memn(s, t))

def nodupn(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +t}:
      Bool.and(Bool.not(memn(x, t)), nodupn(t))

def or_assoc(+a: Bool, +b: Bool, +c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def or_comm(+a: Bool, +b: Bool) -> {Bool.or(a, b) == Bool.or(b, a) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def and_assoc(+a: Bool, +b: Bool, +c: Bool) -> {Bool.and(a, Bool.and(b, c)) == Bool.and(Bool.and(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def and_comm(+a: Bool, +b: Bool) -> {Bool.and(a, b) == Bool.and(b, a) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def bt_mid(+x: Bool, +y: Bool, +z: Bool, +w: Bool) -> {Bool.and(Bool.not(Bool.or(x, y)), Bool.and(z, Bool.not(w))) == Bool.and(Bool.and(Bool.not(x), z), Bool.not(Bool.or(y, w))) : Bool}:
  match x y z w:
    case True{} y2 z2 w2:
      {==}
    case False{} True{} z2 w2:
      +e = and_comm(z2, False{})
      Equal.trans(Bool, Bool.and(False{}, Bool.and(z2, Bool.not(w2))), False{}, Bool.and(z2, False{}), {==}, Equal.sym(Bool, Bool.and(z2, False{}), False{}, Equal.trans(Bool, Bool.and(z2, False{}), Bool.and(False{}, z2), False{}, e, {==})))
    case False{} False{} True{} w2:
      {==}
    case False{} False{} False{} w2:
      {==}

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

def memn_app(+x: Nat, +a: List<&2, Nat>, +b: List<&2, Nat>) -> {memn(x, SC.append(Nat, a, b)) == Bool.or(memn(x, a), memn(x, b)) : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.trans(Bool, Bool.or(Nat.is_eq(h, x), memn(x, SC.append(Nat, t, b))), Bool.or(Nat.is_eq(h, x), Bool.or(memn(x, t), memn(x, b))), Bool.or(Bool.or(Nat.is_eq(h, x), memn(x, t)), memn(x, b)), Equal.cong(Bool, Bool, z => Bool.or(Nat.is_eq(h, x), z), memn(x, SC.append(Nat, t, b)), Bool.or(memn(x, t), memn(x, b)), memn_app(x, t, b)), or_assoc(Nat.is_eq(h, x), memn(x, t), memn(x, b)))

def memn_mid(+x: Nat, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>) -> {memn(x, SC.append(Nat, a, Con{s, b})) == Bool.or(memn(x, SC.append(Nat, a, b)), Nat.is_eq(s, x)) : Bool}:
  match a:
    case Nil{}:
      or_comm(Nat.is_eq(s, x), memn(x, b))
    case Con{+h, +t}:
      Equal.trans(Bool, Bool.or(Nat.is_eq(h, x), memn(x, SC.append(Nat, t, Con{s, b}))), Bool.or(Nat.is_eq(h, x), Bool.or(memn(x, SC.append(Nat, t, b)), Nat.is_eq(s, x))), Bool.or(Bool.or(Nat.is_eq(h, x), memn(x, SC.append(Nat, t, b))), Nat.is_eq(s, x)), Equal.cong(Bool, Bool, z => Bool.or(Nat.is_eq(h, x), z), memn(x, SC.append(Nat, t, Con{s, b})), Bool.or(memn(x, SC.append(Nat, t, b)), Nat.is_eq(s, x)), memn_mid(x, t, s, b)), or_assoc(Nat.is_eq(h, x), memn(x, SC.append(Nat, t, b)), Nat.is_eq(s, x)))

def nd_mid(+a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>) -> {nodupn(SC.append(Nat, a, Con{s, b})) == Bool.and(nodupn(SC.append(Nat, a, b)), Bool.not(memn(s, SC.append(Nat, a, b)))) : Bool}:
  match a:
    case Nil{}:
      and_comm(Bool.not(memn(s, b)), nodupn(b))
    case Con{+h, +t}:
      +X = memn(h, SC.append(Nat, t, b))
      +Z = nodupn(SC.append(Nat, t, b))
      +Wm = memn(s, SC.append(Nat, t, b))
      +e1 = Equal.cong(Bool, Bool, z => Bool.and(Bool.not(z), nodupn(SC.append(Nat, t, Con{s, b}))), memn(h, SC.append(Nat, t, Con{s, b})), Bool.or(X, Nat.is_eq(s, h)), memn_mid(h, t, s, b))
      +e2 = Equal.cong(Bool, Bool, z => Bool.and(Bool.not(Bool.or(X, Nat.is_eq(s, h))), z), nodupn(SC.append(Nat, t, Con{s, b})), Bool.and(Z, Bool.not(Wm)), nd_mid(t, s, b))
      +e3 = bt_mid(X, Nat.is_eq(s, h), Z, Wm)
      +e4 = Equal.cong(Bool, Bool, z => Bool.and(Bool.and(Bool.not(X), Z), Bool.not(Bool.or(z, Wm))), Nat.is_eq(s, h), Nat.is_eq(h, s), is_eq_sym(s, h))
      Equal.trans(Bool, nodupn(SC.append(Nat, Con{h, t}, Con{s, b})), Bool.and(Bool.not(Bool.or(X, Nat.is_eq(s, h))), nodupn(SC.append(Nat, t, Con{s, b}))), Bool.and(Bool.and(Bool.not(X), Z), Bool.not(Bool.or(Nat.is_eq(h, s), Wm))), e1, Equal.trans(Bool, Bool.and(Bool.not(Bool.or(X, Nat.is_eq(s, h))), nodupn(SC.append(Nat, t, Con{s, b}))), Bool.and(Bool.not(Bool.or(X, Nat.is_eq(s, h))), Bool.and(Z, Bool.not(Wm))), Bool.and(Bool.and(Bool.not(X), Z), Bool.not(Bool.or(Nat.is_eq(h, s), Wm))), e2, Equal.trans(Bool, Bool.and(Bool.not(Bool.or(X, Nat.is_eq(s, h))), Bool.and(Z, Bool.not(Wm))), Bool.and(Bool.and(Bool.not(X), Z), Bool.not(Bool.or(Nat.is_eq(s, h), Wm))), Bool.and(Bool.and(Bool.not(X), Z), Bool.not(Bool.or(Nat.is_eq(h, s), Wm))), e3, e4)))

def not_t_f(+b: Bool, +h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  L.not_true(b, h)

def or_f_l(+a: Bool, +b: Bool, +h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, L.true_false(h))
    case False{}:
      {==}

def nd_r(+a: List<&2, Nat>, +x: List<&2, Nat>, +h: {nodupn(SC.append(Nat, a, x)) == True{} : Bool}) -> {nodupn(x) == True{} : Bool}:
  match a:
    case Nil{}:
      h
    case Con{+h0, +t}:
      nd_r(t, x, L.and_right(Bool.not(memn(h0, SC.append(Nat, t, x))), nodupn(SC.append(Nat, t, x)), h))

def nd_l(+a: List<&2, Nat>, +x: List<&2, Nat>, +h: {nodupn(SC.append(Nat, a, x)) == True{} : Bool}) -> {nodupn(a) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+h0, +t}:
      +hm = not_t_f(memn(h0, SC.append(Nat, t, x)), L.and_left(Bool.not(memn(h0, SC.append(Nat, t, x))), nodupn(SC.append(Nat, t, x)), h))
      +hm2 = or_f_l(memn(h0, t), memn(h0, x), L.subst(Bool, z => {z == False{} : Bool}, memn(h0, SC.append(Nat, t, x)), Bool.or(memn(h0, t), memn(h0, x)), memn_app(h0, t, x), hm))
      L.and_intro(Bool.not(memn(h0, t)), nodupn(t), L.subst(Bool, z => {Bool.not(z) == True{} : Bool}, False{}, memn(h0, t), Equal.sym(Bool, memn(h0, t), False{}, hm2), {==}), nd_l(t, x, L.and_right(Bool.not(memn(h0, SC.append(Nat, t, x))), nodupn(SC.append(Nat, t, x)), h)))

def or_true_b(+b: Bool) -> {Bool.or(b, True{}) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def mem_app_r(+y: Nat, +a: List<&2, Nat>, +x: List<&2, Nat>, +h: {memn(y, x) == True{} : Bool}) -> {memn(y, SC.append(Nat, a, x)) == True{} : Bool}:
  L.subst(Bool, z => {z == True{} : Bool}, Bool.or(memn(y, a), memn(y, x)), memn(y, SC.append(Nat, a, x)), Equal.sym(Bool, memn(y, SC.append(Nat, a, x)), Bool.or(memn(y, a), memn(y, x)), memn_app(y, a, x)), L.subst(Bool, z => {Bool.or(memn(y, a), z) == True{} : Bool}, True{}, memn(y, x), Equal.sym(Bool, memn(y, x), True{}, h), or_true_b(memn(y, a))))

def mem_app_l(+y: Nat, +a: List<&2, Nat>, +x: List<&2, Nat>, +h: {memn(y, a) == True{} : Bool}) -> {memn(y, SC.append(Nat, a, x)) == True{} : Bool}:
  L.subst(Bool, z => {z == True{} : Bool}, Bool.or(memn(y, a), memn(y, x)), memn(y, SC.append(Nat, a, x)), Equal.sym(Bool, memn(y, SC.append(Nat, a, x)), Bool.or(memn(y, a), memn(y, x)), memn_app(y, a, x)), L.subst(Bool, z => {Bool.or(z, memn(y, x)) == True{} : Bool}, True{}, memn(y, a), Equal.sym(Bool, memn(y, a), True{}, h), {==}))

def dj_c(+y: Nat, +h0: Nat, +t: List<&2, Nat>, +x: List<&2, Nat>, +hy: {memn(y, x) == True{} : Bool}, +hn: {Bool.not(memn(h0, SC.append(Nat, t, x))) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(h0, y) == c : Bool}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      +e = N.eq_from_is_eq(h0, y, hc)
      +hm = mem_app_r(y, t, x, hy)
      Empty.absurd({True{} == False{} : Bool}, L.false_true(L.subst(Bool, z => {Bool.not(z) == True{} : Bool}, memn(h0, SC.append(Nat, t, x)), True{}, L.subst(Nat, w => {memn(w, SC.append(Nat, t, x)) == True{} : Bool}, y, h0, Equal.sym(Nat, h0, y, e), hm), hn)))
    case False{}:
      {==}

def nd_dj(+a: List<&2, Nat>, +x: List<&2, Nat>, +h: {nodupn(SC.append(Nat, a, x)) == True{} : Bool}, +y: Nat, +hy: {memn(y, x) == True{} : Bool}) -> {memn(y, a) == False{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+h0, +t}:
      +hn = L.and_left(Bool.not(memn(h0, SC.append(Nat, t, x))), nodupn(SC.append(Nat, t, x)), h)
      +e1 = dj_c(y, h0, t, x, hy, hn, Nat.is_eq(h0, y), {==})
      +e2 = nd_dj(t, x, L.and_right(Bool.not(memn(h0, SC.append(Nat, t, x))), nodupn(SC.append(Nat, t, x)), h), y, hy)
      L.subst(Bool, z => {Bool.or(z, memn(y, t)) == False{} : Bool}, False{}, Nat.is_eq(h0, y), Equal.sym(Bool, Nat.is_eq(h0, y), False{}, e1), e2)

def dj2_c(+a: List<&2, Nat>, +x: List<&2, Nat>, +h: {nodupn(SC.append(Nat, a, x)) == True{} : Bool}, +y: Nat, +hy: {memn(y, a) == True{} : Bool}, +c: Bool, +hc: {memn(y, x) == c : Bool}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, L.true_false(Equal.trans(Bool, True{}, memn(y, a), False{}, Equal.sym(Bool, memn(y, a), True{}, hy), nd_dj(a, x, h, y, hc))))
    case False{}:
      {==}

def nd_dj2(+a: List<&2, Nat>, +x: List<&2, Nat>, +h: {nodupn(SC.append(Nat, a, x)) == True{} : Bool}, +y: Nat, +hy: {memn(y, a) == True{} : Bool}) -> {memn(y, x) == False{} : Bool}:
  dj2_c(a, x, h, y, hy, memn(y, x), {==})

def or_ff_l(+a: Bool, +b: Bool, +h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, L.true_false(h))
    case False{}:
      {==}

def or_ff_r(+a: Bool, +b: Bool, +h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({b == False{} : Bool}, L.true_false(h))
    case False{}:
      h

def not_f(+a: Bool, +h: {a == False{} : Bool}) -> {Bool.not(a) == True{} : Bool}:
  L.subst(Bool, z => {Bool.not(z) == True{} : Bool}, False{}, a, Equal.sym(Bool, a, False{}, h), {==})

def or_tl(+a: Bool, +b: Bool, +h: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  L.subst(Bool, z => {Bool.or(z, b) == True{} : Bool}, True{}, a, Equal.sym(Bool, a, True{}, h), {==})

def or_tr(+a: Bool, +b: Bool, +h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  Equal.trans(Bool, Bool.or(a, b), Bool.or(b, a), True{}, or_comm(a, b), or_tl(b, a, h))

def and3(+a: Bool, +b: Bool, +c: Bool, +d: Bool) -> {Bool.and(a, Bool.and(b, Bool.and(c, d))) == Bool.and(Bool.and(a, Bool.and(b, c)), d) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} b2:
      {==}

def ne_sym(+x: Nat, +y: Nat, +h: {Nat.is_eq(x, y) == False{} : Bool}) -> {Nat.is_eq(y, x) == False{} : Bool}:
  Equal.trans(Bool, Nat.is_eq(y, x), Nat.is_eq(x, y), False{}, is_eq_sym(y, x), h)

def lastn(t: List<&2, Nat>, +a: Nat) -> Nat:
  match t:
    case Nil{}:
      a
    case Con{+b, +t2}:
      lastn(t2, b)

def lastn_mem(+t: List<&2, Nat>, +a: Nat) -> {memn(lastn(t, a), Con{a, t}) == True{} : Bool}:
  match t:
    case Nil{}:
      or_tl(Nat.is_eq(a, a), False{}, N.is_eq_refl(a))
    case Con{+b, +t2}:
      or_tr(Nat.is_eq(a, lastn(t2, b)), memn(lastn(t2, b), Con{b, t2}), lastn_mem(t2, b))

def ne_mem_c(+a: Nat, +z: Nat, +xs: List<&2, Nat>, +h1: {Bool.not(memn(a, xs)) == True{} : Bool}, +h2: {memn(z, xs) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(z, a) == c : Bool}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      +e = N.eq_from_is_eq(z, a, hc)
      Empty.absurd({True{} == False{} : Bool}, L.false_true(L.subst(Bool, b => {Bool.not(b) == True{} : Bool}, memn(a, xs), True{}, L.subst(Nat, w => {memn(w, xs) == True{} : Bool}, z, a, e, h2), h1)))
    case False{}:
      {==}

def ne_mem(+a: Nat, +z: Nat, +xs: List<&2, Nat>, +h1: {Bool.not(memn(a, xs)) == True{} : Bool}, +h2: {memn(z, xs) == True{} : Bool}) -> {Nat.is_eq(z, a) == False{} : Bool}:
  ne_mem_c(a, z, xs, h1, h2, Nat.is_eq(z, a), {==})

def rapp(l: List<&2, Nat>, b: List<&2, Nat>) -> List<&2, Nat>:
  match l:
    case Nil{}:
      b
    case Con{+x, r}:
      rapp(r, Con{x, b})

def len_rapp(+l: List<&2, Nat>, +b: List<&2, Nat>) -> {SC.length(Nat, rapp(l, b)) == Nat.add(SC.length(Nat, l), SC.length(Nat, b)) : Nat}:
  match l:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      Equal.trans(Nat, SC.length(Nat, rapp(r, Con{x, b})), Nat.add(SC.length(Nat, r), 1n+SC.length(Nat, b)), 1n+Nat.add(SC.length(Nat, r), SC.length(Nat, b)), len_rapp(r, Con{x, b}), N.add_succ(SC.length(Nat, r), SC.length(Nat, b)))

def Split(+s: Nat, +sl: List<&2, Nat>) -> Type:
  Sigma<&1, &1, List<&2, Nat>, a => Sigma<&1, &1, List<&2, Nat>, b => {sl == SC.append(Nat, a, Con{s, b}) : List<&2, Nat>}>>

def sp_up(+x: Nat, +s: Nat, +t: List<&2, Nat>, r: Split(s, t)) -> Split(s, Con{x, t}):
  match r:
    case Tuple{+a, Tuple{+b, e}}:
      (Con{x, a}, (b, LL.cons_cong(Nat, x, t, SC.append(Nat, a, Con{s, b}), e)))

def sp_c(+x: Nat, +s: Nat, +t: List<&2, Nat>, +c: Bool, +hc: {Nat.is_eq(x, s) == c : Bool}, +hm: {Bool.or(c, memn(s, t)) == True{} : Bool}, rec: @h: {memn(s, t) == True{} : Bool} -> Split(s, t)) -> Split(s, Con{x, t}):
  match c:
    case True{}:
      (Nil{}, (t, Equal.cong(Nat, List<&2, Nat>, z => Con{z, t}, x, s, N.eq_from_is_eq(x, s, hc))))
    case False{}:
      sp_up(x, s, t, rec(hm))

def split_mem(+s: Nat, +sl: List<&2, Nat>, +hm: {memn(s, sl) == True{} : Bool}) -> Split(s, sl):
  match sl:
    case Nil{}:
      Empty.absurd(Split(s, Nil{}), L.false_true(hm))
    case Con{+x, +t}:
      sp_c(x, s, t, Nat.is_eq(x, s), {==}, hm, h => split_mem(s, t, h))
