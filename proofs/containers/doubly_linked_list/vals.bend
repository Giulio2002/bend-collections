import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/u32alg.bend as A
import ../../lib/list.bend as LL
import ../../lib/spec_common.bend as SC
import ./spec.bend as S
import ./state.bend as ST
import ./rel.bend as RL
import ../../lib/nat_list.bend as NL
import ../../lib/words32.bend as W32

# The value and generation lists: reads after writes, prefixes, and the
# invariant's live-listed and zero-generation components pointwise.


# ---- values ----

def val_upd_same(-T: Data, +vl: List<&2, Maybe<&2, T>>, +i: Nat, +v: Maybe<&2, T>, +h: {Nat.is_lt(i, SC.length(Maybe<&2, T>, vl)) == True{} : Bool}) -> {S.val_of(T, SC.update(Maybe<&2, T>, vl, i, v), i) == v : Maybe<&2, T>}:
  match vl i:
    case Nil{} _:
      Empty.absurd({S.val_of(T, Nil{}, i) == v : Maybe<&2, T>}, N.lt_zero_absurd(i, h))
    case Con{m, t} 0n:
      {==}
    case Con{m, +t} 1n+p:
      val_upd_same(T, t, p, v, h)

def val_upd_other(-T: Data, +vl: List<&2, Maybe<&2, T>>, +i: Nat, +j: Nat, +v: Maybe<&2, T>, +ne: {Nat.is_eq(i, j) == False{} : Bool}) -> {S.val_of(T, SC.update(Maybe<&2, T>, vl, i, v), j) == S.val_of(T, vl, j) : Maybe<&2, T>}:
  match vl i j:
    case Nil{} _ _:
      {==}
    case Con{m, t} 0n 0n:
      Empty.absurd({v == m : Maybe<&2, T>}, L.true_false(ne))
    case Con{m, t} 0n 1n+q:
      {==}
    case Con{m, t} 1n+p 0n:
      {==}
    case Con{m, +t} 1n+p 1n+q:
      val_upd_other(T, t, p, q, v, ne)

def val_take(-T: Data, +vl: List<&2, Maybe<&2, T>>, +n: Nat, +i: Nat, +h: {Nat.is_lt(i, n) == True{} : Bool}) -> {S.val_of(T, SC.take(Maybe<&2, T>, vl, n), i) == S.val_of(T, vl, i) : Maybe<&2, T>}:
  match vl n i:
    case Nil{} _ _:
      {==}
    case Con{m, t} 0n _:
      Empty.absurd({S.val_of(T, Nil{}, i) == S.val_of(T, Con{m, t}, i) : Maybe<&2, T>}, N.lt_zero_absurd(i, h))
    case Con{m, t} 1n+p 0n:
      {==}
    case Con{m, +t} 1n+p 1n+q:
      val_take(T, t, p, q, h)

def val_hi(-T: Data, +vl: List<&2, Maybe<&2, T>>, +i: Nat, +h: {Nat.is_le(SC.length(Maybe<&2, T>, vl), i) == True{} : Bool}) -> {S.val_of(T, vl, i) == None{} : Maybe<&2, T>}:
  match vl i:
    case Nil{} _:
      {==}
    case Con{m, t} 0n:
      Empty.absurd({m == None{} : Maybe<&2, T>}, L.false_true(h))
    case Con{m, +t} 1n+p:
      val_hi(T, t, p, h)

# ---- generations ----

def gen_nth0(+gl: List<&2, U32>, +i: Nat) -> {S.gen_of(gl, i) == W32.nth0(gl, i) : U32}:
  match gl i:
    case Nil{} _:
      {==}
    case Con{g, t} 0n:
      {==}
    case Con{g, +t} 1n+p:
      gen_nth0(t, p)

def nth0_take(+gl: List<&2, U32>, +n: Nat, +i: Nat, +h: {Nat.is_lt(i, n) == True{} : Bool}) -> {W32.nth0(SC.take(U32, gl, n), i) == W32.nth0(gl, i) : U32}:
  match gl n i:
    case Nil{} _ _:
      {==}
    case Con{g, t} 0n _:
      Empty.absurd({W32.nth0(Nil{}, i) == W32.nth0(Con{g, t}, i) : U32}, N.lt_zero_absurd(i, h))
    case Con{g, t} 1n+p 0n:
      {==}
    case Con{g, +t} 1n+p 1n+q:
      nth0_take(t, p, q, h)

def gen_take(+gl: List<&2, U32>, +n: Nat, +i: Nat, +h: {Nat.is_lt(i, n) == True{} : Bool}) -> {S.gen_of(SC.take(U32, gl, n), i) == W32.nth0(gl, i) : U32}:
  Equal.trans(U32, S.gen_of(SC.take(U32, gl, n), i), W32.nth0(SC.take(U32, gl, n), i), W32.nth0(gl, i), gen_nth0(SC.take(U32, gl, n), i), nth0_take(gl, n, i, h))

def gen_snoc(+gl: List<&2, U32>, +g: U32) -> {S.gen_of(SC.snoc(U32, gl, g), SC.length(U32, gl)) == g : U32}:
  match gl:
    case Nil{}:
      {==}
    case Con{x, +t}:
      gen_snoc(t, g)

# ---- prefixes ----

def take_upd_succ(-X: Data, +xs: List<&2, X>, +n: Nat, +v: X, +h: {Nat.is_lt(n, SC.length(X, xs)) == True{} : Bool}) -> {SC.take(X, SC.update(X, xs, n, v), 1n+n) == SC.snoc(X, SC.take(X, xs, n), v) : List<&2, X>}:
  match xs n:
    case Nil{} _:
      Empty.absurd({Nil{} == SC.snoc(X, Nil{}, v) : List<&2, X>}, N.lt_zero_absurd(n, h))
    case Con{x, +t} 0n:
      LL.cons_cong(X, v, SC.take(X, t, 0n), Nil{}, LL.sc_take_zero(X, t))
    case Con{x, +t} 1n+p:
      LL.cons_cong(X, x, SC.take(X, SC.update(X, t, p, v), 1n+p), SC.snoc(X, SC.take(X, t, p), v), take_upd_succ(X, t, p, v, h))

def upd_snoc(-X: Data, +ys: List<&2, X>, +dv: X, +v: X) -> {SC.update(X, SC.snoc(X, ys, dv), SC.length(X, ys), v) == SC.snoc(X, ys, v) : List<&2, X>}:
  match ys:
    case Nil{}:
      {==}
    case Con{y, +t}:
      LL.cons_cong(X, y, SC.update(X, SC.snoc(X, t, dv), SC.length(X, t), v), SC.snoc(X, t, v), upd_snoc(X, t, dv, v))

def take_succ_u(+xs: List<&2, U32>, +n: Nat, +h: {Nat.is_lt(n, SC.length(U32, xs)) == True{} : Bool}) -> {SC.take(U32, xs, 1n+n) == SC.snoc(U32, SC.take(U32, xs, n), W32.nth0(xs, n)) : List<&2, U32>}:
  match xs n:
    case Nil{} _:
      Empty.absurd({Nil{} == SC.snoc(U32, Nil{}, 0) : List<&2, U32>}, N.lt_zero_absurd(n, h))
    case Con{x, +t} 0n:
      LL.cons_cong(U32, x, SC.take(U32, t, 0n), Nil{}, LL.sc_take_zero(U32, t))
    case Con{x, +t} 1n+p:
      LL.cons_cong(U32, x, SC.take(U32, t, 1n+p), SC.snoc(U32, SC.take(U32, t, p), W32.nth0(t, p)), take_succ_u(t, p, h))

# ---- the live-listed component, pointwise ----

def or_nt(+b: Bool, +c: Bool, +h: {Bool.or(Bool.not(b), c) == True{} : Bool}, +hb: {b == True{} : Bool}) -> {c == True{} : Bool}:
  L.subst(Bool, z => {Bool.or(Bool.not(z), c) == True{} : Bool}, b, True{}, hb, h)

# every live index x (from k) is the id k + x of sl
def lvin_elim(~T: Data, +vl: List<&2, Maybe<&2, T>>, +k: Nat, +sl: List<&2, Nat>, +h: {ST.lvin(~T, vl, k, sl) == True{} : Bool}, +x: Nat, +hx: {ST.some_b(T, S.val_of(T, vl, x)) == True{} : Bool}) -> {NL.memn(Nat.add(k, x), sl) == True{} : Bool}:
  match vl x:
    case Nil{} _:
      Empty.absurd({NL.memn(Nat.add(k, x), sl) == True{} : Bool}, L.false_true(hx))
    case Con{+m, +t} 0n:
      +h0 = L.and_left(Bool.or(Bool.not(ST.some_b(T, m)), NL.memn(k, sl)), ST.lvin(~T, t, 1n+k, sl), h)
      L.subst(Nat, z => {NL.memn(z, sl) == True{} : Bool}, k, Nat.add(k, 0n), Equal.sym(Nat, Nat.add(k, 0n), k, N.add_zero(k)), or_nt(ST.some_b(T, m), NL.memn(k, sl), h0, hx))
    case Con{+m, +t} 1n+p:
      +ih = lvin_elim(~T, t, 1n+k, sl, L.and_right(Bool.or(Bool.not(ST.some_b(T, m)), NL.memn(k, sl)), ST.lvin(~T, t, 1n+k, sl), h), p, hx)
      L.subst(Nat, z => {NL.memn(z, sl) == True{} : Bool}, 1n+Nat.add(k, p), Nat.add(k, 1n+p), Equal.sym(Nat, Nat.add(k, 1n+p), 1n+Nat.add(k, p), N.add_succ(k, p)), ih)


def or_tr2(+a: Bool, +b: Bool, +h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  L.subst(Bool, z => {Bool.or(a, z) == True{} : Bool}, True{}, b, Equal.sym(Bool, b, True{}, h), NL.or_true_b(a))

# a write of a value at a listed index
def lvin_upd(~T: Data, +vl: List<&2, Maybe<&2, T>>, +k: Nat, +sl: List<&2, Nat>, +j: Nat, +v: Maybe<&2, T>, +h: {ST.lvin(~T, vl, k, sl) == True{} : Bool}, +hm: {NL.memn(Nat.add(k, j), sl) == True{} : Bool}) -> {ST.lvin(~T, SC.update(Maybe<&2, T>, vl, j, v), k, sl) == True{} : Bool}:
  match vl j:
    case Nil{} _:
      {==}
    case Con{+m, +t} 0n:
      +hm0 = L.subst(Nat, z => {NL.memn(z, sl) == True{} : Bool}, Nat.add(k, 0n), k, N.add_zero(k), hm)
      L.and_intro(Bool.or(Bool.not(ST.some_b(T, v)), NL.memn(k, sl)), ST.lvin(~T, t, 1n+k, sl), or_tr2(Bool.not(ST.some_b(T, v)), NL.memn(k, sl), hm0), L.and_right(Bool.or(Bool.not(ST.some_b(T, m)), NL.memn(k, sl)), ST.lvin(~T, t, 1n+k, sl), h))
    case Con{+m, +t} 1n+p:
      +hm1 = L.subst(Nat, z => {NL.memn(z, sl) == True{} : Bool}, Nat.add(k, 1n+p), 1n+Nat.add(k, p), N.add_succ(k, p), hm)
      L.and_intro(Bool.or(Bool.not(ST.some_b(T, m)), NL.memn(k, sl)), ST.lvin(~T, SC.update(Maybe<&2, T>, t, p, v), 1n+k, sl), L.and_left(Bool.or(Bool.not(ST.some_b(T, m)), NL.memn(k, sl)), ST.lvin(~T, t, 1n+k, sl), h), lvin_upd(~T, t, 1n+k, sl, p, v, L.and_right(Bool.or(Bool.not(ST.some_b(T, m)), NL.memn(k, sl)), ST.lvin(~T, t, 1n+k, sl), h), hm1))

# a write of None
def lvin_none(~T: Data, +vl: List<&2, Maybe<&2, T>>, +k: Nat, +sl: List<&2, Nat>, +j: Nat, +h: {ST.lvin(~T, vl, k, sl) == True{} : Bool}) -> {ST.lvin(~T, SC.update(Maybe<&2, T>, vl, j, None{}), k, sl) == True{} : Bool}:
  match vl j:
    case Nil{} _:
      {==}
    case Con{+m, +t} 0n:
      L.and_right(Bool.or(Bool.not(ST.some_b(T, m)), NL.memn(k, sl)), ST.lvin(~T, t, 1n+k, sl), h)
    case Con{+m, +t} 1n+p:
      L.and_intro(Bool.or(Bool.not(ST.some_b(T, m)), NL.memn(k, sl)), ST.lvin(~T, SC.update(Maybe<&2, T>, t, p, None{}), 1n+k, sl), L.and_left(Bool.or(Bool.not(ST.some_b(T, m)), NL.memn(k, sl)), ST.lvin(~T, t, 1n+k, sl), h), lvin_none(~T, t, 1n+k, sl, p, L.and_right(Bool.or(Bool.not(ST.some_b(T, m)), NL.memn(k, sl)), ST.lvin(~T, t, 1n+k, sl), h)))

# ---- ids of one list among another's ----

def subn(xs: List<&2, Nat>, +ys: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(NL.memn(x, ys), subn(t, ys))

def subn_c(+x: Nat, +y: Nat, +t: List<&2, Nat>, +ys: List<&2, Nat>, +hy: {NL.memn(y, ys) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(y, x) == c : Bool}, +hm: {Bool.or(c, NL.memn(x, t)) == True{} : Bool}, rec: @hm2: {NL.memn(x, t) == True{} : Bool} -> {NL.memn(x, ys) == True{} : Bool}) -> {NL.memn(x, ys) == True{} : Bool}:
  match c:
    case True{}:
      L.subst(Nat, z => {NL.memn(z, ys) == True{} : Bool}, y, x, N.eq_from_is_eq(y, x, hc), hy)
    case False{}:
      rec(hm)

def subn_mem(+xs: List<&2, Nat>, +ys: List<&2, Nat>, +x: Nat, +h: {subn(xs, ys) == True{} : Bool}, +hm: {NL.memn(x, xs) == True{} : Bool}) -> {NL.memn(x, ys) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({NL.memn(x, ys) == True{} : Bool}, L.false_true(hm))
    case Con{+y, +t}:
      subn_c(x, y, t, ys, L.and_left(NL.memn(y, ys), subn(t, ys), h), Nat.is_eq(y, x), {==}, hm, hm2 => subn_mem(t, ys, x, L.and_right(NL.memn(y, ys), subn(t, ys), h), hm2))

def subn_wk(+xs: List<&2, Nat>, +ys: List<&2, Nat>, +y: Nat, +h: {subn(xs, ys) == True{} : Bool}) -> {subn(xs, Con{y, ys}) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.and_intro(NL.memn(x, Con{y, ys}), subn(t, Con{y, ys}), NL.or_tr(Nat.is_eq(y, x), NL.memn(x, ys), L.and_left(NL.memn(x, ys), subn(t, ys), h)), subn_wk(t, ys, y, L.and_right(NL.memn(x, ys), subn(t, ys), h)))

def subn_refl(+xs: List<&2, Nat>) -> {subn(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.and_intro(NL.memn(x, Con{x, t}), subn(t, Con{x, t}), RL.self_in(x, t), subn_wk(t, t, x, subn_refl(t)))

def mem2_c(+x: Nat, +y: Nat, +z: Nat, +ys: List<&2, Nat>, +c: Bool, +h: {Bool.or(c, NL.memn(x, ys)) == True{} : Bool}) -> {Bool.or(c, Bool.or(Nat.is_eq(z, x), NL.memn(x, ys))) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      NL.or_tr(Nat.is_eq(z, x), NL.memn(x, ys), h)

def subn_wk2(+xs: List<&2, Nat>, +y: Nat, +z: Nat, +ys: List<&2, Nat>, +h: {subn(xs, Con{y, ys}) == True{} : Bool}) -> {subn(xs, Con{y, Con{z, ys}}) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.and_intro(NL.memn(x, Con{y, Con{z, ys}}), subn(t, Con{y, Con{z, ys}}), mem2_c(x, y, z, ys, Nat.is_eq(y, x), L.and_left(NL.memn(x, Con{y, ys}), subn(t, Con{y, ys}), h)), subn_wk2(t, y, z, ys, L.and_right(NL.memn(x, Con{y, ys}), subn(t, Con{y, ys}), h)))


# a ++ b among a ++ n :: b
def subn_ins(+a: List<&2, Nat>, +b: List<&2, Nat>, +n: Nat) -> {subn(SC.append(Nat, a, b), SC.append(Nat, a, Con{n, b})) == True{} : Bool}:
  match a:
    case Nil{}:
      subn_wk(b, b, n, subn_refl(b))
    case Con{+x, +t}:
      L.and_intro(NL.memn(x, Con{x, SC.append(Nat, t, Con{n, b})}), subn(SC.append(Nat, t, b), Con{x, SC.append(Nat, t, Con{n, b})}), RL.self_in(x, SC.append(Nat, t, Con{n, b})), subn_wk(SC.append(Nat, t, b), SC.append(Nat, t, Con{n, b}), x, subn_ins(t, b, n)))

# a ++ s :: b among s :: a ++ b
def subn_rm(+a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>) -> {subn(SC.append(Nat, a, Con{s, b}), Con{s, SC.append(Nat, a, b)}) == True{} : Bool}:
  match a:
    case Nil{}:
      subn_refl(Con{s, b})
    case Con{+x, +t}:
      L.and_intro(NL.memn(x, Con{s, Con{x, SC.append(Nat, t, b)}}), subn(SC.append(Nat, t, Con{s, b}), Con{s, Con{x, SC.append(Nat, t, b)}}), NL.or_tr(Nat.is_eq(s, x), NL.memn(x, Con{x, SC.append(Nat, t, b)}), RL.self_in(x, SC.append(Nat, t, b))), subn_wk2(SC.append(Nat, t, Con{s, b}), s, x, SC.append(Nat, t, b), subn_rm(t, s, b)))

def ornc(-T: Data, +m: Maybe<&2, T>, +c: Bool, +c0: Bool, +h: {Bool.or(Bool.not(ST.some_b(T, m)), c0) == True{} : Bool}, f: @hc: {c0 == True{} : Bool} -> {c == True{} : Bool}) -> {Bool.or(Bool.not(ST.some_b(T, m)), c) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      f(h)

# a larger list of ids
def lvin_sub(~T: Data, +vl: List<&2, Maybe<&2, T>>, +k: Nat, +sl: List<&2, Nat>, +sl2: List<&2, Nat>, +h: {ST.lvin(~T, vl, k, sl) == True{} : Bool}, +hs: {subn(sl, sl2) == True{} : Bool}) -> {ST.lvin(~T, vl, k, sl2) == True{} : Bool}:
  match vl:
    case Nil{}:
      {==}
    case Con{+m, +t}:
      +h0 = ornc(T, m, NL.memn(k, sl2), NL.memn(k, sl), L.and_left(Bool.or(Bool.not(ST.some_b(T, m)), NL.memn(k, sl)), ST.lvin(~T, t, 1n+k, sl), h), hk => subn_mem(sl, sl2, k, hs, hk))
      L.and_intro(Bool.or(Bool.not(ST.some_b(T, m)), NL.memn(k, sl2)), ST.lvin(~T, t, 1n+k, sl2), h0, lvin_sub(~T, t, 1n+k, sl, sl2, L.and_right(Bool.or(Bool.not(ST.some_b(T, m)), NL.memn(k, sl)), ST.lvin(~T, t, 1n+k, sl), h), hs))

# indices from k are all above s: s can be dropped
def lvin_low(~T: Data, +vl: List<&2, Maybe<&2, T>>, +k: Nat, +s: Nat, +sl: List<&2, Nat>, +h: {ST.lvin(~T, vl, k, Con{s, sl}) == True{} : Bool}, +hlt: {Nat.is_lt(s, k) == True{} : Bool}) -> {ST.lvin(~T, vl, k, sl) == True{} : Bool}:
  match vl:
    case Nil{}:
      {==}
    case Con{+m, +t}:
      +hne = N.is_eq_lt(s, k, hlt)
      +h0 = ornc(T, m, NL.memn(k, sl), NL.memn(k, Con{s, sl}), L.and_left(Bool.or(Bool.not(ST.some_b(T, m)), NL.memn(k, Con{s, sl})), ST.lvin(~T, t, 1n+k, Con{s, sl}), h), hk => L.subst(Bool, z => {Bool.or(z, NL.memn(k, sl)) == True{} : Bool}, Nat.is_eq(s, k), False{}, hne, hk))
      L.and_intro(Bool.or(Bool.not(ST.some_b(T, m)), NL.memn(k, sl)), ST.lvin(~T, t, 1n+k, sl), h0, lvin_low(~T, t, 1n+k, s, sl, L.and_right(Bool.or(Bool.not(ST.some_b(T, m)), NL.memn(k, Con{s, sl})), ST.lvin(~T, t, 1n+k, Con{s, sl}), h), N.lt_trans(s, k, 1n+k, hlt, N.lt_succ(k))))

# the id s = k + j with a vacant value can be dropped
def lvin_skip(~T: Data, +vl: List<&2, Maybe<&2, T>>, +k: Nat, +j: Nat, +sl: List<&2, Nat>, +h: {ST.lvin(~T, vl, k, Con{Nat.add(k, j), sl}) == True{} : Bool}, +hv: {ST.some_b(T, S.val_of(T, vl, j)) == False{} : Bool}) -> {ST.lvin(~T, vl, k, sl) == True{} : Bool}:
  match vl j:
    case Nil{} _:
      {==}
    case Con{+m, +t} 0n:
      +h1 = L.and_right(Bool.or(Bool.not(ST.some_b(T, m)), NL.memn(k, Con{Nat.add(k, 0n), sl})), ST.lvin(~T, t, 1n+k, Con{Nat.add(k, 0n), sl}), h)
      +h1b = L.subst(Nat, z => {ST.lvin(~T, t, 1n+k, Con{z, sl}) == True{} : Bool}, Nat.add(k, 0n), k, N.add_zero(k), h1)
      +h0 = L.subst(Bool, z => {Bool.or(Bool.not(z), NL.memn(k, sl)) == True{} : Bool}, False{}, ST.some_b(T, m), Equal.sym(Bool, ST.some_b(T, m), False{}, hv), {==})
      L.and_intro(Bool.or(Bool.not(ST.some_b(T, m)), NL.memn(k, sl)), ST.lvin(~T, t, 1n+k, sl), h0, lvin_low(~T, t, 1n+k, k, sl, h1b, N.lt_succ(k)))
    case Con{+m, +t} 1n+p:
      +e = N.add_succ(k, p)
      +hne = N.is_eq_lt(k, 1n+Nat.add(k, p), N.le_lt_succ(k, Nat.add(k, p), N.le_add_right(k, p)))
      +hne2 = L.subst(Nat, z => {Nat.is_eq(z, k) == False{} : Bool}, 1n+Nat.add(k, p), Nat.add(k, 1n+p), Equal.sym(Nat, Nat.add(k, 1n+p), 1n+Nat.add(k, p), e), N.is_eq_sym_false(k, 1n+Nat.add(k, p), hne))
      +h0 = ornc(T, m, NL.memn(k, sl), NL.memn(k, Con{Nat.add(k, 1n+p), sl}), L.and_left(Bool.or(Bool.not(ST.some_b(T, m)), NL.memn(k, Con{Nat.add(k, 1n+p), sl})), ST.lvin(~T, t, 1n+k, Con{Nat.add(k, 1n+p), sl}), h), hk => L.subst(Bool, z => {Bool.or(z, NL.memn(k, sl)) == True{} : Bool}, Nat.is_eq(Nat.add(k, 1n+p), k), False{}, hne2, hk))
      +h1 = L.and_right(Bool.or(Bool.not(ST.some_b(T, m)), NL.memn(k, Con{Nat.add(k, 1n+p), sl})), ST.lvin(~T, t, 1n+k, Con{Nat.add(k, 1n+p), sl}), h)
      +h1b = L.subst(Nat, z => {ST.lvin(~T, t, 1n+k, Con{z, sl}) == True{} : Bool}, Nat.add(k, 1n+p), Nat.add(1n+k, p), e, h1)
      L.and_intro(Bool.or(Bool.not(ST.some_b(T, m)), NL.memn(k, sl)), ST.lvin(~T, t, 1n+k, sl), h0, lvin_skip(~T, t, 1n+k, p, sl, h1b, hv))

def lvin_rep(~T: Data, +m: Nat, +k: Nat, +sl: List<&2, Nat>) -> {ST.lvin(~T, SC.replicate(Maybe<&2, T>, m, None{}), k, sl) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      lvin_rep(~T, p, 1n+k, sl)

# vacant slots appended
def lvin_grow(~T: Data, +vl: List<&2, Maybe<&2, T>>, +k: Nat, +sl: List<&2, Nat>, +m: Nat, +h: {ST.lvin(~T, vl, k, sl) == True{} : Bool}) -> {ST.lvin(~T, SC.append(Maybe<&2, T>, vl, SC.replicate(Maybe<&2, T>, m, None{})), k, sl) == True{} : Bool}:
  match vl:
    case Nil{}:
      lvin_rep(~T, m, k, sl)
    case Con{+x, +t}:
      L.and_intro(Bool.or(Bool.not(ST.some_b(T, x)), NL.memn(k, sl)), ST.lvin(~T, SC.append(Maybe<&2, T>, t, SC.replicate(Maybe<&2, T>, m, None{})), 1n+k, sl), L.and_left(Bool.or(Bool.not(ST.some_b(T, x)), NL.memn(k, sl)), ST.lvin(~T, t, 1n+k, sl), h), lvin_grow(~T, t, 1n+k, sl, m, L.and_right(Bool.or(Bool.not(ST.some_b(T, x)), NL.memn(k, sl)), ST.lvin(~T, t, 1n+k, sl), h)))

# ---- the zero-generation component ----

def gz_at(+gl: List<&2, U32>, +fr: Nat, +h: {ST.gz(gl, fr) == True{} : Bool}, +hl: {Nat.is_lt(fr, SC.length(U32, gl)) == True{} : Bool}) -> {W32.nth0(gl, fr) == 0 : U32}:
  match gl fr:
    case Nil{} _:
      Empty.absurd({W32.nth0(Nil{}, fr) == 0 : U32}, N.lt_zero_absurd(fr, hl))
    case Con{+g, +t} 0n:
      A.eq_of(g, 0, L.and_left(U32.is_eq(g, 0), ST.gz(t, 0n), h))
    case Con{+g, +t} 1n+p:
      gz_at(t, p, h, hl)

def gz_succ(+gl: List<&2, U32>, +fr: Nat, +h: {ST.gz(gl, fr) == True{} : Bool}) -> {ST.gz(gl, 1n+fr) == True{} : Bool}:
  match gl fr:
    case Nil{} _:
      {==}
    case Con{+g, +t} 0n:
      L.and_right(U32.is_eq(g, 0), ST.gz(t, 0n), h)
    case Con{+g, +t} 1n+p:
      gz_succ(t, p, h)

def gz_upd(+gl: List<&2, U32>, +fr: Nat, +i: Nat, +v: U32, +h: {ST.gz(gl, fr) == True{} : Bool}, +hi: {Nat.is_lt(i, fr) == True{} : Bool}) -> {ST.gz(SC.update(U32, gl, i, v), fr) == True{} : Bool}:
  match gl fr i:
    case Nil{} _ _:
      {==}
    case Con{g, t} 0n _:
      Empty.absurd({ST.gz(SC.update(U32, Con{g, t}, i, v), 0n) == True{} : Bool}, N.lt_zero_absurd(i, hi))
    case Con{g, t} 1n+q 0n:
      h
    case Con{g, +t} 1n+q 1n+p:
      gz_upd(t, q, p, v, h, hi)

def gz_rep(+m: Nat) -> {ST.gz(SC.replicate(U32, m, 0), 0n) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      gz_rep(p)

def gz_grow(+gl: List<&2, U32>, +m: Nat) -> {ST.gz(SC.append(U32, gl, SC.replicate(U32, m, 0)), SC.length(U32, gl)) == True{} : Bool}:
  match gl:
    case Nil{}:
      gz_rep(m)
    case Con{g, +t}:
      gz_grow(t, m)
