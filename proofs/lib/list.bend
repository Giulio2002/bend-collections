import Base
import ./logic.bend as L
import ./nat.bend as N
import ../../spec/common.bend as SC

# Lemmas about the specification list vocabulary (spec/common.bend).

def cons_cong(-A: Data, +h: A, +xs: List<&2, A>, +ys: List<&2, A>, +e: {xs == ys : List<&2, A>}) -> {Con{h, xs} == Con{h, ys} : List<&2, A>}:
  Equal.cong(List<&2, A>, List<&2, A>, zs => Con{h, zs}, xs, ys, e)

def append_nil(-A: Data, +xs: List<&2, A>) -> {SC.append(A, xs, Nil{}) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      cons_cong(A, h, SC.append(A, t, Nil{}), t, append_nil(A, t))

def append_assoc(-A: Data, +xs: List<&2, A>, +ys: List<&2, A>, +zs: List<&2, A>) -> {SC.append(A, SC.append(A, xs, ys), zs) == SC.append(A, xs, SC.append(A, ys, zs)) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      cons_cong(A, h, SC.append(A, SC.append(A, t, ys), zs), SC.append(A, t, SC.append(A, ys, zs)), append_assoc(A, t, ys, zs))

def length_append(-A: Data, +xs: List<&2, A>, +ys: List<&2, A>) -> {SC.length(A, SC.append(A, xs, ys)) == Nat.add(SC.length(A, xs), SC.length(A, ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      N.succ_cong(SC.length(A, SC.append(A, t, ys)), Nat.add(SC.length(A, t), SC.length(A, ys)), length_append(A, t, ys))

def snoc_append(-A: Data, +xs: List<&2, A>, +x: A) -> {SC.snoc(A, xs, x) == SC.append(A, xs, Con{x, Nil{}}) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      cons_cong(A, h, SC.snoc(A, t, x), SC.append(A, t, Con{x, Nil{}}), snoc_append(A, t, x))

def length_snoc(-A: Data, +xs: List<&2, A>, +x: A) -> {SC.length(A, SC.snoc(A, xs, x)) == 1n+SC.length(A, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      N.succ_cong(SC.length(A, SC.snoc(A, t, x)), 1n+SC.length(A, t), length_snoc(A, t, x))

def length_replicate(-A: Data, +n: Nat, +x: A) -> {SC.length(A, SC.replicate(A, n, x)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      N.succ_cong(SC.length(A, SC.replicate(A, p, x)), p, length_replicate(A, p, x))

def replicate_add(-A: Data, +m: Nat, +n: Nat, +x: A) -> {SC.append(A, SC.replicate(A, m, x), SC.replicate(A, n, x)) == SC.replicate(A, Nat.add(m, n), x) : List<&2, A>}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      cons_cong(A, x, SC.append(A, SC.replicate(A, p, x), SC.replicate(A, n, x)), SC.replicate(A, Nat.add(p, n), x), replicate_add(A, p, n, x))

# ---- nth / update across append ----

def nth_append_left(-A: Data, +xs: List<&2, A>, +ys: List<&2, A>, +i: Nat, +h: {Nat.is_lt(i, SC.length(A, xs)) == True{} : Bool}) -> {SC.nth(A, SC.append(A, xs, ys), i) == SC.nth(A, xs, i) : Maybe<&2, A>}:
  match xs i:
    case Nil{} _:
      Empty.absurd({SC.nth(A, ys, i) == None{} : Maybe<&2, A>}, N.lt_zero_absurd(i, h))
    case Con{h1, t} 0n:
      {==}
    case Con{h1, t} 1n+p:
      nth_append_left(A, t, ys, p, h)

def nth_append_right(-A: Data, +xs: List<&2, A>, +ys: List<&2, A>, +i: Nat, +h: {Nat.is_le(SC.length(A, xs), i) == True{} : Bool}) -> {SC.nth(A, SC.append(A, xs, ys), i) == SC.nth(A, ys, Nat.sub(i, SC.length(A, xs))) : Maybe<&2, A>}:
  match xs i:
    case Nil{} _:
      %Equal.sym(Nat, Nat.sub(i, 0n), i, N.sub_zero(i)) : {SC.nth(A, ys, i) == SC.nth(A, ys, _) : Maybe<&2, A>}
      {==}
    case Con{h1, t} 0n:
      Empty.absurd({SC.nth(A, SC.append(A, Con{h1, t}, ys), 0n) == SC.nth(A, ys, Nat.sub(0n, 1n+SC.length(A, t))) : Maybe<&2, A>}, L.false_true(h))
    case Con{h1, t} 1n+p:
      nth_append_right(A, t, ys, p, h)

def update_append_left(-A: Data, +xs: List<&2, A>, +ys: List<&2, A>, +i: Nat, +v: A, +h: {Nat.is_lt(i, SC.length(A, xs)) == True{} : Bool}) -> {SC.update(A, SC.append(A, xs, ys), i, v) == SC.append(A, SC.update(A, xs, i, v), ys) : List<&2, A>}:
  match xs i:
    case Nil{} _:
      Empty.absurd({SC.update(A, ys, i, v) == SC.append(A, Nil{}, ys) : List<&2, A>}, N.lt_zero_absurd(i, h))
    case Con{h1, t} 0n:
      {==}
    case Con{+h1, t} 1n+p:
      cons_cong(A, h1, SC.update(A, SC.append(A, t, ys), p, v), SC.append(A, SC.update(A, t, p, v), ys), update_append_left(A, t, ys, p, v, h))

def update_append_right(-A: Data, +xs: List<&2, A>, +ys: List<&2, A>, +i: Nat, +v: A, +h: {Nat.is_le(SC.length(A, xs), i) == True{} : Bool}) -> {SC.update(A, SC.append(A, xs, ys), i, v) == SC.append(A, xs, SC.update(A, ys, Nat.sub(i, SC.length(A, xs)), v)) : List<&2, A>}:
  match xs i:
    case Nil{} _:
      %Equal.sym(Nat, Nat.sub(i, 0n), i, N.sub_zero(i)) : {SC.update(A, ys, i, v) == SC.update(A, ys, _, v) : List<&2, A>}
      {==}
    case Con{h1, t} 0n:
      Empty.absurd({SC.update(A, SC.append(A, Con{h1, t}, ys), 0n, v) == SC.append(A, Con{h1, t}, SC.update(A, ys, Nat.sub(0n, 1n+SC.length(A, t)), v)) : List<&2, A>}, L.false_true(h))
    case Con{+h1, t} 1n+p:
      cons_cong(A, h1, SC.update(A, SC.append(A, t, ys), p, v), SC.append(A, t, SC.update(A, ys, Nat.sub(p, SC.length(A, t)), v)), update_append_right(A, t, ys, p, v, h))

def length_update(-A: Data, +xs: List<&2, A>, +i: Nat, +v: A) -> {SC.length(A, SC.update(A, xs, i, v)) == SC.length(A, xs) : Nat}:
  match xs i:
    case Nil{} _:
      {==}
    case Con{h1, t} 0n:
      {==}
    case Con{h1, t} 1n+p:
      N.succ_cong(SC.length(A, SC.update(A, t, p, v)), SC.length(A, t), length_update(A, t, p, v))

def nth_lt_length(-A: Data, +xs: List<&2, A>, +i: Nat, +x: A, +h: {SC.nth(A, xs, i) == Some{x} : Maybe<&2, A>}) -> {Nat.is_lt(i, SC.length(A, xs)) == True{} : Bool}:
  match xs i:
    case Nil{} _:
      Empty.absurd({Nat.is_lt(i, 0n) == True{} : Bool}, L.none_some(A, x, h))
    case Con{h1, t} 0n:
      {==}
    case Con{h1, t} 1n+p:
      nth_lt_length(A, t, p, x, h)

def nth_update_same(-A: Data, +xs: List<&2, A>, +i: Nat, +v: A, +h: {Nat.is_lt(i, SC.length(A, xs)) == True{} : Bool}) -> {SC.nth(A, SC.update(A, xs, i, v), i) == Some{v} : Maybe<&2, A>}:
  match xs i:
    case Nil{} _:
      Empty.absurd({SC.nth(A, Nil{}, i) == Some{v} : Maybe<&2, A>}, N.lt_zero_absurd(i, h))
    case Con{h1, t} 0n:
      {==}
    case Con{h1, t} 1n+p:
      nth_update_same(A, t, p, v, h)

def nth_none(-A: Data, +xs: List<&2, A>, +i: Nat, +h: {Nat.is_le(SC.length(A, xs), i) == True{} : Bool}) -> {SC.nth(A, xs, i) == None{} : Maybe<&2, A>}:
  match xs i:
    case Nil{} _:
      {==}
    case Con{x, t} 0n:
      Empty.absurd({Some{x} == None{} : Maybe<&2, A>}, L.false_true(h))
    case Con{x, +t} 1n+p:
      nth_none(A, t, p, h)

# Base List.append agrees with the specification append.
def base_append(-A: Data, +xs: List<&2, A>, +ys: List<&2, A>) -> {List.append(&2, A, xs, ys) == SC.append(A, xs, ys) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      cons_cong(A, h, List.append(&2, A, t, ys), SC.append(A, t, ys), base_append(A, t, ys))

def length_zero_nil(-A: Data, +xs: List<&2, A>, +h: {SC.length(A, xs) == 0n : Nat}) -> {xs == Nil{} : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      Empty.absurd({Con{x, t} == Nil{} : List<&2, A>}, N.succ_zero(SC.length(A, t), h))

# reverse.go(reverse.go(xs, a), b) == reverse.go(a, xs ++ b)
def rev_go_twice(-A: Data, +xs: List<&2, A>, +a: List<&2, A>, +b: List<&2, A>) -> {List.reverse.go(&2, A, List.reverse.go(&2, A, xs, a), b) == List.reverse.go(&2, A, a, SC.append(A, xs, b)) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      rev_go_twice(A, t, Con{h, a}, b)

def rev_rev(-A: Data, +xs: List<&2, A>) -> {List.reverse(&2, A, List.reverse.go(&2, A, xs, Nil{})) == xs : List<&2, A>}:
  Equal.trans(List<&2, A>, List.reverse.go(&2, A, List.reverse.go(&2, A, xs, Nil{}), Nil{}), SC.append(A, xs, Nil{}), xs, rev_go_twice(A, xs, Nil{}, Nil{}), append_nil(A, xs))

def nth_update_other(-A: Data, +xs: List<&2, A>, +i: Nat, +j: Nat, +v: A, +ne: {Nat.is_eq(i, j) == False{} : Bool}) -> {SC.nth(A, SC.update(A, xs, i, v), j) == SC.nth(A, xs, j) : Maybe<&2, A>}:
  match xs i j:
    case Nil{} _ _:
      {==}
    case Con{h, t} 0n 0n:
      Empty.absurd({Some{v} == Some{h} : Maybe<&2, A>}, L.true_false(ne))
    case Con{h, t} 0n 1n+q:
      {==}
    case Con{h, t} 1n+p 0n:
      {==}
    case Con{h, +t} 1n+p 1n+q:
      nth_update_other(A, t, p, q, v, ne)

# ---- snoc / reverse ----

def append_snoc(-A: Data, +xs: List<&2, A>, +ys: List<&2, A>, +x: A) -> {SC.append(A, xs, SC.snoc(A, ys, x)) == SC.snoc(A, SC.append(A, xs, ys), x) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      cons_cong(A, h, SC.append(A, t, SC.snoc(A, ys, x)), SC.snoc(A, SC.append(A, t, ys), x), append_snoc(A, t, ys, x))

def snoc_append_cons(-A: Data, +xs: List<&2, A>, +x: A, +acc: List<&2, A>) -> {SC.append(A, SC.snoc(A, xs, x), acc) == SC.append(A, xs, Con{x, acc}) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      cons_cong(A, h, SC.append(A, SC.snoc(A, t, x), acc), SC.append(A, t, Con{x, acc}), snoc_append_cons(A, t, x, acc))

def rev_snoc(-A: Data, +xs: List<&2, A>, +x: A) -> {SC.reverse(A, SC.snoc(A, xs, x)) == Con{x, SC.reverse(A, xs)} : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.cong(List<&2, A>, List<&2, A>, zs => SC.snoc(A, zs, h), SC.reverse(A, SC.snoc(A, t, x)), Con{x, SC.reverse(A, t)}, rev_snoc(A, t, x))

def spec_rev_rev(-A: Data, +xs: List<&2, A>) -> {SC.reverse(A, SC.reverse(A, xs)) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.trans(List<&2, A>, SC.reverse(A, SC.snoc(A, SC.reverse(A, t), h)), Con{h, SC.reverse(A, SC.reverse(A, t))}, Con{h, t},
        rev_snoc(A, SC.reverse(A, t), h), cons_cong(A, h, SC.reverse(A, SC.reverse(A, t)), t, spec_rev_rev(A, t)))

def rev_append(-A: Data, +xs: List<&2, A>, +ys: List<&2, A>) -> {SC.reverse(A, SC.append(A, xs, ys)) == SC.append(A, SC.reverse(A, ys), SC.reverse(A, xs)) : List<&2, A>}:
  match xs:
    case Nil{}:
      Equal.sym(List<&2, A>, SC.append(A, SC.reverse(A, ys), Nil{}), SC.reverse(A, ys), append_nil(A, SC.reverse(A, ys)))
    case Con{+h, +t}:
      Equal.trans(List<&2, A>, SC.snoc(A, SC.reverse(A, SC.append(A, t, ys)), h), SC.snoc(A, SC.append(A, SC.reverse(A, ys), SC.reverse(A, t)), h), SC.append(A, SC.reverse(A, ys), SC.snoc(A, SC.reverse(A, t), h)),
        Equal.cong(List<&2, A>, List<&2, A>, zs => SC.snoc(A, zs, h), SC.reverse(A, SC.append(A, t, ys)), SC.append(A, SC.reverse(A, ys), SC.reverse(A, t)), rev_append(A, t, ys)),
        Equal.sym(List<&2, A>, SC.append(A, SC.reverse(A, ys), SC.snoc(A, SC.reverse(A, t), h)), SC.snoc(A, SC.append(A, SC.reverse(A, ys), SC.reverse(A, t)), h), append_snoc(A, SC.reverse(A, ys), SC.reverse(A, t), h)))

def length_rev(-A: Data, +xs: List<&2, A>) -> {SC.length(A, SC.reverse(A, xs)) == SC.length(A, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.trans(Nat, SC.length(A, SC.snoc(A, SC.reverse(A, t), h)), 1n+SC.length(A, SC.reverse(A, t)), 1n+SC.length(A, t), length_snoc(A, SC.reverse(A, t), h), N.succ_cong(SC.length(A, SC.reverse(A, t)), SC.length(A, t), length_rev(A, t)))

def base_rev_go(-A: Data, +xs: List<&2, A>, +acc: List<&2, A>) -> {List.reverse.go(&2, A, xs, acc) == SC.append(A, SC.reverse(A, xs), acc) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.trans(List<&2, A>, List.reverse.go(&2, A, t, Con{h, acc}), SC.append(A, SC.reverse(A, t), Con{h, acc}), SC.append(A, SC.snoc(A, SC.reverse(A, t), h), acc),
        base_rev_go(A, t, Con{h, acc}), Equal.sym(List<&2, A>, SC.append(A, SC.snoc(A, SC.reverse(A, t), h), acc), SC.append(A, SC.reverse(A, t), Con{h, acc}), snoc_append_cons(A, SC.reverse(A, t), h, acc)))

def base_rev(-A: Data, +xs: List<&2, A>) -> {List.reverse(&2, A, xs) == SC.reverse(A, xs) : List<&2, A>}:
  Equal.trans(List<&2, A>, List.reverse.go(&2, A, xs, Nil{}), SC.append(A, SC.reverse(A, xs), Nil{}), SC.reverse(A, xs), base_rev_go(A, xs, Nil{}), append_nil(A, SC.reverse(A, xs)))

# ---- Base take / drop ----

def base_take_drop(-A: Data, +xs: List<&2, A>, +k: Nat) -> {SC.append(A, List.take(&2, A, xs, k), List.drop(&2, A, xs, k)) == xs : List<&2, A>}:
  match xs k:
    case Nil{} _:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{+h, +t} 1n+p:
      cons_cong(A, h, SC.append(A, List.take(&2, A, t, p), List.drop(&2, A, t, p)), t, base_take_drop(A, t, p))

def length_take(-A: Data, +xs: List<&2, A>, +k: Nat, +h: {Nat.is_le(k, SC.length(A, xs)) == True{} : Bool}) -> {SC.length(A, List.take(&2, A, xs, k)) == k : Nat}:
  match xs k:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      Empty.absurd({0n == 1n+p : Nat}, L.false_true(h))
    case Con{x, t} 0n:
      {==}
    case Con{x, +t} 1n+p:
      N.succ_cong(SC.length(A, List.take(&2, A, t, p)), p, length_take(A, t, p, h))

def length_drop(-A: Data, +xs: List<&2, A>, +k: Nat) -> {SC.length(A, List.drop(&2, A, xs, k)) == Nat.sub(SC.length(A, xs), k) : Nat}:
  match xs k:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      {==}
    case Con{x, t} 0n:
      {==}
    case Con{x, +t} 1n+p:
      length_drop(A, t, p)

# ---- last / init ----

def last_snoc(-A: Data, +xs: List<&2, A>, +x: A) -> {SC.last(A, SC.snoc(A, xs, x)) == Some{x} : Maybe<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, Nil{}}:
      {==}
    case Con{h, Con{+h2, +t2}}:
      last_snoc(A, Con{h2, t2}, x)

def init_snoc(-A: Data, +xs: List<&2, A>, +x: A) -> {SC.init(A, SC.snoc(A, xs, x)) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, Nil{}}:
      {==}
    case Con{+h, Con{+h2, +t2}}:
      cons_cong(A, h, SC.init(A, SC.snoc(A, Con{h2, t2}, x)), Con{h2, t2}, init_snoc(A, Con{h2, t2}, x))

# ---- take / drop over spec/common (generic) ----

def sc_length_take(-A: Data, +xs: List<&2, A>, +n: Nat, +h: {Nat.is_le(n, SC.length(A, xs)) == True{} : Bool}) -> {SC.length(A, SC.take(A, xs, n)) == n : Nat}:
  match xs n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+m:
      Empty.absurd({SC.length(A, SC.take(A, Nil{}, 1n+m)) == 1n+m : Nat}, L.false_true(h))
    case Con{a, t} 0n:
      {==}
    case Con{a, t} 1n+m:
      N.succ_cong(SC.length(A, SC.take(A, t, m)), m, sc_length_take(A, t, m, h))

def sc_nth_take(-A: Data, +xs: List<&2, A>, +n: Nat, +i: Nat, +h: {Nat.is_lt(i, n) == True{} : Bool}) -> {SC.nth(A, SC.take(A, xs, n), i) == SC.nth(A, xs, i) : Maybe<&2, A>}:
  match xs n i:
    case Nil{} _ _:
      {==}
    case Con{a, t} 0n _:
      Empty.absurd({SC.nth(A, SC.take(A, Con{a, t}, 0n), i) == SC.nth(A, Con{a, t}, i) : Maybe<&2, A>}, N.lt_zero_absurd(i, h))
    case Con{a, t} 1n+m 0n:
      {==}
    case Con{a, t} 1n+m 1n+j:
      sc_nth_take(A, t, m, j, h)

def sc_take_take(-A: Data, +xs: List<&2, A>, +n: Nat, +e: Nat, +h: {Nat.is_le(e, n) == True{} : Bool}) -> {SC.take(A, SC.take(A, xs, n), e) == SC.take(A, xs, e) : List<&2, A>}:
  match xs n e:
    case Nil{} _ _:
      {==}
    case Con{a, t} 0n 0n:
      {==}
    case Con{a, t} 1n+m 0n:
      {==}
    case Con{a, t} 0n 1n+f:
      Empty.absurd({SC.take(A, SC.take(A, Con{a, t}, 0n), 1n+f) == SC.take(A, Con{a, t}, 1n+f) : List<&2, A>}, L.false_true(h))
    case Con{a, t} 1n+m 1n+f:
      cons_cong(A, a, SC.take(A, SC.take(A, t, m), f), SC.take(A, t, f), sc_take_take(A, t, m, f, h))

def sc_take_zero(-A: Data, +xs: List<&2, A>) -> {SC.take(A, xs, 0n) == Nil{} : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{a, t}:
      {==}

def sc_take_append_left(-A: Data, +xs: List<&2, A>, +ys: List<&2, A>, +i: Nat, +h: {Nat.is_le(i, SC.length(A, xs)) == True{} : Bool}) -> {SC.take(A, SC.append(A, xs, ys), i) == SC.take(A, xs, i) : List<&2, A>}:
  match xs i:
    case Nil{} 0n:
      sc_take_zero(A, ys)
    case Nil{} 1n+j:
      Empty.absurd({SC.take(A, ys, 1n+j) == Nil{} : List<&2, A>}, L.false_true(h))
    case Con{a, t} 0n:
      {==}
    case Con{a, t} 1n+j:
      cons_cong(A, a, SC.take(A, SC.append(A, t, ys), j), SC.take(A, t, j), sc_take_append_left(A, t, ys, j, h))

def sc_take_append_right(-A: Data, +xs: List<&2, A>, +ys: List<&2, A>, +i: Nat, +h: {Nat.is_le(SC.length(A, xs), i) == True{} : Bool}) -> {SC.take(A, SC.append(A, xs, ys), i) == SC.append(A, xs, SC.take(A, ys, Nat.sub(i, SC.length(A, xs)))) : List<&2, A>}:
  match xs i:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+j:
      {==}
    case Con{a, t} 0n:
      Empty.absurd({SC.take(A, SC.append(A, Con{a, t}, ys), 0n) == SC.append(A, Con{a, t}, SC.take(A, ys, Nat.sub(0n, 1n+SC.length(A, t)))) : List<&2, A>}, L.false_true(h))
    case Con{a, t} 1n+j:
      cons_cong(A, a, SC.take(A, SC.append(A, t, ys), j), SC.append(A, t, SC.take(A, ys, Nat.sub(j, SC.length(A, t)))), sc_take_append_right(A, t, ys, j, h))

# take r == take l ++ (next r - l after l), for l <= r
def sub_zero_eq(+r: Nat) -> {Nat.sub(r, 0n) == r : Nat}:
  N.sub_zero(r)

def sc_take_split(-A: Data, +xs: List<&2, A>, +l: Nat, +r: Nat, +h: {Nat.is_le(l, r) == True{} : Bool}) -> {SC.take(A, xs, r) == SC.append(A, SC.take(A, xs, l), SC.take(A, SC.drop(A, xs, l), Nat.sub(r, l))) : List<&2, A>}:
  match xs l r:
    case Nil{} _ _:
      {==}
    case Con{a, t} 0n r:
      %Equal.sym(Nat, Nat.sub(r, 0n), r, sub_zero_eq(r)) : {SC.take(A, Con{a, t}, r) == SC.take(A, Con{a, t}, _) : List<&2, A>}
      {==}
    case Con{a, t} 1n+k 0n:
      Empty.absurd({SC.take(A, Con{a, t}, 0n) == SC.append(A, SC.take(A, Con{a, t}, 1n+k), SC.take(A, SC.drop(A, Con{a, t}, 1n+k), Nat.sub(0n, 1n+k))) : List<&2, A>}, L.false_true(h))
    case Con{a, t} 1n+k 1n+s:
      cons_cong(A, a, SC.take(A, t, s), SC.append(A, SC.take(A, t, k), SC.take(A, SC.drop(A, t, k), Nat.sub(s, k))), sc_take_split(A, t, k, s, h))

# drop l (take n xs) == take (n - l) (drop l xs)
def sc_drop_take(-A: Data, +xs: List<&2, A>, +n: Nat, +l: Nat) -> {SC.drop(A, SC.take(A, xs, n), l) == SC.take(A, SC.drop(A, xs, l), Nat.sub(n, l)) : List<&2, A>}:
  match xs n l:
    case Nil{} _ _:
      {==}
    case Con{a, t} 0n 0n:
      {==}
    case Con{a, t} 0n 1n+k:
      Equal.sym(List<&2, A>, SC.take(A, SC.drop(A, t, k), 0n), Nil{}, sc_take_zero(A, SC.drop(A, t, k)))
    case Con{a, t} 1n+m 0n:
      {==}
    case Con{a, t} 1n+m 1n+k:
      sc_drop_take(A, t, m, k)

def sc_take_update(-A: Data, +xs: List<&2, A>, +i: Nat, +v: A, +n: Nat) -> {SC.take(A, SC.update(A, xs, i, v), n) == SC.update(A, SC.take(A, xs, n), i, v) : List<&2, A>}:
  match xs i n:
    case Nil{} _ _:
      {==}
    case Con{a, t} 0n 0n:
      {==}
    case Con{a, t} 1n+j 0n:
      {==}
    case Con{a, t} 0n 1n+m:
      {==}
    case Con{a, t} 1n+j 1n+m:
      cons_cong(A, a, SC.take(A, SC.update(A, t, j, v), m), SC.update(A, SC.take(A, t, m), j, v), sc_take_update(A, t, j, v, m))

def sc_take_rep(-A: Data, +m: Nat, +x: A, +n: Nat, +h: {Nat.is_le(n, m) == True{} : Bool}) -> {SC.take(A, SC.replicate(A, m, x), n) == SC.replicate(A, n, x) : List<&2, A>}:
  match m n:
    case 0n 0n:
      {==}
    case 0n 1n+k:
      Empty.absurd({SC.take(A, Nil{}, 1n+k) == SC.replicate(A, 1n+k, x) : List<&2, A>}, L.false_true(h))
    case 1n+j 0n:
      {==}
    case 1n+j 1n+k:
      cons_cong(A, x, SC.take(A, SC.replicate(A, j, x), k), SC.replicate(A, k, x), sc_take_rep(A, j, x, k, h))

# nth below the length is not None
def sc_nth_some(-A: Data, +xs: List<&2, A>, +i: Nat, +h: {Nat.is_lt(i, SC.length(A, xs)) == True{} : Bool}, +e: {SC.nth(A, xs, i) == None{} : Maybe<&2, A>}) -> Empty:
  match xs i:
    case Nil{} _:
      N.lt_zero_absurd(i, h)
    case Con{a, t} 0n:
      L.none_some(A, a, Equal.sym(Maybe<&2, A>, Some{a}, None{}, e))
    case Con{a, t} 1n+j:
      sc_nth_some(A, t, j, h, e)
