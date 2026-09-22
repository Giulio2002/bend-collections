import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../spec/common.bend as SC

# Slot layout of a dynamic array: the first n slots are Some, the rest None.

def somes(-T: Data, xs: List<&2, Maybe<&2, T>>) -> List<&2, T>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{None{}, r}:
      somes(T, r)
    case Con{Some{x}, r}:
      Con{x, somes(T, r)}

def nones(-T: Data, xs: List<&2, Maybe<&2, T>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{None{}, r}:
      nones(T, r)
    case Con{Some{x}, r}:
      False{}

def lay(-T: Data, xs: List<&2, Maybe<&2, T>>, n: Nat) -> Bool:
  match xs n:
    case Nil{} 0n:
      True{}
    case Nil{} 1n+m:
      False{}
    case Con{None{}, r} 0n:
      nones(T, r)
    case Con{None{}, r} 1n+m:
      False{}
    case Con{Some{x}, r} 0n:
      False{}
    case Con{Some{x}, r} 1n+m:
      lay(T, r, m)

def nones_somes(-T: Data, +xs: List<&2, Maybe<&2, T>>, +h: {nones(T, xs) == True{} : Bool}) -> {somes(T, xs) == Nil{} : List<&2, T>}:
  match xs:
    case Nil{}:
      {==}
    case Con{None{}, +r}:
      nones_somes(T, r, h)
    case Con{Some{x}, r}:
      Empty.absurd({Con{x, somes(T, r)} == Nil{} : List<&2, T>}, L.false_true(h))

def lay_len(-T: Data, +xs: List<&2, Maybe<&2, T>>, +n: Nat, +h: {lay(T, xs, n) == True{} : Bool}) -> {SC.length(T, somes(T, xs)) == n : Nat}:
  match xs n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+m:
      Empty.absurd({0n == 1n+m : Nat}, L.false_true(h))
    case Con{None{}, +r} 0n:
      %Equal.sym(List<&2, T>, somes(T, r), Nil{}, nones_somes(T, r, h)) : {SC.length(T, _) == 0n : Nat}
      {==}
    case Con{None{}, r} 1n+m:
      Empty.absurd({SC.length(T, somes(T, r)) == 1n+m : Nat}, L.false_true(h))
    case Con{Some{x}, r} 0n:
      Empty.absurd({1n+SC.length(T, somes(T, r)) == 0n : Nat}, L.false_true(h))
    case Con{Some{x}, +r} 1n+m:
      N.succ_cong(SC.length(T, somes(T, r)), m, lay_len(T, r, m, h))

def lay_le(-T: Data, +xs: List<&2, Maybe<&2, T>>, +n: Nat, +h: {lay(T, xs, n) == True{} : Bool}) -> {Nat.is_le(n, SC.length(Maybe<&2, T>, xs)) == True{} : Bool}:
  match xs n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+m:
      Empty.absurd({Nat.is_le(1n+m, 0n) == True{} : Bool}, L.false_true(h))
    case Con{None{}, r} 0n:
      {==}
    case Con{None{}, r} 1n+m:
      Empty.absurd({Nat.is_le(1n+m, 1n+SC.length(Maybe<&2, T>, r)) == True{} : Bool}, L.false_true(h))
    case Con{Some{x}, r} 0n:
      {==}
    case Con{Some{x}, +r} 1n+m:
      lay_le(T, r, m, h)

def lay_nil_pos(-T: Data, +n: Nat, +i: Nat, +hi: {Nat.is_lt(i, n) == True{} : Bool}) -> {lay(T, Nil{}, n) == False{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({True{} == False{} : Bool}, N.lt_zero_absurd(i, hi))
    case 1n+m:
      {==}

# Slot i (< n) holds exactly the i-th item.
def lay_nth(-T: Data, +xs: List<&2, Maybe<&2, T>>, +n: Nat, +i: Nat, +h: {lay(T, xs, n) == True{} : Bool}, +hi: {Nat.is_lt(i, n) == True{} : Bool}) -> {SC.nth(Maybe<&2, T>, xs, i) == Some{SC.nth(T, somes(T, xs), i)} : Maybe<&2, Maybe<&2, T>>}:
  match xs n i:
    case Nil{} _ _:
      Empty.absurd({None{} == Some{None{}} : Maybe<&2, Maybe<&2, T>>}, L.true_not_false(lay(T, Nil{}, n), h, lay_nil_pos(T, n, i, hi)))
    case Con{None{}, r} 0n _:
      Empty.absurd({SC.nth(Maybe<&2, T>, Con{None{}, r}, i) == Some{SC.nth(T, somes(T, r), i)} : Maybe<&2, Maybe<&2, T>>}, N.lt_zero_absurd(i, hi))
    case Con{None{}, r} 1n+m _:
      Empty.absurd({SC.nth(Maybe<&2, T>, Con{None{}, r}, i) == Some{SC.nth(T, somes(T, r), i)} : Maybe<&2, Maybe<&2, T>>}, L.false_true(h))
    case Con{Some{x}, r} 0n _:
      Empty.absurd({SC.nth(Maybe<&2, T>, Con{Some{x}, r}, i) == Some{SC.nth(T, Con{x, somes(T, r)}, i)} : Maybe<&2, Maybe<&2, T>>}, L.false_true(h))
    case Con{Some{x}, r} 1n+m 0n:
      {==}
    case Con{Some{x}, +r} 1n+m 1n+j:
      lay_nth(T, r, m, j, h, hi)

def nones_nth(-T: Data, +xs: List<&2, Maybe<&2, T>>, +i: Nat, +h: {nones(T, xs) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.length(Maybe<&2, T>, xs)) == True{} : Bool}) -> {SC.nth(Maybe<&2, T>, xs, i) == Some{None{}} : Maybe<&2, Maybe<&2, T>>}:
  match xs i:
    case Nil{} _:
      Empty.absurd({None{} == Some{None{}} : Maybe<&2, Maybe<&2, T>>}, N.lt_zero_absurd(i, hi))
    case Con{None{}, r} 0n:
      {==}
    case Con{None{}, +r} 1n+j:
      nones_nth(T, r, j, h, hi)
    case Con{Some{x}, r} _:
      Empty.absurd({SC.nth(Maybe<&2, T>, Con{Some{x}, r}, i) == Some{None{}} : Maybe<&2, Maybe<&2, T>>}, L.false_true(h))

def nones_rep(-T: Data, +k: Nat) -> {nones(T, SC.replicate(Maybe<&2, T>, k, None{})) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      nones_rep(T, j)

def somes_rep(-T: Data, +k: Nat) -> {somes(T, SC.replicate(Maybe<&2, T>, k, None{})) == Nil{} : List<&2, T>}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      somes_rep(T, j)

def lay_rep(-T: Data, +k: Nat) -> {lay(T, SC.replicate(Maybe<&2, T>, k, None{}), 0n) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      nones_rep(T, j)

def nones_lay0(-T: Data, +xs: List<&2, Maybe<&2, T>>, +h: {nones(T, xs) == True{} : Bool}) -> {lay(T, xs, 0n) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{None{}, r}:
      h
    case Con{Some{x}, r}:
      h

def lay0_nones(-T: Data, +xs: List<&2, Maybe<&2, T>>, +h: {lay(T, xs, 0n) == True{} : Bool}) -> {nones(T, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{None{}, r}:
      h
    case Con{Some{x}, r}:
      h

def nones_append(-T: Data, +xs: List<&2, Maybe<&2, T>>, +ys: List<&2, Maybe<&2, T>>, +hx: {nones(T, xs) == True{} : Bool}, +hy: {nones(T, ys) == True{} : Bool}) -> {nones(T, SC.append(Maybe<&2, T>, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case Con{None{}, +r}:
      nones_append(T, r, ys, hx, hy)
    case Con{Some{x}, r}:
      hx

# ---- set ----

def lay_set(-T: Data, +xs: List<&2, Maybe<&2, T>>, +n: Nat, +i: Nat, +v: T, +h: {lay(T, xs, n) == True{} : Bool}, +hi: {Nat.is_lt(i, n) == True{} : Bool}) -> {lay(T, SC.update(Maybe<&2, T>, xs, i, Some{v}), n) == True{} : Bool}:
  match xs n i:
    case Nil{} _ _:
      Empty.absurd({lay(T, Nil{}, n) == True{} : Bool}, L.true_not_false(lay(T, Nil{}, n), h, lay_nil_pos(T, n, i, hi)))
    case Con{None{}, r} 0n _:
      Empty.absurd({lay(T, SC.update(Maybe<&2, T>, Con{None{}, r}, i, Some{v}), 0n) == True{} : Bool}, N.lt_zero_absurd(i, hi))
    case Con{None{}, r} 1n+m _:
      Empty.absurd({lay(T, SC.update(Maybe<&2, T>, Con{None{}, r}, i, Some{v}), 1n+m) == True{} : Bool}, L.false_true(h))
    case Con{Some{x}, r} 0n _:
      Empty.absurd({lay(T, SC.update(Maybe<&2, T>, Con{Some{x}, r}, i, Some{v}), 0n) == True{} : Bool}, L.false_true(h))
    case Con{Some{x}, r} 1n+m 0n:
      h
    case Con{Some{x}, +r} 1n+m 1n+j:
      lay_set(T, r, m, j, v, h, hi)

def somes_set(-T: Data, +xs: List<&2, Maybe<&2, T>>, +n: Nat, +i: Nat, +v: T, +h: {lay(T, xs, n) == True{} : Bool}, +hi: {Nat.is_lt(i, n) == True{} : Bool}) -> {somes(T, SC.update(Maybe<&2, T>, xs, i, Some{v})) == SC.update(T, somes(T, xs), i, v) : List<&2, T>}:
  match xs n i:
    case Nil{} _ _:
      Empty.absurd({Nil{} == Nil{} : List<&2, T>}, L.true_not_false(lay(T, Nil{}, n), h, lay_nil_pos(T, n, i, hi)))
    case Con{None{}, r} 0n _:
      Empty.absurd({somes(T, SC.update(Maybe<&2, T>, Con{None{}, r}, i, Some{v})) == SC.update(T, somes(T, r), i, v) : List<&2, T>}, N.lt_zero_absurd(i, hi))
    case Con{None{}, r} 1n+m _:
      Empty.absurd({somes(T, SC.update(Maybe<&2, T>, Con{None{}, r}, i, Some{v})) == SC.update(T, somes(T, r), i, v) : List<&2, T>}, L.false_true(h))
    case Con{Some{x}, r} 0n _:
      Empty.absurd({somes(T, SC.update(Maybe<&2, T>, Con{Some{x}, r}, i, Some{v})) == SC.update(T, Con{x, somes(T, r)}, i, v) : List<&2, T>}, L.false_true(h))
    case Con{Some{x}, r} 1n+m 0n:
      {==}
    case Con{Some{+x}, +r} 1n+m 1n+j:
      LL.cons_cong(T, x, somes(T, SC.update(Maybe<&2, T>, r, j, Some{v})), SC.update(T, somes(T, r), j, v), somes_set(T, r, m, j, v, h, hi))

# ---- push (slot n is the first free one) ----

def push_free(-T: Data, +xs: List<&2, Maybe<&2, T>>, +n: Nat, +h: {lay(T, xs, n) == True{} : Bool}, +hn: {Nat.is_lt(n, SC.length(Maybe<&2, T>, xs)) == True{} : Bool}) -> {SC.nth(Maybe<&2, T>, xs, n) == Some{None{}} : Maybe<&2, Maybe<&2, T>>}:
  match xs n:
    case Nil{} _:
      Empty.absurd({None{} == Some{None{}} : Maybe<&2, Maybe<&2, T>>}, N.lt_zero_absurd(n, hn))
    case Con{None{}, r} 0n:
      {==}
    case Con{None{}, r} 1n+m:
      Empty.absurd({SC.nth(Maybe<&2, T>, r, m) == Some{None{}} : Maybe<&2, Maybe<&2, T>>}, L.false_true(h))
    case Con{Some{x}, r} 0n:
      Empty.absurd({Some{Some{x}} == Some{None{}} : Maybe<&2, Maybe<&2, T>>}, L.false_true(h))
    case Con{Some{x}, +r} 1n+m:
      push_free(T, r, m, h, hn)

def lay_push(-T: Data, +xs: List<&2, Maybe<&2, T>>, +n: Nat, +v: T, +h: {lay(T, xs, n) == True{} : Bool}, +hn: {Nat.is_lt(n, SC.length(Maybe<&2, T>, xs)) == True{} : Bool}) -> {lay(T, SC.update(Maybe<&2, T>, xs, n, Some{v}), 1n+n) == True{} : Bool}:
  match xs n:
    case Nil{} _:
      Empty.absurd({lay(T, Nil{}, 1n+n) == True{} : Bool}, N.lt_zero_absurd(n, hn))
    case Con{None{}, +r} 0n:
      nones_lay0(T, r, h)
    case Con{None{}, r} 1n+m:
      Empty.absurd({lay(T, Con{None{}, SC.update(Maybe<&2, T>, r, m, Some{v})}, 2n+m) == True{} : Bool}, L.false_true(h))
    case Con{Some{x}, r} 0n:
      Empty.absurd({lay(T, Con{Some{v}, r}, 1n) == True{} : Bool}, L.false_true(h))
    case Con{Some{x}, +r} 1n+m:
      lay_push(T, r, m, v, h, hn)

def somes_push(-T: Data, +xs: List<&2, Maybe<&2, T>>, +n: Nat, +v: T, +h: {lay(T, xs, n) == True{} : Bool}, +hn: {Nat.is_lt(n, SC.length(Maybe<&2, T>, xs)) == True{} : Bool}) -> {somes(T, SC.update(Maybe<&2, T>, xs, n, Some{v})) == SC.snoc(T, somes(T, xs), v) : List<&2, T>}:
  match xs n:
    case Nil{} _:
      Empty.absurd({Nil{} == Con{v, Nil{}} : List<&2, T>}, N.lt_zero_absurd(n, hn))
    case Con{None{}, +r} 0n:
      %Equal.sym(List<&2, T>, somes(T, r), Nil{}, nones_somes(T, r, h)) : {Con{v, _} == SC.snoc(T, _, v) : List<&2, T>}
      {==}
    case Con{None{}, r} 1n+m:
      Empty.absurd({somes(T, Con{None{}, SC.update(Maybe<&2, T>, r, m, Some{v})}) == SC.snoc(T, somes(T, r), v) : List<&2, T>}, L.false_true(h))
    case Con{Some{x}, r} 0n:
      Empty.absurd({Con{v, somes(T, r)} == SC.snoc(T, Con{x, somes(T, r)}, v) : List<&2, T>}, L.false_true(h))
    case Con{Some{+x}, +r} 1n+m:
      LL.cons_cong(T, x, somes(T, SC.update(Maybe<&2, T>, r, m, Some{v})), SC.snoc(T, somes(T, r), v), somes_push(T, r, m, v, h, hn))

# ---- pop (slot m of a layout with m+1 items) ----

def lay_pop(-T: Data, +xs: List<&2, Maybe<&2, T>>, +m: Nat, +h: {lay(T, xs, 1n+m) == True{} : Bool}) -> {lay(T, SC.update(Maybe<&2, T>, xs, m, None{}), m) == True{} : Bool}:
  match xs m:
    case Nil{} _:
      Empty.absurd({lay(T, Nil{}, m) == True{} : Bool}, L.false_true(h))
    case Con{None{}, r} _:
      Empty.absurd({lay(T, SC.update(Maybe<&2, T>, Con{None{}, r}, m, None{}), m) == True{} : Bool}, L.false_true(h))
    case Con{Some{x}, +r} 0n:
      lay0_nones(T, r, h)
    case Con{Some{x}, +r} 1n+k:
      lay_pop(T, r, k, h)

def init_cons(-T: Data, +x: T, +ys: List<&2, T>, +k: Nat, +h: {SC.length(T, ys) == 1n+k : Nat}) -> {SC.init(T, Con{x, ys}) == Con{x, SC.init(T, ys)} : List<&2, T>}:
  match ys:
    case Nil{}:
      Empty.absurd({Nil{} == Con{x, Nil{}} : List<&2, T>}, N.zero_succ(k, h))
    case Con{y, t}:
      {==}

def somes_pop(-T: Data, +xs: List<&2, Maybe<&2, T>>, +m: Nat, +h: {lay(T, xs, 1n+m) == True{} : Bool}) -> {somes(T, SC.update(Maybe<&2, T>, xs, m, None{})) == SC.init(T, somes(T, xs)) : List<&2, T>}:
  match xs m:
    case Nil{} _:
      Empty.absurd({Nil{} == Nil{} : List<&2, T>}, L.false_true(h))
    case Con{None{}, r} _:
      Empty.absurd({somes(T, SC.update(Maybe<&2, T>, Con{None{}, r}, m, None{})) == SC.init(T, somes(T, r)) : List<&2, T>}, L.false_true(h))
    case Con{Some{x}, +r} 0n:
      %Equal.sym(List<&2, T>, somes(T, r), Nil{}, nones_somes(T, r, lay0_nones(T, r, h))) : {_ == SC.init(T, Con{x, _}) : List<&2, T>}
      {==}
    case Con{Some{+x}, +r} 1n+k:
      Equal.trans(List<&2, T>, Con{x, somes(T, SC.update(Maybe<&2, T>, r, k, None{}))}, Con{x, SC.init(T, somes(T, r))}, SC.init(T, Con{x, somes(T, r)}),
        LL.cons_cong(T, x, somes(T, SC.update(Maybe<&2, T>, r, k, None{})), SC.init(T, somes(T, r)), somes_pop(T, r, k, h)),
        Equal.sym(List<&2, T>, SC.init(T, Con{x, somes(T, r)}), Con{x, SC.init(T, somes(T, r))}, init_cons(T, x, somes(T, r), k, lay_len(T, r, 1n+k, h))))

# nth at the last position is last.
def nth_last(-T: Data, +ys: List<&2, T>, +m: Nat, +h: {SC.length(T, ys) == 1n+m : Nat}) -> {SC.nth(T, ys, m) == SC.last(T, ys) : Maybe<&2, T>}:
  match ys m:
    case Nil{} _:
      Empty.absurd({None{} == None{} : Maybe<&2, T>}, N.zero_succ(m, h))
    case Con{y, Nil{}} 0n:
      {==}
    case Con{y, Con{y2, t2}} 0n:
      Empty.absurd({Some{y} == SC.last(T, Con{y2, t2}) : Maybe<&2, T>}, N.succ_zero(SC.length(T, t2), N.succ_inj(1n+SC.length(T, t2), 0n, h)))
    case Con{y, Nil{}} 1n+k:
      Empty.absurd({SC.nth(T, Nil{}, k) == Some{y} : Maybe<&2, T>}, N.zero_succ(k, N.succ_inj(0n, 1n+k, h)))
    case Con{y, Con{+y2, +t2}} 1n+k:
      nth_last(T, Con{y2, t2}, k, N.succ_inj(1n+SC.length(T, t2), 1n+k, h))

# ---- growth (append free slots) and clear ----

def lay_grow(-T: Data, +xs: List<&2, Maybe<&2, T>>, +n: Nat, +k: Nat, +h: {lay(T, xs, n) == True{} : Bool}) -> {lay(T, SC.append(Maybe<&2, T>, xs, SC.replicate(Maybe<&2, T>, k, None{})), n) == True{} : Bool}:
  match xs n:
    case Nil{} 0n:
      lay_rep(T, k)
    case Nil{} 1n+m:
      Empty.absurd({lay(T, SC.replicate(Maybe<&2, T>, k, None{}), 1n+m) == True{} : Bool}, L.false_true(h))
    case Con{None{}, +r} 0n:
      nones_append(T, r, SC.replicate(Maybe<&2, T>, k, None{}), h, nones_rep(T, k))
    case Con{None{}, r} 1n+m:
      h
    case Con{Some{x}, r} 0n:
      h
    case Con{Some{x}, +r} 1n+m:
      lay_grow(T, r, m, k, h)

def somes_grow(-T: Data, +xs: List<&2, Maybe<&2, T>>, +k: Nat) -> {somes(T, SC.append(Maybe<&2, T>, xs, SC.replicate(Maybe<&2, T>, k, None{}))) == somes(T, xs) : List<&2, T>}:
  match xs:
    case Nil{}:
      somes_rep(T, k)
    case Con{None{}, +r}:
      somes_grow(T, r, k)
    case Con{Some{+x}, +r}:
      LL.cons_cong(T, x, somes(T, SC.append(Maybe<&2, T>, r, SC.replicate(Maybe<&2, T>, k, None{}))), somes(T, r), somes_grow(T, r, k))
