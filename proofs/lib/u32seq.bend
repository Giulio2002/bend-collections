import Base
import ./logic.bend as L
import ./nat.bend as N
import ./list.bend as LL
import ./u32.bend as U
import ./u32alg.bend as UA
import ../spec/common.bend as SC
import ../spec/u32seq.bend as Q

# Wrapping sums of U32 sequences and point additions (addat).

def addat(xs: List<&2, U32>, +i: Nat, +v: U32) -> List<&2, U32>:
  match xs i:
    case Nil{} _:
      Nil{}
    case Con{h, t} 0n:
      Con{U32.add(h, v), t}
    case Con{h, t} 1n+j:
      Con{h, addat(t, j, v)}

def sum_append(+xs: List<&2, U32>, +ys: List<&2, U32>) -> {Q.sum(SC.append(U32, xs, ys)) == U32.add(Q.sum(xs), Q.sum(ys)) : U32}:
  match xs:
    case Nil{}:
      Equal.sym(U32, U32.add(0, Q.sum(ys)), Q.sum(ys), UA.zero_add(Q.sum(ys)))
    case Con{h, t}:
      %Equal.sym(U32, Q.sum(SC.append(U32, t, ys)), U32.add(Q.sum(t), Q.sum(ys)), sum_append(t, ys)) : {U32.add(h, _) == U32.add(U32.add(h, Q.sum(t)), Q.sum(ys)) : U32}
      Equal.sym(U32, U32.add(U32.add(h, Q.sum(t)), Q.sum(ys)), U32.add(h, U32.add(Q.sum(t), Q.sum(ys))), UA.assoc(h, Q.sum(t), Q.sum(ys)))

def sum_zeros(+n: Nat) -> {Q.sum(Q.zeros(n)) == 0 : U32}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      %Equal.sym(U32, Q.sum(Q.zeros(k)), 0, sum_zeros(k)) : {U32.add(0, _) == 0 : U32}
      UA.zero_add(0)

def length_addat(+xs: List<&2, U32>, +i: Nat, +v: U32) -> {SC.length(U32, addat(xs, i, v)) == SC.length(U32, xs) : Nat}:
  match xs i:
    case Nil{} _:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+j:
      N.succ_cong(SC.length(U32, addat(t, j, v)), SC.length(U32, t), length_addat(t, j, v))

# Adding v at an index below the length adds v to the sum.
def sum_addat(+xs: List<&2, U32>, +i: Nat, +v: U32, +h: {Nat.is_lt(i, SC.length(U32, xs)) == True{} : Bool}) -> {Q.sum(addat(xs, i, v)) == U32.add(Q.sum(xs), v) : U32}:
  match xs i:
    case Nil{} _:
      Empty.absurd({0 == U32.add(0, v) : U32}, N.lt_zero_absurd(i, h))
    case Con{x, t} 0n:
      %Equal.sym(U32, U32.add(U32.add(x, v), Q.sum(t)), U32.add(x, U32.add(v, Q.sum(t))), UA.assoc(x, v, Q.sum(t))) : {_ == U32.add(U32.add(x, Q.sum(t)), v) : U32}
      %Equal.sym(U32, U32.add(U32.add(x, Q.sum(t)), v), U32.add(x, U32.add(Q.sum(t), v)), UA.assoc(x, Q.sum(t), v)) : {U32.add(x, U32.add(v, Q.sum(t))) == _ : U32}
      %U32.add_comm(v, Q.sum(t)) : {U32.add(x, U32.add(v, Q.sum(t))) == U32.add(x, _) : U32}
      {==}
    case Con{x, t} 1n+j:
      %Equal.sym(U32, Q.sum(addat(t, j, v)), U32.add(Q.sum(t), v), sum_addat(t, j, v, h)) : {U32.add(x, _) == U32.add(U32.add(x, Q.sum(t)), v) : U32}
      Equal.sym(U32, U32.add(U32.add(x, Q.sum(t)), v), U32.add(x, U32.add(Q.sum(t), v)), UA.assoc(x, Q.sum(t), v))

def addat_left(+xs: List<&2, U32>, +ys: List<&2, U32>, +i: Nat, +v: U32, +h: {Nat.is_lt(i, SC.length(U32, xs)) == True{} : Bool}) -> {addat(SC.append(U32, xs, ys), i, v) == SC.append(U32, addat(xs, i, v), ys) : List<&2, U32>}:
  match xs i:
    case Nil{} _:
      Empty.absurd({addat(ys, i, v) == ys : List<&2, U32>}, N.lt_zero_absurd(i, h))
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+j:
      LL.cons_cong(U32, x, addat(SC.append(U32, t, ys), j, v), SC.append(U32, addat(t, j, v), ys), addat_left(t, ys, j, v, h))

def addat_right(+xs: List<&2, U32>, +ys: List<&2, U32>, +i: Nat, +v: U32, +h: {Nat.is_le(SC.length(U32, xs), i) == True{} : Bool}) -> {addat(SC.append(U32, xs, ys), i, v) == SC.append(U32, xs, addat(ys, Nat.sub(i, SC.length(U32, xs)), v)) : List<&2, U32>}:
  match xs i:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+j:
      {==}
    case Con{x, t} 0n:
      Empty.absurd({addat(SC.append(U32, Con{x, t}, ys), 0n, v) == SC.append(U32, Con{x, t}, addat(ys, Nat.sub(0n, 1n+SC.length(U32, t)), v)) : List<&2, U32>}, L.false_true(h))
    case Con{x, t} 1n+j:
      LL.cons_cong(U32, x, addat(SC.append(U32, t, ys), j, v), SC.append(U32, t, addat(ys, Nat.sub(j, SC.length(U32, t)), v)), addat_right(t, ys, j, v, h))

def take_addat(+xs: List<&2, U32>, +i: Nat, +v: U32, +n: Nat) -> {SC.take(U32, addat(xs, i, v), n) == addat(SC.take(U32, xs, n), i, v) : List<&2, U32>}:
  match xs i n:
    case Nil{} _ _:
      {==}
    case Con{x, t} 0n 0n:
      {==}
    case Con{x, t} 1n+j 0n:
      {==}
    case Con{x, t} 0n 1n+m:
      {==}
    case Con{x, t} 1n+j 1n+m:
      LL.cons_cong(U32, x, SC.take(U32, addat(t, j, v), m), addat(SC.take(U32, t, m), j, v), take_addat(t, j, v, m))

# The spec's "update index i with (old + v)" is addat.
def update_addat(+xs: List<&2, U32>, +i: Nat, +y: U32, +v: U32, +e: {SC.nth(U32, xs, i) == Some{y} : Maybe<&2, U32>}) -> {SC.update(U32, xs, i, U32.add(y, v)) == addat(xs, i, v) : List<&2, U32>}:
  match xs i:
    case Nil{} _:
      Empty.absurd({Nil{} == Nil{} : List<&2, U32>}, L.none_some(U32, y, e))
    case Con{x, t} 0n:
      %L.some_inj(U32, x, y, e) : {Con{U32.add(_, v), t} == Con{U32.add(x, v), t} : List<&2, U32>}
      {==}
    case Con{x, t} 1n+j:
      LL.cons_cong(U32, x, SC.update(U32, t, j, U32.add(y, v)), addat(t, j, v), update_addat(t, j, y, v, e))

# sum of the slice [l, r) is the difference of prefix sums
def sum_slice(+xs: List<&2, U32>, +l: Nat, +r: Nat, +h: {Nat.is_le(l, r) == True{} : Bool}) -> {U32.sub(Q.sum(SC.take(U32, xs, r)), Q.sum(SC.take(U32, xs, l))) == Q.sum(Q.slice(xs, l, r)) : U32}:
  %Equal.sym(List<&2, U32>, SC.take(U32, xs, r), SC.append(U32, SC.take(U32, xs, l), SC.take(U32, SC.drop(U32, xs, l), Nat.sub(r, l))), LL.sc_take_split(U32, xs, l, r, h)) : {U32.sub(Q.sum(_), Q.sum(SC.take(U32, xs, l))) == Q.sum(Q.slice(xs, l, r)) : U32}
  %Equal.sym(U32, Q.sum(SC.append(U32, SC.take(U32, xs, l), Q.slice(xs, l, r))), U32.add(Q.sum(SC.take(U32, xs, l)), Q.sum(Q.slice(xs, l, r))), sum_append(SC.take(U32, xs, l), Q.slice(xs, l, r))) : {U32.sub(_, Q.sum(SC.take(U32, xs, l))) == Q.sum(Q.slice(xs, l, r)) : U32}
  UA.add_sub(Q.sum(SC.take(U32, xs, l)), Q.sum(Q.slice(xs, l, r)))

# slicing the first n values equals slicing the whole list when r <= n
def sub_le_mono(+l: Nat, +r: Nat, +n: Nat, +h: {Nat.is_le(r, n) == True{} : Bool}) -> {Nat.is_le(Nat.sub(r, l), Nat.sub(n, l)) == True{} : Bool}:
  match l r n:
    case 0n _ _:
      %Equal.sym(Nat, Nat.sub(r, 0n), r, N.sub_zero(r)) : {Nat.is_le(_, Nat.sub(n, 0n)) == True{} : Bool}
      %Equal.sym(Nat, Nat.sub(n, 0n), n, N.sub_zero(n)) : {Nat.is_le(r, _) == True{} : Bool}
      h
    case 1n+k 0n _:
      N.zero_le(Nat.sub(n, 1n+k))
    case 1n+k 1n+s 0n:
      Empty.absurd({Nat.is_le(Nat.sub(s, k), 0n) == True{} : Bool}, L.false_true(h))
    case 1n+k 1n+s 1n+m:
      sub_le_mono(k, s, m, h)

def slice_take(+xs: List<&2, U32>, +n: Nat, +l: Nat, +r: Nat, +h: {Nat.is_le(r, n) == True{} : Bool}, +hl: {Nat.is_le(l, r) == True{} : Bool}) -> {Q.slice(SC.take(U32, xs, n), l, r) == Q.slice(xs, l, r) : List<&2, U32>}:
  %Equal.sym(List<&2, U32>, SC.drop(U32, SC.take(U32, xs, n), l), SC.take(U32, SC.drop(U32, xs, l), Nat.sub(n, l)), LL.sc_drop_take(U32, xs, n, l)) : {SC.take(U32, _, Nat.sub(r, l)) == Q.slice(xs, l, r) : List<&2, U32>}
  LL.sc_take_take(U32, SC.drop(U32, xs, l), Nat.sub(n, l), Nat.sub(r, l), sub_le_mono(l, r, n, h))
