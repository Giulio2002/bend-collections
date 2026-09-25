import Base
import ./nat.bend as N
import ./list.bend as LL
import ../../spec/lib/common.bend as SC
import ../../src/containers/deque.bend as D

# List facts for the two-list deque and queue: splitting a back list for a
# rebalance, and the halving bound that keeps the moved half nonempty.

def zero_sub(+k: Nat) -> {Nat.sub(0n, k) == 0n : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      {==}

def take_drop(-T: Data, +xs: List<&2, T>, +k: Nat) -> {SC.append(T, SC.take(T, xs, k), SC.drop(T, xs, k)) == xs : List<&2, T>}:
  match xs k:
    case Nil{} _:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+p:
      LL.cons_cong(T, h, SC.append(T, SC.take(T, t, p), SC.drop(T, t, p)), t, take_drop(T, t, p))

def len_drop(-T: Data, +xs: List<&2, T>, +k: Nat) -> {SC.length(T, SC.drop(T, xs, k)) == Nat.sub(SC.length(T, xs), k) : Nat}:
  match xs k:
    case Nil{} _:
      Equal.sym(Nat, Nat.sub(0n, k), 0n, zero_sub(k))
    case Con{h, t} 0n:
      Equal.sym(Nat, Nat.sub(1n+SC.length(T, t), 0n), 1n+SC.length(T, t), N.sub_zero(1n+SC.length(T, t)))
    case Con{h, t} 1n+p:
      len_drop(T, t, p)

# the deque's split keeps the first n and reverses the rest
def split_eq(~T: Data, +n: Nat, +xs: List<&2, T>) -> {D.split(~T, n, xs) == (SC.take(T, xs, n), SC.reverse(T, SC.drop(T, xs, n))) : List<&2, T> & List<&2, T>}:
  match n xs:
    case 0n Nil{}:
      {==}
    case 0n Con{h, t}:
      Equal.cong(List<&2, T>, List<&2, T> & List<&2, T>, r => (Nil{}, r), List.reverse(&2, T, Con{h, t}), SC.reverse(T, Con{h, t}), LL.base_rev(T, Con{h, t}))
    case 1n+p Nil{}:
      {==}
    case 1n+p Con{x, t}:
      Equal.cong(List<&2, T> & List<&2, T>, List<&2, T> & List<&2, T>, r => D.split_cons(~T, x, r), D.split(~T, p, t), (SC.take(T, t, p), SC.reverse(T, SC.drop(T, t, p))), split_eq(~T, p, t))

# half of a nonempty length is below it
def half_le(+n: Nat) -> {Nat.is_le(Nat.div(1n+n, 2n), n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+0n:
      {==}
    case 1n+1n+k:
      %Equal.sym(Nat, Nat.div(Nat.add(2n, 1n+k), 2n), 1n+Nat.div(1n+k, 2n), N.div2_step(1n+k)) : {Nat.is_le(_, 2n+k) == True{} : Bool}
      N.le_trans(1n+Nat.div(1n+k, 2n), 1n+k, 2n+k, half_le(k), N.le_succ(1n+k))

def len_take(-T: Data, +xs: List<&2, T>, +n: Nat, +h: {Nat.is_le(n, SC.length(T, xs)) == True{} : Bool}) -> {SC.length(T, SC.take(T, xs, n)) == n : Nat}:
  LL.sc_length_take(T, xs, n, h)

def len_rev(-T: Data, +xs: List<&2, T>) -> {SC.length(T, SC.reverse(T, xs)) == SC.length(T, xs) : Nat}:
  LL.length_rev(T, xs)
