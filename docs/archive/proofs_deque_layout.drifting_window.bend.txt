import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../../spec/common.bend as SC
import ../dynamic_array/layout.bend as LY

# Slot layout of a deque: the elements occupy the window [lo, lo + n) of the
# slot list, every slot outside it is None.
#
#   win(xs, lo, n)  =  the first lo slots are None and LY.lay holds from
#                      there: n Somes, then only Nones.
#
# `LY.somes(xs)` (the values of the Some slots, in slot order) is therefore
# exactly the sequence the deque denotes, and every lemma below reduces the
# window at offset lo to the dynamic array's lemmas at offset 0.

def none_and(-T: Data, h: Maybe<&2, T>, b: Bool) -> Bool:
  match h:
    case None{}:
      b
    case Some{x}:
      False{}

def win(-T: Data, xs: List<&2, Maybe<&2, T>>, lo: Nat, n: Nat) -> Bool:
  match xs lo:
    case Nil{} 0n:
      LY.lay(T, Nil{}, n)
    case Con{h, r} 0n:
      LY.lay(T, Con{h, r}, n)
    case Nil{} 1n+k:
      False{}
    case Con{h, r} 1n+k:
      none_and(T, h, win(T, r, k, n))

# ---- basic projections ----

def win_lay(-T: Data, +xs: List<&2, Maybe<&2, T>>, +n: Nat, +h: {win(T, xs, 0n, n) == True{} : Bool}) -> {LY.lay(T, xs, n) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case Con{h2, r}:
      h

def lay_win(-T: Data, +xs: List<&2, Maybe<&2, T>>, +n: Nat, +h: {LY.lay(T, xs, n) == True{} : Bool}) -> {win(T, xs, 0n, n) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case Con{h2, r}:
      h

def win_len(-T: Data, +xs: List<&2, Maybe<&2, T>>, +lo: Nat, +n: Nat, +h: {win(T, xs, lo, n) == True{} : Bool}) -> {SC.length(T, LY.somes(T, xs)) == n : Nat}:
  match xs lo:
    case Nil{} 0n:
      LY.lay_len(T, Nil{}, n, h)
    case Con{h2, r} 0n:
      LY.lay_len(T, Con{h2, r}, n, h)
    case Nil{} 1n+k:
      Empty.absurd({0n == n : Nat}, L.false_true(h))
    case Con{None{}, +r} 1n+k:
      win_len(T, r, k, n, h)
    case Con{Some{x}, r} 1n+k:
      Empty.absurd({1n+SC.length(T, LY.somes(T, r)) == n : Nat}, L.false_true(h))

def win_le(-T: Data, +xs: List<&2, Maybe<&2, T>>, +lo: Nat, +n: Nat, +h: {win(T, xs, lo, n) == True{} : Bool}) -> {Nat.is_le(Nat.add(lo, n), SC.length(Maybe<&2, T>, xs)) == True{} : Bool}:
  match xs lo:
    case Nil{} 0n:
      LY.lay_le(T, Nil{}, n, h)
    case Con{h2, r} 0n:
      LY.lay_le(T, Con{h2, r}, n, h)
    case Nil{} 1n+k:
      Empty.absurd({Nat.is_le(Nat.add(1n+k, n), 0n) == True{} : Bool}, L.false_true(h))
    case Con{None{}, +r} 1n+k:
      win_le(T, r, k, n, h)
    case Con{Some{x}, r} 1n+k:
      Empty.absurd({Nat.is_le(Nat.add(1n+k, n), 1n+SC.length(Maybe<&2, T>, r)) == True{} : Bool}, L.false_true(h))

# Slot lo + i holds exactly the i-th element.
def win_nth(-T: Data, +xs: List<&2, Maybe<&2, T>>, +lo: Nat, +n: Nat, +i: Nat, +h: {win(T, xs, lo, n) == True{} : Bool}, +hi: {Nat.is_lt(i, n) == True{} : Bool}) -> {SC.nth(Maybe<&2, T>, xs, Nat.add(lo, i)) == Some{SC.nth(T, LY.somes(T, xs), i)} : Maybe<&2, Maybe<&2, T>>}:
  match xs lo:
    case Nil{} 0n:
      LY.lay_nth(T, Nil{}, n, i, h, hi)
    case Con{h2, r} 0n:
      LY.lay_nth(T, Con{h2, r}, n, i, h, hi)
    case Nil{} 1n+k:
      Empty.absurd({None{} == Some{None{}} : Maybe<&2, Maybe<&2, T>>}, L.false_true(h))
    case Con{None{}, +r} 1n+k:
      win_nth(T, r, k, n, i, h, hi)
    case Con{Some{x}, r} 1n+k:
      Empty.absurd({SC.nth(Maybe<&2, T>, r, Nat.add(k, i)) == Some{SC.nth(T, Con{x, LY.somes(T, r)}, i)} : Maybe<&2, Maybe<&2, T>>}, L.false_true(h))

# ---- push_back: the free slot lo + n ----

def win_free(-T: Data, +xs: List<&2, Maybe<&2, T>>, +lo: Nat, +n: Nat, +h: {win(T, xs, lo, n) == True{} : Bool}, +hn: {Nat.is_lt(Nat.add(lo, n), SC.length(Maybe<&2, T>, xs)) == True{} : Bool}) -> {SC.nth(Maybe<&2, T>, xs, Nat.add(lo, n)) == Some{None{}} : Maybe<&2, Maybe<&2, T>>}:
  match xs lo:
    case Nil{} 0n:
      LY.push_free(T, Nil{}, n, h, hn)
    case Con{h2, r} 0n:
      LY.push_free(T, Con{h2, r}, n, h, hn)
    case Nil{} 1n+k:
      Empty.absurd({None{} == Some{None{}} : Maybe<&2, Maybe<&2, T>>}, L.false_true(h))
    case Con{None{}, +r} 1n+k:
      win_free(T, r, k, n, h, hn)
    case Con{Some{x}, r} 1n+k:
      Empty.absurd({SC.nth(Maybe<&2, T>, r, Nat.add(k, n)) == Some{None{}} : Maybe<&2, Maybe<&2, T>>}, L.false_true(h))

def win_push_back(-T: Data, +xs: List<&2, Maybe<&2, T>>, +lo: Nat, +n: Nat, +v: T, +h: {win(T, xs, lo, n) == True{} : Bool}, +hn: {Nat.is_lt(Nat.add(lo, n), SC.length(Maybe<&2, T>, xs)) == True{} : Bool}) -> {win(T, SC.update(Maybe<&2, T>, xs, Nat.add(lo, n), Some{v}), lo, 1n+n) == True{} : Bool}:
  match xs lo:
    case Nil{} 0n:
      lay_win(T, SC.update(Maybe<&2, T>, Nil{}, n, Some{v}), 1n+n, LY.lay_push(T, Nil{}, n, v, h, hn))
    case Con{h2, +r} 0n:
      lay_win(T, SC.update(Maybe<&2, T>, Con{h2, r}, n, Some{v}), 1n+n, LY.lay_push(T, Con{h2, r}, n, v, h, hn))
    case Nil{} 1n+k:
      Empty.absurd({win(T, Nil{}, 1n+k, 1n+n) == True{} : Bool}, L.false_true(h))
    case Con{None{}, +r} 1n+k:
      win_push_back(T, r, k, n, v, h, hn)
    case Con{Some{x}, r} 1n+k:
      Empty.absurd({win(T, SC.update(Maybe<&2, T>, Con{Some{x}, r}, Nat.add(1n+k, n), Some{v}), 1n+k, 1n+n) == True{} : Bool}, L.false_true(h))

def somes_push_back(-T: Data, +xs: List<&2, Maybe<&2, T>>, +lo: Nat, +n: Nat, +v: T, +h: {win(T, xs, lo, n) == True{} : Bool}, +hn: {Nat.is_lt(Nat.add(lo, n), SC.length(Maybe<&2, T>, xs)) == True{} : Bool}) -> {LY.somes(T, SC.update(Maybe<&2, T>, xs, Nat.add(lo, n), Some{v})) == SC.snoc(T, LY.somes(T, xs), v) : List<&2, T>}:
  match xs lo:
    case Nil{} 0n:
      LY.somes_push(T, Nil{}, n, v, h, hn)
    case Con{h2, +r} 0n:
      LY.somes_push(T, Con{h2, r}, n, v, h, hn)
    case Nil{} 1n+k:
      Empty.absurd({Nil{} == Con{v, Nil{}} : List<&2, T>}, L.false_true(h))
    case Con{None{}, +r} 1n+k:
      somes_push_back(T, r, k, n, v, h, hn)
    case Con{Some{x}, r} 1n+k:
      Empty.absurd({LY.somes(T, SC.update(Maybe<&2, T>, Con{Some{x}, r}, Nat.add(1n+k, n), Some{v})) == SC.snoc(T, Con{x, LY.somes(T, r)}, v) : List<&2, T>}, L.false_true(h))

# ---- push_front: the free slot lo - 1 ----

def win_push_front(-T: Data, +xs: List<&2, Maybe<&2, T>>, +k: Nat, +n: Nat, +v: T, +h: {win(T, xs, 1n+k, n) == True{} : Bool}) -> {win(T, SC.update(Maybe<&2, T>, xs, k, Some{v}), k, 1n+n) == True{} : Bool}:
  match xs k:
    case Nil{} 0n:
      Empty.absurd({win(T, Nil{}, 0n, 1n+n) == True{} : Bool}, L.false_true(h))
    case Con{None{}, +r} 0n:
      lay_win(T, Con{Some{v}, r}, 1n+n, win_lay(T, r, n, h))
    case Con{Some{x}, r} 0n:
      Empty.absurd({win(T, Con{Some{v}, r}, 0n, 1n+n) == True{} : Bool}, L.false_true(h))
    case Nil{} 1n+j:
      Empty.absurd({win(T, Nil{}, 1n+j, 1n+n) == True{} : Bool}, L.false_true(h))
    case Con{None{}, +r} 1n+j:
      win_push_front(T, r, j, n, v, h)
    case Con{Some{x}, r} 1n+j:
      Empty.absurd({win(T, SC.update(Maybe<&2, T>, Con{Some{x}, r}, 1n+j, Some{v}), 1n+j, 1n+n) == True{} : Bool}, L.false_true(h))

def somes_push_front(-T: Data, +xs: List<&2, Maybe<&2, T>>, +k: Nat, +n: Nat, +v: T, +h: {win(T, xs, 1n+k, n) == True{} : Bool}) -> {LY.somes(T, SC.update(Maybe<&2, T>, xs, k, Some{v})) == Con{v, LY.somes(T, xs)} : List<&2, T>}:
  match xs k:
    case Nil{} 0n:
      Empty.absurd({Nil{} == Con{v, Nil{}} : List<&2, T>}, L.false_true(h))
    case Con{None{}, r} 0n:
      {==}
    case Con{Some{x}, r} 0n:
      Empty.absurd({Con{v, LY.somes(T, r)} == Con{v, Con{x, LY.somes(T, r)}} : List<&2, T>}, L.false_true(h))
    case Nil{} 1n+j:
      Empty.absurd({Nil{} == Con{v, Nil{}} : List<&2, T>}, L.false_true(h))
    case Con{None{}, +r} 1n+j:
      somes_push_front(T, r, j, n, v, h)
    case Con{Some{x}, r} 1n+j:
      Empty.absurd({LY.somes(T, SC.update(Maybe<&2, T>, Con{Some{x}, r}, 1n+j, Some{v})) == Con{v, Con{x, LY.somes(T, r)}} : List<&2, T>}, L.false_true(h))

# ---- pop_front: slot lo ----

def win_pop_front(-T: Data, +xs: List<&2, Maybe<&2, T>>, +lo: Nat, +m: Nat, +h: {win(T, xs, lo, 1n+m) == True{} : Bool}) -> {win(T, SC.update(Maybe<&2, T>, xs, lo, None{}), 1n+lo, m) == True{} : Bool}:
  match xs lo:
    case Nil{} 0n:
      Empty.absurd({win(T, Nil{}, 1n, m) == True{} : Bool}, L.false_true(h))
    case Con{None{}, r} 0n:
      Empty.absurd({win(T, Con{None{}, r}, 1n, m) == True{} : Bool}, L.false_true(h))
    case Con{Some{x}, +r} 0n:
      lay_win(T, r, m, h)
    case Nil{} 1n+k:
      Empty.absurd({win(T, Nil{}, 2n+k, m) == True{} : Bool}, L.false_true(h))
    case Con{None{}, +r} 1n+k:
      win_pop_front(T, r, k, m, h)
    case Con{Some{x}, r} 1n+k:
      Empty.absurd({win(T, SC.update(Maybe<&2, T>, Con{Some{x}, r}, 1n+k, None{}), 2n+k, m) == True{} : Bool}, L.false_true(h))

def somes_pop_front(-T: Data, +xs: List<&2, Maybe<&2, T>>, +lo: Nat, +m: Nat, +h: {win(T, xs, lo, 1n+m) == True{} : Bool}) -> {LY.somes(T, SC.update(Maybe<&2, T>, xs, lo, None{})) == SC.tail(T, LY.somes(T, xs)) : List<&2, T>}:
  match xs lo:
    case Nil{} 0n:
      Empty.absurd({Nil{} == Nil{} : List<&2, T>}, L.false_true(h))
    case Con{None{}, r} 0n:
      Empty.absurd({LY.somes(T, r) == SC.tail(T, LY.somes(T, r)) : List<&2, T>}, L.false_true(h))
    case Con{Some{x}, r} 0n:
      {==}
    case Nil{} 1n+k:
      Empty.absurd({Nil{} == Nil{} : List<&2, T>}, L.false_true(h))
    case Con{None{}, +r} 1n+k:
      somes_pop_front(T, r, k, m, h)
    case Con{Some{x}, r} 1n+k:
      Empty.absurd({LY.somes(T, SC.update(Maybe<&2, T>, Con{Some{x}, r}, 1n+k, None{})) == SC.tail(T, Con{x, LY.somes(T, r)}) : List<&2, T>}, L.false_true(h))

# ---- pop_back: slot lo + m ----

def win_pop_back(-T: Data, +xs: List<&2, Maybe<&2, T>>, +lo: Nat, +m: Nat, +h: {win(T, xs, lo, 1n+m) == True{} : Bool}) -> {win(T, SC.update(Maybe<&2, T>, xs, Nat.add(lo, m), None{}), lo, m) == True{} : Bool}:
  match xs lo:
    case Nil{} 0n:
      lay_win(T, SC.update(Maybe<&2, T>, Nil{}, m, None{}), m, LY.lay_pop(T, Nil{}, m, h))
    case Con{h2, +r} 0n:
      lay_win(T, SC.update(Maybe<&2, T>, Con{h2, r}, m, None{}), m, LY.lay_pop(T, Con{h2, r}, m, h))
    case Nil{} 1n+k:
      Empty.absurd({win(T, Nil{}, 1n+k, m) == True{} : Bool}, L.false_true(h))
    case Con{None{}, +r} 1n+k:
      win_pop_back(T, r, k, m, h)
    case Con{Some{x}, r} 1n+k:
      Empty.absurd({win(T, SC.update(Maybe<&2, T>, Con{Some{x}, r}, Nat.add(1n+k, m), None{}), 1n+k, m) == True{} : Bool}, L.false_true(h))

def somes_pop_back(-T: Data, +xs: List<&2, Maybe<&2, T>>, +lo: Nat, +m: Nat, +h: {win(T, xs, lo, 1n+m) == True{} : Bool}) -> {LY.somes(T, SC.update(Maybe<&2, T>, xs, Nat.add(lo, m), None{})) == SC.init(T, LY.somes(T, xs)) : List<&2, T>}:
  match xs lo:
    case Nil{} 0n:
      LY.somes_pop(T, Nil{}, m, h)
    case Con{h2, +r} 0n:
      LY.somes_pop(T, Con{h2, r}, m, h)
    case Nil{} 1n+k:
      Empty.absurd({Nil{} == Nil{} : List<&2, T>}, L.false_true(h))
    case Con{None{}, +r} 1n+k:
      somes_pop_back(T, r, k, m, h)
    case Con{Some{x}, r} 1n+k:
      Empty.absurd({LY.somes(T, SC.update(Maybe<&2, T>, Con{Some{x}, r}, Nat.add(1n+k, m), None{})) == SC.init(T, Con{x, LY.somes(T, r)}) : List<&2, T>}, L.false_true(h))

# ---- growth: free slots appended at the back or prepended at the front ----

def win_grow_back(-T: Data, +xs: List<&2, Maybe<&2, T>>, +lo: Nat, +n: Nat, +k: Nat, +h: {win(T, xs, lo, n) == True{} : Bool}) -> {win(T, SC.append(Maybe<&2, T>, xs, SC.replicate(Maybe<&2, T>, k, None{})), lo, n) == True{} : Bool}:
  match xs lo:
    case Nil{} 0n:
      lay_win(T, SC.append(Maybe<&2, T>, Nil{}, SC.replicate(Maybe<&2, T>, k, None{})), n, LY.lay_grow(T, Nil{}, n, k, h))
    case Con{h2, +r} 0n:
      lay_win(T, SC.append(Maybe<&2, T>, Con{h2, r}, SC.replicate(Maybe<&2, T>, k, None{})), n, LY.lay_grow(T, Con{h2, r}, n, k, h))
    case Nil{} 1n+j:
      Empty.absurd({win(T, SC.replicate(Maybe<&2, T>, k, None{}), 1n+j, n) == True{} : Bool}, L.false_true(h))
    case Con{None{}, +r} 1n+j:
      win_grow_back(T, r, j, n, k, h)
    case Con{Some{x}, r} 1n+j:
      Empty.absurd({win(T, SC.append(Maybe<&2, T>, Con{Some{x}, r}, SC.replicate(Maybe<&2, T>, k, None{})), 1n+j, n) == True{} : Bool}, L.false_true(h))

def win_pad_front(-T: Data, +xs: List<&2, Maybe<&2, T>>, +n: Nat, k: Nat, +h: {win(T, xs, 0n, n) == True{} : Bool}) -> {win(T, SC.append(Maybe<&2, T>, SC.replicate(Maybe<&2, T>, k, None{}), xs), k, n) == True{} : Bool}:
  match k:
    case 0n:
      h
    case 1n+j:
      win_pad_front(T, xs, n, j, h)

def somes_pad_front(-T: Data, +xs: List<&2, Maybe<&2, T>>, k: Nat) -> {LY.somes(T, SC.append(Maybe<&2, T>, SC.replicate(Maybe<&2, T>, k, None{}), xs)) == LY.somes(T, xs) : List<&2, T>}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      somes_pad_front(T, xs, j)

# ---- the empty deque ----

def win_empty(-T: Data) -> {win(T, Con{None{}, Nil{}}, 0n, 0n) == True{} : Bool}:
  {==}
