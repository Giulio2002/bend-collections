import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/list.bend as LL
import ../../../spec/lib/common.bend as SC

# List facts about take / drop / update at one position, used to describe the
# effect of an indexed loop over an array on the list of its slots.

def take_zero(-A: Data, xs: List<&2, A>) -> {SC.take(A, xs, 0n) == Nil{} : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

def drop_zero(-A: Data, xs: List<&2, A>) -> {SC.drop(A, xs, 0n) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

# The element at q, pulled out of the tail that starts there.
def drop_cons(-A: Data, xs: List<&2, A>, q: Nat, +x: A, +hx: {SC.nth(A, xs, q) == Some{x} : Maybe<&2, A>}) -> {SC.drop(A, xs, q) == Con{x, SC.drop(A, xs, 1n+q)} : List<&2, A>}:
  match xs q:
    case Nil{} _:
      Empty.absurd({Nil{} == Con{x, Nil{}} : List<&2, A>}, L.none_some(A, x, hx))
    case Con{h, t} 0n:
      %Equal.sym(List<&2, A>, SC.drop(A, t, 0n), t, drop_zero(A, t)) : {Con{h, t} == Con{x, _} : List<&2, A>}
      %Equal.sym(A, h, x, L.some_inj(A, h, x, hx)) : {Con{_, t} == Con{x, t} : List<&2, A>}
      {==}
    case Con{h, t} 1n+p:
      drop_cons(A, t, p, x, hx)

# One more element taken is that element appended.
def take_succ(-A: Data, xs: List<&2, A>, q: Nat, +x: A, +hx: {SC.nth(A, xs, q) == Some{x} : Maybe<&2, A>}) -> {SC.take(A, xs, 1n+q) == SC.snoc(A, SC.take(A, xs, q), x) : List<&2, A>}:
  match xs q:
    case Nil{} _:
      Empty.absurd({Nil{} == Con{x, Nil{}} : List<&2, A>}, L.none_some(A, x, hx))
    case Con{h, t} 0n:
      %Equal.sym(List<&2, A>, SC.take(A, t, 0n), Nil{}, take_zero(A, t)) : {Con{h, _} == SC.snoc(A, Nil{}, x) : List<&2, A>}
      %Equal.sym(A, h, x, L.some_inj(A, h, x, hx)) : {Con{_, Nil{}} == SC.snoc(A, Nil{}, x) : List<&2, A>}
      {==}
    case Con{h, t} 1n+p:
      Equal.cong(List<&2, A>, List<&2, A>, z => Con{h, z}, SC.take(A, t, 1n+p), SC.snoc(A, SC.take(A, t, p), x), take_succ(A, t, p, x, hx))

# Replacing position q does not disturb what follows it.
def drop_update(-A: Data, xs: List<&2, A>, q: Nat, +v: A) -> {SC.drop(A, SC.update(A, xs, q, v), 1n+q) == SC.drop(A, xs, 1n+q) : List<&2, A>}:
  match xs q:
    case Nil{} _:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+p:
      drop_update(A, t, p, v)

# ... nor what precedes it.
def take_update(-A: Data, xs: List<&2, A>, q: Nat, +v: A) -> {SC.take(A, SC.update(A, xs, q, v), q) == SC.take(A, xs, q) : List<&2, A>}:
  match xs q:
    case Nil{} _:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+p:
      Equal.cong(List<&2, A>, List<&2, A>, z => Con{h, z}, SC.take(A, SC.update(A, t, p, v), p), SC.take(A, t, p), take_update(A, t, p, v))

def take_update_succ(-A: Data, xs: List<&2, A>, q: Nat, +v: A, +h: {Nat.is_lt(q, SC.length(A, xs)) == True{} : Bool}) -> {SC.take(A, SC.update(A, xs, q, v), 1n+q) == SC.snoc(A, SC.take(A, xs, q), v) : List<&2, A>}:
  match xs q:
    case Nil{} _:
      Empty.absurd({SC.take(A, Nil{}, 1n+q) == SC.snoc(A, Nil{}, v) : List<&2, A>}, N.lt_zero_absurd(q, h))
    case Con{h2, t} 0n:
      %Equal.sym(List<&2, A>, SC.take(A, t, 0n), Nil{}, take_zero(A, t)) : {Con{v, _} == SC.snoc(A, Nil{}, v) : List<&2, A>}
      {==}
    case Con{h2, t} 1n+p:
      Equal.cong(List<&2, A>, List<&2, A>, z => Con{h2, z}, SC.take(A, SC.update(A, t, p, v), 1n+p), SC.snoc(A, SC.take(A, t, p), v), take_update_succ(A, t, p, v, h))

def take_all(-A: Data, xs: List<&2, A>) -> {SC.take(A, xs, SC.length(A, xs)) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(List<&2, A>, List<&2, A>, z => Con{h, z}, SC.take(A, t, SC.length(A, t)), t, take_all(A, t))

def drop_all(-A: Data, xs: List<&2, A>) -> {SC.drop(A, xs, SC.length(A, xs)) == Nil{} : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      drop_all(A, t)

