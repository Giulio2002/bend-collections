import Base
import ../../../src/containers/internal/intrusive_list.bend as L
import ../../../src/containers/types/intrusive_doubly_linked_list.bend as E

# Sequence refinement of fold_left on a structurally represented chain.
# Callback state/accumulator are arbitrary affine Types. This establishes
# forward order and exact-once callbacks for every length, not just examples.
# Application array/handle adapters still need their own representation law.
def cursor(-V: Data, +xs: List<&2, V>) -> Maybe<&2, List<&2, V>>:
  match xs:
    case Nil{}: None{}
    case Con{v, rest}: Some{Con{v, rest}}

def next(~S: Type, ~V: Data, s: S, node: List<&2, V>) -> S & Maybe<&2, List<&2, V>>:
  match node:
    case Nil{}: (s, None{})
    case Con{v, rest}: (s, cursor(V, rest))

def value(~S: Type, ~V: Data, ~zero: V, s: S, node: List<&2, V>) -> S & V:
  match node:
    case Nil{}: (s, zero)
    case Con{v, rest}: (s, v)

def get(~S: Type, ~V: Data, s: S, h: List<&2, V>) -> S & Maybe<&2, List<&2, V>>:
  (s, cursor(V, h))

def model(~S: Type, ~V: Data, ~A: Type, ~C: Data, ~fn: S -> C -> A -> V -> S & A, xs: List<&2, V>, +c: C, r: S & A) -> S & Result<&2, &1, E.Error, A>:
  match xs r:
    case Nil{} Tuple{s, acc}: (s, Done{acc})
    case Con{v, rest} Tuple{s, acc}: model(~S, ~V, ~A, ~C, ~fn, rest, c, fn(s, c, acc, v))

def refinement(~S: Type, ~V: Data, ~A: Type, ~C: Data, ~zero: V, ~fn: S -> C -> A -> V -> S & A, +xs: List<&2, V>, +c: C, r: S & A) -> {L.fold_loop(~S, ~List<&2, V>, ~V, ~A, ~C, ~(s => n => next(~S, ~V, s, n)), ~(s => n => value(~S, ~V, ~zero, s, n)), ~fn, List.length(&2, V, xs), c, L.fold_step_3(~S, ~List<&2, V>, ~V, ~A, ~C, ~(s => n => next(~S, ~V, s, n)), ~(s => n => value(~S, ~V, ~zero, s, n)), ~fn, cursor(V, xs), r)) == model(~S, ~V, ~A, ~C, ~fn, xs, c, r) : S & Result<&2, &1, E.Error, A>}:
  match xs r:
    case Nil{} Tuple{s, acc}: {==}
    case Con{v, rest} Tuple{s, acc}:
      refinement(~S, ~V, ~A, ~C, ~zero, ~fn, rest, c, fn(s, c, acc, v))

def fold_left_refines(~S: Type, ~V: Data, ~A: Type, ~C: Data, ~zero: V, ~fn: S -> C -> A -> V -> S & A, +xs: List<&2, V>, +c: C, s: S, acc: A) -> {L.fold_left(~S, ~List<&2, V>, ~V, ~A, ~C, ~List<&2, V>, ~(s => h => get(~S, ~V, s, h)), ~(s => n => next(~S, ~V, s, n)), ~(s => n => value(~S, ~V, ~zero, s, n)), ~fn, List.length(&2, V, xs), s, xs, c, acc) == model(~S, ~V, ~A, ~C, ~fn, xs, c, (s, acc)) : S & Result<&2, &1, E.Error, A>}:
  refinement(~S, ~V, ~A, ~C, ~zero, ~fn, xs, c, (s, acc))
