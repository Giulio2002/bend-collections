import Base
import ./fold.bend as Chain
import ../../../src/containers/internal/intrusive_list.bend as L
import ../../../src/containers/types/intrusive_doubly_linked_list.bend as E

# Exact callback order for every finite chain under sufficient fuel.
# In this observer instance link stores are silent and root/post hooks may
# change arbitrary affine state. Detachment itself is checked separately.
def ignore_link(~S: Type, ~V: Data, s: S, n: List<&2, V>, m: Maybe<&2, List<&2, V>>) -> S:
  s

def model(~S: Type, ~V: Data, ~C: Data, ~post: S -> C -> List<&2, V> -> S, +rest: List<&2, V>, head: List<&2, V>, +c: C, s: S) -> S & Result<&2, &1, E.Error, Unit>:
  match rest:
    case Nil{}: (post(s, c, head), Done{Unit{}})
    case Con{v, tail}: model(~S, ~V, ~C, ~post, tail, head, c, post(s, c, Con{v, tail}))

def clear_loop_order(~S: Type, ~V: Data, ~C: Data, ~post: S -> C -> List<&2, V> -> S, +rest: List<&2, V>, +head: List<&2, V>, +c: C, s: S) -> {L.clear_loop(~S, ~List<&2, V>, ~C, ~(s => n => Chain.next(~S, ~V, s, n)), ~(s => n => m => ignore_link(~S, ~V, s, n, m)), ~(s => n => m => ignore_link(~S, ~V, s, n, m)), ~post, 1n+List.length(&2, V, rest), head, c, (s, Chain.cursor(V, rest))) == model(~S, ~V, ~C, ~post, rest, head, c, s) : S & Result<&2, &1, E.Error, Unit>}:
  match rest:
    case Nil{}: {==}
    case Con{v, tail}:
      clear_loop_order(~S, ~V, ~C, ~post, tail, head, c, post(s, c, Con{v, tail}))

def preflight_fits(~S: Type, ~V: Data, +xs: List<&2, V>, -s: S) -> {L.chain_fits(~S, ~List<&2, V>, ~(s => n => Chain.next(~S, ~V, s, n)), List.length(&2, V, xs), (s, Chain.cursor(V, xs))) == (s, True{}) : S & Bool}:
  match xs:
    case Nil{}: {==}
    case Con{v, rest}: preflight_fits(~S, ~V, rest, s)

def expected(~S: Type, ~V: Data, ~I: Data, ~C: Data, ~sh: S -> I -> Maybe<&2, List<&2, V>> -> S, ~post: S -> C -> List<&2, V> -> S, +xs: List<&2, V>, i: I, c: C, s: S) -> S & Result<&2, &1, E.Error, Unit>:
  match xs:
    case Nil{}: (s, Done{Unit{}})
    case Con{v, rest}: model(~S, ~V, ~C, ~post, rest, Con{v, rest}, c, sh(s, i, None{}))

def clear_list_order(~S: Type, ~V: Data, ~I: Data, ~C: Data, ~sh: S -> I -> Maybe<&2, List<&2, V>> -> S, ~post: S -> C -> List<&2, V> -> S, +xs: List<&2, V>, +i: I, +c: C, s: S) -> {L.clear_list_as(~S, ~List<&2, V>, ~List<&2, V>, ~I, ~C, ~(s => h => Chain.get(~S, ~V, s, h)), ~(s => n => Chain.next(~S, ~V, s, n)), ~(s => n => m => ignore_link(~S, ~V, s, n, m)), ~(s => n => m => ignore_link(~S, ~V, s, n, m)), ~sh, ~post, List.length(&2, V, xs), s, xs, i, c) == expected(~S, ~V, ~I, ~C, ~sh, ~post, xs, i, c, s) : S & Result<&2, &1, E.Error, Unit>}:
  match xs:
    case Nil{}: {==}
    case Con{v, rest}:
      %Equal.sym(S & Bool, L.chain_fits(~S, ~List<&2, V>, ~(s => n => Chain.next(~S, ~V, s, n)), List.length(&2, V, Con{v, rest}), (s, Chain.cursor(V, Con{v, rest}))), (s, True{}), preflight_fits(~S, ~V, Con{v, rest}, s)) : {L.clear_checked(~S, ~List<&2, V>, ~List<&2, V>, ~I, ~C, ~(s => h => Chain.get(~S, ~V, s, h)), ~(s => n => Chain.next(~S, ~V, s, n)), ~(s => n => m => ignore_link(~S, ~V, s, n, m)), ~(s => n => m => ignore_link(~S, ~V, s, n, m)), ~sh, ~post, 1n+List.length(&2, V, rest), Con{v, rest}, i, c, Some{Con{v, rest}}, _) == expected(~S, ~V, ~I, ~C, ~sh, ~post, Con{v, rest}, i, c, s) : S & Result<&2, &1, E.Error, Unit>}
      clear_loop_order(~S, ~V, ~C, ~post, rest, Con{v, rest}, c, sh(s, i, None{}))
