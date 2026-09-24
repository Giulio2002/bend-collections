import Base
import ./spec.bend as Spec
import ./fold.bend as Fold
import ./clear.bend as Clear
import ../../lib/nat.bend as NN
import ../../../src/containers/internal/intrusive_list.bend as L
import ../../../src/containers/types/intrusive_doubly_linked_list.bend as E

# Quantified edit-program refinement over the ACTUAL public operations.
# Read-result premises describe primitive accessor observations, not list
# correctness or the result being proved. Setters are arbitrary: the theorem
# preserves their order, identity and distinction, including their effects.
# This does not certify application accessors, handle validity, races, the
# compiler, or every callback-driven traversal. See the validation document.

def remove_known(~S: Type, ~N: Data, ~I: Data, ~next: S -> N -> S & Maybe<&2, N>, ~prev: S -> N -> S & Maybe<&2, N>, ~sn: S -> N -> Maybe<&2, N> -> S, ~sp: S -> N -> Maybe<&2, N> -> S, ~sh: S -> I -> Maybe<&2, N> -> S, ~sf: S -> I -> N -> S, s2: S, +i: I, +node: N, +before: Maybe<&2, N>, +after: Maybe<&2, N>) -> {L.remove_2(~S, ~N, ~I, ~next, ~prev, ~sn, ~sp, ~sh, i, node, after, (s2, before)) == Spec.run(~S, ~N, ~I, ~sn, ~sp, ~sh, ~sf, Spec.remove(N, I, i, node, before, after), s2) : S}:
  match before after:
    case None{} None{}: {==}
    case None{} Some{q}: {==}
    case Some{p} None{}: {==}
    case Some{p} Some{q}: {==}

def remove_writes(~S: Type, ~N: Data, ~I: Data, ~next: S -> N -> S & Maybe<&2, N>, ~prev: S -> N -> S & Maybe<&2, N>, ~sn: S -> N -> Maybe<&2, N> -> S, ~sp: S -> N -> Maybe<&2, N> -> S, ~sh: S -> I -> Maybe<&2, N> -> S, ~sf: S -> I -> N -> S, s: S, s1: S, s2: S, +i: I, +node: N, +before: Maybe<&2, N>, +after: Maybe<&2, N>, hn: {next(s, node) == (s1, after) : S & Maybe<&2, N>}, hp: {prev(s1, node) == (s2, before) : S & Maybe<&2, N>}) -> {L.remove(~S, ~N, ~I, ~next, ~prev, ~sn, ~sp, ~sh, s, i, node) == Spec.run(~S, ~N, ~I, ~sn, ~sp, ~sh, ~sf, Spec.remove(N, I, i, node, before, after), s2) : S}:
  %Equal.sym(S & Maybe<&2, N>, next(s, node), (s1, after), hn) : {L.remove_1(~S, ~N, ~I, ~next, ~prev, ~sn, ~sp, ~sh, i, node, _) == Spec.run(~S, ~N, ~I, ~sn, ~sp, ~sh, ~sf, Spec.remove(N, I, i, node, before, after), s2) : S}
  %Equal.sym(S & Maybe<&2, N>, prev(s1, node), (s2, before), hp) : {L.remove_2(~S, ~N, ~I, ~next, ~prev, ~sn, ~sp, ~sh, i, node, after, _) == Spec.run(~S, ~N, ~I, ~sn, ~sp, ~sh, ~sf, Spec.remove(N, I, i, node, before, after), s2) : S}
  remove_known(~S, ~N, ~I, ~next, ~prev, ~sn, ~sp, ~sh, ~sf, s2, i, node, before, after)

def prepend_known(~S: Type, ~N: Data, ~H: Data, ~I: Data, ~get: S -> H -> S & Maybe<&2, N>, ~sn: S -> N -> Maybe<&2, N> -> S, ~sp: S -> N -> Maybe<&2, N> -> S, ~sh: S -> I -> Maybe<&2, N> -> S, ~sf: S -> I -> N -> S, s1: S, +i: I, +node: N, +head: Maybe<&2, N>) -> {L.prepend_as_1(~S, ~N, ~H, ~I, ~get, ~sn, ~sp, ~sf, i, node, (s1, head)) == Spec.run(~S, ~N, ~I, ~sn, ~sp, ~sh, ~sf, Spec.prepend(N, I, i, node, head), s1) : S}:
  match head:
    case None{}: {==}
    case Some{q}: {==}

def prepend_writes(~S: Type, ~N: Data, ~H: Data, ~I: Data, ~get: S -> H -> S & Maybe<&2, N>, ~sn: S -> N -> Maybe<&2, N> -> S, ~sp: S -> N -> Maybe<&2, N> -> S, ~sh: S -> I -> Maybe<&2, N> -> S, ~sf: S -> I -> N -> S, s: S, s1: S, +h: H, +i: I, +node: N, +head: Maybe<&2, N>, hg: {get(s, h) == (s1, head) : S & Maybe<&2, N>}) -> {L.prepend_as(~S, ~N, ~H, ~I, ~get, ~sn, ~sp, ~sf, s, h, i, node) == Spec.run(~S, ~N, ~I, ~sn, ~sp, ~sh, ~sf, Spec.prepend(N, I, i, node, head), s1) : S}:
  %Equal.sym(S & Maybe<&2, N>, get(s, h), (s1, head), hg) : {L.prepend_as_1(~S, ~N, ~H, ~I, ~get, ~sn, ~sp, ~sf, i, node, _) == Spec.run(~S, ~N, ~I, ~sn, ~sp, ~sh, ~sf, Spec.prepend(N, I, i, node, head), s1) : S}
  prepend_known(~S, ~N, ~H, ~I, ~get, ~sn, ~sp, ~sh, ~sf, s1, i, node, head)

def pool_then_next(~S: Type, ~N: Data, ~C: Data, ~next: S -> N -> S & Maybe<&2, N>, ~sn: S -> N -> Maybe<&2, N> -> S, ~make: S -> C -> S & N, c: C, r: S & E.Pool<N>) -> S & (E.Pool<N> & N):
  (s, pool) = r
  L.pool_next(~S, ~N, ~C, ~next, ~sn, ~make, s, pool, c)

def pool_lifo(~S: Type, ~N: Data, ~C: Data, ~next: S -> N -> S & Maybe<&2, N>, ~sn: S -> N -> Maybe<&2, N> -> S, ~make: S -> C -> S & N, s: S, +c: C, +node: N, +head: Maybe<&2, N>, +count: Nat, read_back: {next(sn(s, node, head), node) == (sn(s, node, head), head) : S & Maybe<&2, N>}) -> {pool_then_next(~S, ~N, ~C, ~next, ~sn, ~make, c, L.pool_free(~S, ~N, ~sn, s, E.Pool{head, count}, node)) == (sn(sn(s, node, head), node, None{}), (E.Pool{head, count}, node)) : S & (E.Pool<N> & N)}:
  %Equal.sym(S & Maybe<&2, N>, next(sn(s, node, head), node), (sn(s, node, head), head), read_back) : {L.pool_take_1(~S, ~N, ~C, ~next, ~sn, ~make, node, 1n+count, _) == (sn(sn(s, node, head), node, None{}), (E.Pool{head, count}, node)) : S & (E.Pool<N> & N)}
  Equal.cong(Nat, S & (E.Pool<N> & N), k => (sn(sn(s, node, head), node, None{}), (E.Pool{head, k}, node)), Nat.sub(count, 0n), count, NN.sub_zero(count))

def default_node(~N: Data, ~V: Data, +v: V) -> {L.new_node(~N, ~V, v) == E.Node{None{}, None{}, v} : E.DefaultNode<N, V>}:
  {==}
