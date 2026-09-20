import Base
import ../spec/prefix_trie.bend as PS
import ../src/prefix_trie.bend as P
import ../types/prefix_trie.bend as E
import ../types/balanced_search_tree.bend as BE
import ./prefix_trie/keys.bend as K
import ./prefix_trie/ops.bend as OP
import ./prefix_trie/steps.bend as ST
import ./prefix_trie/trace.bend as TR

# Prefix trie: public proof entry point (String keys, erased value type V).
#   abstraction  ST.abs (the empty key's entry, then the preorder enumeration
#                of the root's sibling lists, keys rebuilt character by
#                character)
#   invariant    ST.inv (every sibling list strictly increasing by code)
# Spec: the String.order-sorted finite map of spec/prefix_trie.bend; prefix
# listing is filtering, longest_prefix selects the maximal-length matching
# key. Every operation and error path is proven in ST.step_ok.

def new_abs(-V: Data) -> {ST.abs(V, P.new(V)) == Nil{} : List<&2, BE.Entry<String, V>>}:
  {==}

def new_inv(-V: Data) -> {ST.inv(V, P.new(V)) == True{} : Bool}:
  {==}

def step_ok(-V: Data, +s: P.PrefixTrie<V>, +op: E.Op<V>, +g: {ST.inv(V, s) == True{} : Bool}) -> ST.StepOK(V, s, op):
  ST.step_ok(V, s, op, g)

def trace_new(-V: Data, +ops: List<&2, E.Op<V>>) -> {TR.view(V, P.run(V, ops, P.new(V))) == PS.run(V, ops, Nil{}) : List<&2, BE.Entry<String, V>> & List<&2, E.Obs<V>>}:
  TR.trace_from(V, ops, P.new(V), {==})

def trace_new_inv(-V: Data, +ops: List<&2, E.Op<V>>) -> {ST.inv(V, Pair.fst(P.PrefixTrie<V>, List<&2, E.Obs<V>>, P.run(V, ops, P.new(V)))) == True{} : Bool}:
  TR.inv_from(V, ops, P.new(V), {==})
