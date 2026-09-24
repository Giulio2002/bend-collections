import Base
import ../../../src/containers/balanced_search_tree.bend as M
import ../../../src/containers/types/dynamic_array.bend as DE

# Universal local laws for the traversal optimization, not a proof of the
# complete indexed TreeMap or of arbitrary iterator histories.
def choice_equivalent(+x: Nat, +p: Nat, +q: Nat, +found: Bool) -> {M.ascend_choice(x, p, q, found) == M.pick(M.Ascend, found, M.Ascend{0n, p, True{}}, M.Ascend{x, q, False{}}) : M.Ascend}:
  match found:
    case False{}:
      {==}
    case True{}:
      {==}

def slot_preserves_buffer(nodes: M.NodeStore<U32>, value: Result<&2, &2, DE.Error, M.Node<U32>>) -> {Pair.fst(M.NodeStore<U32>, M.Node<U32>, M.node_slot_done(~U32, ~U32, ~U32.cmp, (nodes, value))) == nodes : M.NodeStore<U32>}:
  match value:
    case Fail{e}:
      {==}
    case Done{node}:
      {==}

def step_preserves_buffer(x: Nat, p: Nat, forward: Bool, nodes: M.NodeStore<U32>, node: M.Node<U32>) -> {Pair.fst(M.NodeStore<U32>, M.Ascend, M.ascend_slots_step(~U32, ~U32, ~U32.cmp, x, p, forward, (nodes, node))) == nodes : M.NodeStore<U32>}:
  match node:
    case M.Free{next}:
      {==}
    case M.N{red, left, right, parent, key}:
      {==}
