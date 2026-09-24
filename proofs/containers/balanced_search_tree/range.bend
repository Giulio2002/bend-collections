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
