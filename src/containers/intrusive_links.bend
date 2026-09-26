import Base
import ./intrusive_doubly_linked_list.bend as IL

# A ready-made link table for the intrusive list: entity ids are U32 values
# 1 .. 2^node_depth - 1 (0 means "no entity"), roots are 0 .. 2^root_depth - 1.
# One U32 per link, so a membership edit is a few indexed array writes. The
# accessors below are the ones proved to meet the adapter laws for every size
# (proofs/containers/intrusive_doubly_linked_list/links.bend); an application
# that keeps its own entity array can copy this layout.
type Links is Type:
  Links{nexts: Array<U32>, prevs: Array<U32>, heads: Array<U32>}

def new(+node_depth: Nat, +root_depth: Nat) -> Links:
  Links{Array.new(U32, node_depth, 0), Array.new(U32, node_depth, 0), Array.new(U32, root_depth, 0)}

def decode_pick(+x: U32, zero: Bool) -> Maybe<&2, U32>:
  match zero:
    case True{}:
      None{}
    case False{}:
      Some{x}

def decode(+x: U32) -> Maybe<&2, U32>:
  decode_pick(x, U32.is_eq(x, 0))

def encode(m: Maybe<&2, U32>) -> U32:
  match m:
    case None{}:
      0
    case Some{x}:
      x

def next_got(prevs: Array<U32>, heads: Array<U32>, r: Array<U32> & U32) -> Links & Maybe<&2, U32>:
  (nexts, +x) = r
  (Links{nexts, prevs, heads}, decode(x))

def prev_got(nexts: Array<U32>, heads: Array<U32>, r: Array<U32> & U32) -> Links & Maybe<&2, U32>:
  (prevs, +x) = r
  (Links{nexts, prevs, heads}, decode(x))

def head_got(nexts: Array<U32>, prevs: Array<U32>, r: Array<U32> & U32) -> Links & Maybe<&2, U32>:
  (heads, +x) = r
  (Links{nexts, prevs, heads}, decode(x))

def next(s: Links, n: U32) -> Links & Maybe<&2, U32>:
  Links{nexts, prevs, heads} = s
  next_got(prevs, heads, Array.get(U32, nexts, n))

def prev(s: Links, n: U32) -> Links & Maybe<&2, U32>:
  Links{nexts, prevs, heads} = s
  prev_got(nexts, heads, Array.get(U32, prevs, n))

def get_head(s: Links, r: U32) -> Links & Maybe<&2, U32>:
  Links{nexts, prevs, heads} = s
  head_got(nexts, prevs, Array.get(U32, heads, r))

def set_next(s: Links, n: U32, m: Maybe<&2, U32>) -> Links:
  Links{nexts, prevs, heads} = s
  Links{Array.set(U32, nexts, n, encode(m)), prevs, heads}

def set_prev(s: Links, n: U32, m: Maybe<&2, U32>) -> Links:
  Links{nexts, prevs, heads} = s
  Links{nexts, Array.set(U32, prevs, n, encode(m)), heads}

def set_head(s: Links, r: U32, m: Maybe<&2, U32>) -> Links:
  Links{nexts, prevs, heads} = s
  Links{nexts, prevs, Array.set(U32, heads, r, encode(m))}

def set_head_nonempty(s: Links, r: U32, n: U32) -> Links:
  set_head(s, r, Some{n})

# Detach member n of root r in O(1).
def remove(s: Links, +r: U32, +n: U32) -> Links:
  IL.remove(~Links, ~U32, ~U32, ~next, ~prev, ~set_next, ~set_prev, ~set_head, s, r, n)

# Link detached entity n at the front of root r in O(1).
def prepend(s: Links, +r: U32, +n: U32) -> Links:
  IL.prepend_as(~Links, ~U32, ~U32, ~U32, ~get_head, ~set_next, ~set_prev, ~set_head_nonempty, s, r, r, n)
