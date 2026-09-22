# Retained proof dependency: bend-collections@6ce40ef:src/doubly_linked_list.bend
# Only declarations needed by the LRU refinement are kept; no retired runtime is imported.
# Proof-only dependency extracted from retained LRU support; no retired collection API.
import Base

def nil() -> U32:
  0

# The link to an element, and the element a (non-nil) link points to.

def slot(+l: U32) -> U32:
  U32.sub(l, 1)


def set_next_go(nexts: Array<U32>, +a: U32, +q: U32, none: Bool) -> Array<U32>:
  match none:
    case True{}:
      nexts
    case False{}:
      Array.set(U32, nexts, slot(a), q)

# ---- insertion ----


def set_next(nexts: Array<U32>, +a: U32, +q: U32) -> Array<U32>:
  set_next_go(nexts, a, q, U32.is_eq(a, nil()))


def pick_end(none: Bool, +n: U32, +e: U32) -> U32:
  match none:
    case True{}:
      n
    case False{}:
      e
