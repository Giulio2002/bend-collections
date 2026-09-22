import Base
import ../../src/containers/bitset.bend as B

# The word-list model of the packed representation.
#
# src/bitset.bend stores the words in a native Base.Array and addresses them
# by index; the mathematics of "what the words mean" is easier to state over
# the list of stored words, so these are the list-level counterparts of the
# runtime walks. proofs/bitset/arr.bend proves that each runtime operation
# does exactly what the corresponding function here says, on the list of the
# array's slots, and proofs/bitset/state.bend then relates that list to the
# independent bit-sequence specification.
#
# These definitions are the ones src/bitset.bend used before it moved to
# Base.Array, so every lemma of proofs/bitset/state.bend about them is the
# retained one.

# Zero words covering n more bits; `free` counts unused bits left in the
# last emitted word, so exactly ceil(n/32) words are produced from free = 0.
def zeros(n: Nat, free: Nat) -> List<&2, U32>:
  match n free:
    case 0n _:
      Nil{}
    case 1n+p 0n:
      Con{0, zeros(p, 31n)}
    case 1n+p 1n+f:
      zeros(p, f)

def get_pick(b: Bool, w: U32, +i: Nat, r: Bool) -> Bool:
  match b:
    case True{}:
      B.word_get(w, i)
    case False{}:
      r

def get_walk(ws: List<&2, U32>, +i: Nat) -> Bool:
  match ws:
    case Nil{}:
      False{}
    case Con{w, t}:
      get_pick(Nat.is_lt(i, 32n), w, i, get_walk(t, Nat.sub(i, 32n)))

def put_pick(b: Bool, +v: Bool, +w: U32, +i: Nat, t: List<&2, U32>, r: List<&2, U32>) -> List<&2, U32>:
  match b:
    case True{}:
      Con{B.word_put(v, w, i), t}
    case False{}:
      Con{w, r}

def put_walk(+ws: List<&2, U32>, +i: Nat, +v: Bool) -> List<&2, U32>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{+w, +t}:
      put_pick(Nat.is_lt(i, 32n), v, w, i, t, put_walk(t, Nat.sub(i, 32n), v))

def zip_words(+k: B.WordOp, ws: List<&2, U32>, vs: List<&2, U32>) -> List<&2, U32>:
  match ws vs:
    case Con{a, s} Con{b, t}:
      Con{B.word_op(k, a, b), zip_words(k, s, t)}
    case _ _:
      Nil{}

def count_words(ws: List<&2, U32>) -> Nat:
  match ws:
    case Nil{}:
      0n
    case Con{w, t}:
      Nat.add(B.word_count(32n, w), count_words(t))

def members_words(ws: List<&2, U32>, +off: Nat) -> List<&2, Nat>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{w, t}:
      B.word_members(32n, w, off, members_words(t, Nat.add(32n, off)))

