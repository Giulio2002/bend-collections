import Base

# Port of reference/lru/types/model.bend, byte-identical EXCEPT for the
# layout of `Metrics`, and a pair of accessors for it.
#
# WHY THE LAYOUT HAD TO CHANGE. The retained snapshot declares
#
#   type Metrics is Data:
#     Counts{inserts: Word(64n), evictions: Word(64n), removals: Word(64n),
#            hits: Word(64n), misses: Word(64n)}
#
# The native C backend of Bend 2.0.16 FLATTENS a constructor's fields, and
# `Word(64n)` flattens to 64 slots, so that constructor needs 320 and the
# backend rejects it with "an arity over 255". Measured in this workspace:
# three `Word(64n)` fields compile (192), four do not (256); nesting the
# counters inside another record or inside a two-constructor wrapper does NOT
# help, because flattening is recursive; a RECURSIVE container does, because
# it cannot be unrolled. The counters therefore live in a list, which keeps
# their exact 64-bit values and wrap-around semantics -- nothing about the
# numeric domain changes, only where the five words are stored.
#
# reference/lru stays byte-identical and hash-pinned; this port exists so the
# cache can be COMPILED NATIVELY for the benchmark rows. The trust boundary
# and the provenance are in docs/lru-compat.md.

# Negative{n} denotes -(n+1), so zero has exactly one representation.
type Integer is Data:
  Positive{magnitude: Nat}
  Negative{predecessor: Nat}

type Int64 is Data:
  I64{bits: Word(64n)}

# The five counters, in the order of the snapshot's fields:
# inserts, evictions, removals, hits, misses.
type Metrics is Data:
  Counts{cs: List<&2, Word(64n)>}

type Entry<-K: Data, -V: Data> is Data:
  Item{key: K, value: V, deadline: Int64}

type Event<-K: Data, -V: Data> is Data:
  Evicted{key: K, value: V}

def zero_metrics() -> Metrics:
  Counts{Con{Word.zero(64n), Con{Word.zero(64n), Con{Word.zero(64n), Con{Word.zero(64n), Con{Word.zero(64n), Nil{}}}}}}}

# ---- the five counters by position ----

def nth_word(cs: List<&2, Word(64n)>, +i: Nat) -> Word(64n):
  match cs i:
    case Nil{} _:
      Word.zero(64n)
    case Con{+w, t} 0n:
      w
    case Con{w, t} 1n+p:
      nth_word(t, p)

def bump_at(cs: List<&2, Word(64n)>, +i: Nat) -> List<&2, Word(64n)>:
  match cs i:
    case Nil{} _:
      Nil{}
    case Con{+w, t} 0n:
      Con{Word.inc(64n, w), t}
    case Con{w, t} 1n+p:
      Con{w, bump_at(t, p)}

def counter(+i: Nat, m: Metrics) -> Word(64n):
  match m:
    case Counts{cs}:
      nth_word(cs, i)

def bump(+i: Nat, m: Metrics) -> Metrics:
  match m:
    case Counts{cs}:
      Counts{bump_at(cs, i)}

def inserts(m: Metrics) -> Word(64n):
  counter(0n, m)

def evictions(m: Metrics) -> Word(64n):
  counter(1n, m)

def removals(m: Metrics) -> Word(64n):
  counter(2n, m)

def hits(m: Metrics) -> Word(64n):
  counter(3n, m)

def misses(m: Metrics) -> Word(64n):
  counter(4n, m)
