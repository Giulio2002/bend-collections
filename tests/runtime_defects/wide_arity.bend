import Base

# Minimal reproducer: Bend 2.0.16's native C backend flattens a non-recursive
# Data constructor into one node and rejects a flattened arity over 255.
# Word(64n) occupies 64 slots, so a constructor with four or more Word(64n)
# fields cannot exist in a native binary:
#
#   bend tests/runtime_defects/wide_arity.bend            -> prints "ok" (run mode)
#   bend tests/runtime_defects/wide_arity.bend -o /tmp/wa -> "Error: an arity over 255"
#
# reference/lru/types/model.bend declares
#   type Metrics is Data: Counts{inserts, evictions, removals, hits, misses}
# with five Word(64n) fields (320 slots), and every Cache value contains one,
# so the retained LRU cannot be compiled to a native binary. reference/ is an
# immutable pinned snapshot, so this cannot be fixed in editable source.
# Three fields (192 slots) still compile; see docs/VALIDATION.md.
#
# Further narrowing (iteration 0002), so the defect report is exact:
#   * the failure is in CODE GENERATION, not linking: `-o out.c` (emit C) fails
#     with the same message, so there is no "emit C and compile it yourself"
#     route;
#   * `bend --help` exposes no flag affecting flattening or the arity cap;
#   * a program whose ONLY contact with the retained cache is building
#     reference/lru/types/model.bend `zero_metrics()` already fails, so the
#     blocker is `Metrics` itself and not `Cache.State` that embeds it;
#   * `Cache.State` stores `counts: T.Metrics` by value, so every Cache value
#     transitively contains it and no editable wrapper, boxing at the call
#     site, or narrower type instantiation can change the layout of a type
#     declared inside the hash-pinned reference/ snapshot.
# Further narrowing (iteration 0004): flattening is TRANSITIVE through
# non-recursive Data, and only a recursive field type escapes it. Measured
# with this compiler, outside the workspace:
#   * `type Int64 is Data: I64{bits: Word(64n)}` and then a constructor with
#     five `Int64` fields still fails with "an arity over 255" (5 x 64 = 320
#     slots): boxing each counter in a one-field record does NOT help;
#   * the same constructor with five fields of a RECURSIVE type
#     (`type Rec is Data: RNil{} | RCons{head: Word(64n), tail: Rec}`)
#     compiles and runs (arity 5), because a recursive type is a pointer.
# So a native LRU would need `reference/lru/types/model.bend` `Metrics` to
# change its field type to a recursive one -- a change inside the hash-pinned
# snapshot, which would also have to be mirrored in the 383 places where the
# reference's own proofs construct or match `Counts{...}`. Porting the whole
# reference (25k lines, 22.5k of them proofs) into editable src/ is the only
# route, and it is not in this iteration.
#
# Consequence: the nine lru.* operations of
# automation/performance_contract.json have no native rows. This is reported
# as a live gate failure, not an exemption.

type Wide is Data:
  W4{a: Word(64n), b: Word(64n), c: Word(64n), d: Word(64n)}

# Boxing a Word(64n) in a one-field non-recursive record does not change the
# flattened arity: Boxed below is 5 x 64 = 320 slots and is rejected too.
type Int64 is Data:
  I64{bits: Word(64n)}

type Boxed is Data:
  B5{a: Int64, b: Int64, c: Int64, d: Int64, e: Int64}

# A recursive field type is a pointer, so this one IS accepted (arity 5).
type Rec is Data:
  RNil{}
  RCons{head: Word(64n), tail: Rec}

type Recs is Data:
  R5{a: Rec, b: Rec, c: Rec, d: Rec, e: Rec}

def z64() -> Int64:
  I64{Word.zero(64n)}

def boxed() -> Boxed:
  B5{z64(), z64(), z64(), z64(), z64()}

def r1() -> Rec:
  RCons{Word.zero(64n), RNil{}}

def recs() -> Recs:
  R5{r1(), r1(), r1(), r1(), r1()}

def sh_boxed(b: Boxed) -> String:
  match b:
    case B5{a, b2, c, d, e}:
      "ok"

def sh_recs(b: Recs) -> String:
  match b:
    case R5{a, b2, c, d, e}:
      "ok"

type Narrow is Data:
  W3{a: Word(64n), b: Word(64n), c: Word(64n)}

def wide() -> Wide:
  W4{Word.zero(64n), Word.zero(64n), Word.zero(64n), Word.zero(64n)}

def narrow() -> Narrow:
  W3{Word.zero(64n), Word.zero(64n), Word.zero(64n)}

def sh(w: Wide) -> String:
  match w:
    case W4{a, b, c, d}:
      "ok"

def sh3(w: Narrow) -> String:
  match w:
    case W3{a, b, c}:
      "ok"

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(sh3(narrow()))
    IO.print(sh_recs(recs()))
    IO.print(sh_boxed(boxed()))
    IO.print(sh(wide()))
