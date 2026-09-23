import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/spec_common.bend as SC
import ../../../src/containers/bitset.bend as B
import ./model.bend as MD
import ./index.bend as IX

# The word-list walks of proofs/bitset/model.bend, re-expressed as a single
# indexed access. This is the step that lets src/bitset.bend address the word
# directly (Base.Array, O(1)) instead of walking the list:
#
#   get_walk(ws, i)    = word_get(word wordix(i) of ws, bitix(i))
#   put_walk(ws, i, v) = ws with word wordix(i) replaced by
#                        word_put(v, that word, bitix(i))

# Word q of the list (0 beyond the end; the callers always stay in range).
def nthw(ws: List<&2, U32>, q: Nat) -> U32:
  match ws q:
    case Nil{} _:
      0
    case Con{w, t} 0n:
      w
    case Con{w, t} 1n+p:
      nthw(t, p)

def shrn_zero(+k: Nat) -> {U32.shrn(0, k) == 0 : U32}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(U32, U32.shrn(0, p), 0, shrn_zero(p)) : {U32.shr(_) == 0 : U32}
      {==}

def word_get_zero(+k: Nat) -> {B.word_get(0, k) == False{} : Bool}:
  %Equal.sym(U32, U32.shrn(0, k), 0, shrn_zero(k)) : {B.low(_) == False{} : Bool}
  {==}

# ---- get ----

def get_case(+w: U32, +t: List<&2, U32>, +i: Nat, b: Bool, +eb: {Nat.is_lt(i, 32n) == b : Bool}, +ih: {MD.get_walk(t, Nat.sub(i, 32n)) == B.word_get(nthw(t, B.wordix(Nat.sub(i, 32n))), B.bitix(Nat.sub(i, 32n))) : Bool}) -> {MD.get_pick(b, w, i, MD.get_walk(t, Nat.sub(i, 32n))) == B.word_get(nthw(Con{w, t}, B.wordix(i)), B.bitix(i)) : Bool}:
  match b:
    case True{}:
      %Equal.sym(Nat, B.wordix(i), 0n, IX.wordix_small(i, eb)) : {B.word_get(w, i) == B.word_get(nthw(Con{w, t}, _), B.bitix(i)) : Bool}
      %Equal.sym(Nat, B.bitix(i), i, IX.bitix_small(i, eb)) : {B.word_get(w, i) == B.word_get(w, _) : Bool}
      {==}
    case False{}:
      %Equal.sym(Nat, B.wordix(i), 1n+B.wordix(Nat.sub(i, 32n)), IX.wordix_step(i, eb)) : {MD.get_walk(t, Nat.sub(i, 32n)) == B.word_get(nthw(Con{w, t}, _), B.bitix(i)) : Bool}
      %Equal.sym(Nat, B.bitix(i), B.bitix(Nat.sub(i, 32n)), IX.bitix_step(i, eb)) : {MD.get_walk(t, Nat.sub(i, 32n)) == B.word_get(nthw(t, B.wordix(Nat.sub(i, 32n))), _) : Bool}
      ih

def get_index(ws: List<&2, U32>, +i: Nat) -> {MD.get_walk(ws, i) == B.word_get(nthw(ws, B.wordix(i)), B.bitix(i)) : Bool}:
  match ws:
    case Nil{}:
      Equal.sym(Bool, B.word_get(0, B.bitix(i)), False{}, word_get_zero(B.bitix(i)))
    case Con{+w, +t}:
      get_case(w, t, i, Nat.is_lt(i, 32n), {==}, get_index(t, Nat.sub(i, 32n)))

# ---- put ----

def put_case(+v: Bool, +w: U32, +t: List<&2, U32>, +i: Nat, b: Bool, +eb: {Nat.is_lt(i, 32n) == b : Bool}, +ih: {MD.put_walk(t, Nat.sub(i, 32n), v) == SC.update(U32, t, B.wordix(Nat.sub(i, 32n)), B.word_put(v, nthw(t, B.wordix(Nat.sub(i, 32n))), B.bitix(Nat.sub(i, 32n)))) : List<&2, U32>}) -> {MD.put_pick(b, v, w, i, t, MD.put_walk(t, Nat.sub(i, 32n), v)) == SC.update(U32, Con{w, t}, B.wordix(i), B.word_put(v, nthw(Con{w, t}, B.wordix(i)), B.bitix(i))) : List<&2, U32>}:
  match b:
    case True{}:
      %Equal.sym(Nat, B.wordix(i), 0n, IX.wordix_small(i, eb)) : {Con{B.word_put(v, w, i), t} == SC.update(U32, Con{w, t}, _, B.word_put(v, nthw(Con{w, t}, _), B.bitix(i))) : List<&2, U32>}
      %Equal.sym(Nat, B.bitix(i), i, IX.bitix_small(i, eb)) : {Con{B.word_put(v, w, i), t} == Con{B.word_put(v, w, _), t} : List<&2, U32>}
      {==}
    case False{}:
      %Equal.sym(Nat, B.wordix(i), 1n+B.wordix(Nat.sub(i, 32n)), IX.wordix_step(i, eb)) : {Con{w, MD.put_walk(t, Nat.sub(i, 32n), v)} == SC.update(U32, Con{w, t}, _, B.word_put(v, nthw(Con{w, t}, _), B.bitix(i))) : List<&2, U32>}
      %Equal.sym(Nat, B.bitix(i), B.bitix(Nat.sub(i, 32n)), IX.bitix_step(i, eb)) : {Con{w, MD.put_walk(t, Nat.sub(i, 32n), v)} == Con{w, SC.update(U32, t, B.wordix(Nat.sub(i, 32n)), B.word_put(v, nthw(t, B.wordix(Nat.sub(i, 32n))), _))} : List<&2, U32>}
      Equal.cong(List<&2, U32>, List<&2, U32>, z => Con{w, z},
        MD.put_walk(t, Nat.sub(i, 32n), v),
        SC.update(U32, t, B.wordix(Nat.sub(i, 32n)), B.word_put(v, nthw(t, B.wordix(Nat.sub(i, 32n))), B.bitix(Nat.sub(i, 32n)))),
        ih)

def put_index(ws: List<&2, U32>, +i: Nat, +v: Bool) -> {MD.put_walk(ws, i, v) == SC.update(U32, ws, B.wordix(i), B.word_put(v, nthw(ws, B.wordix(i)), B.bitix(i))) : List<&2, U32>}:
  match ws:
    case Nil{}:
      {==}
    case Con{+w, +t}:
      put_case(v, w, t, i, Nat.is_lt(i, 32n), {==}, put_index(t, Nat.sub(i, 32n), v))

# ---- nthw is nth in range ----

def nthw_nth(ws: List<&2, U32>, q: Nat, +h: {Nat.is_lt(q, SC.length(U32, ws)) == True{} : Bool}) -> {SC.nth(U32, ws, q) == Some{nthw(ws, q)} : Maybe<&2, U32>}:
  match ws q:
    case Nil{} _:
      Empty.absurd({SC.nth(U32, Nil{}, q) == Some{nthw(Nil{}, q)} : Maybe<&2, U32>}, N.lt_zero_absurd(q, h))
    case Con{w, t} 0n:
      {==}
    case Con{w, t} 1n+p:
      nthw_nth(t, p, h)
