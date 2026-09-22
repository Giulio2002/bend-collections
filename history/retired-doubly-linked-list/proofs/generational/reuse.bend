import Base
import ../../src/doubly_linked_list.bend as D
import ../../src/internal/dlist_storage.bend as R
import ../../types/doubly_linked_list.bend as E
import ../lib/logic.bend as L
import ../lib/u32alg.bend as U

# Runtime-linked component laws for the new public generational API.
# No array/node/value lists are introduced into production by these shadows.
def low(g: U32) -> Bool:
  U32{WCon{bit, tail}} = g
  bit

def inc_distinct_go(+g: U32, same: Bool, +h: {U32.is_eq(U32.inc(g), g) == same : Bool}) -> {U32.is_eq(U32.inc(g), g) == False{} : Bool}:
  match same g:
    case False{} +g0:
      h
    case True{} U32{WCon{False{}, +t}}:
      Empty.absurd({U32.is_eq(U32.inc(U32{WCon{False{}, t}}), U32{WCon{False{}, t}}) == False{} : Bool}, L.false_true(Equal.sym(Bool, True{}, False{}, Equal.cong(U32, Bool, low, U32.inc(U32{WCon{False{}, t}}), U32{WCon{False{}, t}}, U.eq_of(U32.inc(U32{WCon{False{}, t}}), U32{WCon{False{}, t}}, h)))))
    case True{} U32{WCon{True{}, +t}}:
      Empty.absurd({U32.is_eq(U32.inc(U32{WCon{True{}, t}}), U32{WCon{True{}, t}}) == False{} : Bool}, L.false_true(Equal.cong(U32, Bool, low, U32.inc(U32{WCon{True{}, t}}), U32{WCon{True{}, t}}, U.eq_of(U32.inc(U32{WCon{True{}, t}}), U32{WCon{True{}, t}}, h))))

def inc_distinct(+g: U32) -> {U32.is_eq(U32.inc(g), g) == False{} : Bool}:
  inc_distinct_go(g, U32.is_eq(U32.inc(g), g), {==})

def single(~T: Data, g: U32, x: T) -> D.DList<T>:
  D.DL{0, 0n, 1, R.DL{0, 1, 0, 1n, 1, 1, 0n, 1, ALeaf{Some{x}}, ALeaf{0}, ALeaf{0}}, ALeaf{g}}

def freed(~T: Data, g: U32) -> D.DList<T>:
  D.DL{0, 0n, 1, R.DL{0, 1, 1, 0n, 0, 0, 0n, 1, ALeaf{None{}}, ALeaf{0}, ALeaf{0}}, ALeaf{U32.inc(g)}}

def exhausted(~T: Data) -> D.DList<T>:
  D.DL{0, 0n, 1, R.DL{0, 1, 0, 0n, 0, 0, 0n, 1, ALeaf{None{}}, ALeaf{0}, ALeaf{0}}, ALeaf{4294967295}}

def remove_reclaims(~T: Data, +g: U32, +x: T, +room: {U32.is_eq(g, 4294967295) == False{} : Bool}) -> {D.remove(~T, single(~T, g, x), E.H{0, 0, g}) == (freed(~T, g), Done{x}) : D.DList<T> & Result<&2, &2, E.Error, T>}:
  %Equal.sym(Bool, U32.is_eq(g, g), True{}, U.eq_refl(g)) : {D.project_value(~T, D.checked(~T, E.Remove{E.H{0, 0, g}}, (single(~T, g, x), D.generation_error(_)))) == (freed(~T, g), Done{x}) : D.DList<T> & Result<&2, &2, E.Error, T>}
  %Equal.sym(Bool, U32.is_eq(g, 4294967295), False{}, room) : {D.project_value(~T, D.retire(~T, 0, 0n, 1, R.DL{0, 1, 0, 0n, 0, 0, 0n, 1, ALeaf{None{}}, ALeaf{0}, ALeaf{0}}, ALeaf{g}, 0, g, x, _)) == (freed(~T, g), Done{x}) : D.DList<T> & Result<&2, &2, E.Error, T>}
  {==}

def reuse_slot(~T: Data, +g: U32, +y: T) -> {D.push_back(~T, freed(~T, g), y) == (single(~T, U32.inc(g), y), E.H{0, 0, U32.inc(g)}) : D.DList<T> & E.Handle}:
  {==}

def stale_after_reuse(~T: Data, +g: U32, +y: T) -> {D.get(~T, single(~T, U32.inc(g), y), E.H{0, 0, g}) == (single(~T, U32.inc(g), y), Fail{E.StaleHandle{}}) : D.DList<T> & Result<&2, &2, E.Error, T>}:
  %Equal.sym(Bool, U32.is_eq(U32.inc(g), g), False{}, inc_distinct(g)) : {D.project_value(~T, D.checked(~T, E.Get{E.H{0, 0, g}}, (single(~T, U32.inc(g), y), D.generation_error(_)))) == (single(~T, U32.inc(g), y), Fail{E.StaleHandle{}}) : D.DList<T> & Result<&2, &2, E.Error, T>}
  {==}

def new_handle_works(~T: Data, +g: U32, +y: T) -> {D.get(~T, single(~T, g, y), E.H{0, 0, g}) == (single(~T, g, y), Done{y}) : D.DList<T> & Result<&2, &2, E.Error, T>}:
  %Equal.sym(Bool, U32.is_eq(g, g), True{}, U.eq_refl(g)) : {D.project_value(~T, D.checked(~T, E.Get{E.H{0, 0, g}}, (single(~T, g, y), D.generation_error(_)))) == (single(~T, g, y), Done{y}) : D.DList<T> & Result<&2, &2, E.Error, T>}
  {==}

def no_wrap(~T: Data, +x: T) -> {D.remove(~T, single(~T, 4294967295, x), E.H{0, 0, 4294967295}) == (exhausted(~T), Done{x}) : D.DList<T> & Result<&2, &2, E.Error, T>}:
  {==}

def retired_stays_stale(~T: Data) -> {D.get(~T, exhausted(~T), E.H{0, 0, 4294967295}) == (exhausted(~T), Fail{E.StaleHandle{}}) : D.DList<T> & Result<&2, &2, E.Error, T>}:
  {==}
