import Base
import ../../src/containers/doubly_linked_list.bend as D
import ../../src/containers/internal/dlist_storage.bend as R
import ../../src/containers/types/internal_dlist.bend as I
import ../../src/containers/types/doubly_linked_list.bend as E

# The public list's direct operations: each is the projection of the trace
# step on the same operation, for every list and handle.


# ---- the verdict's continuations ----

def gv(~T: Data, +tag: U32, +depth: Nat, +cap: U32, -gens: Array<U32>, p: R.DList<T> & Result<&2, &2, I.Error, T>) -> {D.get_result(~T, tag, depth, cap, gens, p) == D.project_value(~T, D.value_result(~T, tag, depth, cap, gens, p)) : D.DList<T> & Result<&2, &2, E.Error, T>}:
  match p:
    case Tuple{raw, res}:
      {==}

def sv(~T: Data, +tag: U32, +depth: Nat, +cap: U32, -gens: Array<U32>, p: R.DList<T> & Result<&2, &2, I.Error, Unit>) -> {D.set_result(~T, tag, depth, cap, gens, p) == D.project_unit(~T, D.unit_result(~T, tag, depth, cap, gens, p)) : D.DList<T> & Result<&2, &2, E.Error, Unit>}:
  match p:
    case Tuple{raw, res}:
      {==}

def get_m(~T: Data, +h: E.Handle, +tag: U32, +depth: Nat, +cap: U32, raw: R.DList<T>, gens: Array<U32>, m: Maybe<&2, E.Error>) -> {D.get_ready(~T, h, (D.DL{tag, depth, cap, raw, gens}, m)) == D.project_value(~T, D.checked(~T, E.Get{h}, (D.DL{tag, depth, cap, raw, gens}, m))) : D.DList<T> & Result<&2, &2, E.Error, T>}:
  match m:
    case Some{e}:
      {==}
    case None{}:
      gv(~T, tag, depth, cap, gens, R.get(~T, raw, D.old_handle(h)))

def get_s(~T: Data, +h: E.Handle, s: D.DList<T>, m: Maybe<&2, E.Error>) -> {D.get_ready(~T, h, (s, m)) == D.project_value(~T, D.checked(~T, E.Get{h}, (s, m))) : D.DList<T> & Result<&2, &2, E.Error, T>}:
  match s:
    case D.DL{+tag, +depth, +cap, raw, gens}:
      get_m(~T, h, tag, depth, cap, raw, gens, m)

def get_r(~T: Data, +h: E.Handle, r: D.DList<T> & Maybe<&2, E.Error>) -> {D.get_ready(~T, h, r) == D.project_value(~T, D.checked(~T, E.Get{h}, r)) : D.DList<T> & Result<&2, &2, E.Error, T>}:
  match r:
    case Tuple{s, m}:
      get_s(~T, h, s, m)

def set_m(~T: Data, +h: E.Handle, +x: T, +tag: U32, +depth: Nat, +cap: U32, raw: R.DList<T>, gens: Array<U32>, m: Maybe<&2, E.Error>) -> {D.set_ready(~T, h, x, (D.DL{tag, depth, cap, raw, gens}, m)) == D.project_unit(~T, D.checked(~T, E.Set{h, x}, (D.DL{tag, depth, cap, raw, gens}, m))) : D.DList<T> & Result<&2, &2, E.Error, Unit>}:
  match m:
    case Some{e}:
      {==}
    case None{}:
      sv(~T, tag, depth, cap, gens, R.set(~T, raw, D.old_handle(h), x))

def set_s(~T: Data, +h: E.Handle, +x: T, s: D.DList<T>, m: Maybe<&2, E.Error>) -> {D.set_ready(~T, h, x, (s, m)) == D.project_unit(~T, D.checked(~T, E.Set{h, x}, (s, m))) : D.DList<T> & Result<&2, &2, E.Error, Unit>}:
  match s:
    case D.DL{+tag, +depth, +cap, raw, gens}:
      set_m(~T, h, x, tag, depth, cap, raw, gens, m)

def set_r(~T: Data, +h: E.Handle, +x: T, r: D.DList<T> & Maybe<&2, E.Error>) -> {D.set_ready(~T, h, x, r) == D.project_unit(~T, D.checked(~T, E.Set{h, x}, r)) : D.DList<T> & Result<&2, &2, E.Error, Unit>}:
  match r:
    case Tuple{s, m}:
      set_s(~T, h, x, s, m)

def rm_m(~T: Data, +owner: U32, +id: U32, +g: U32, +tag: U32, +depth: Nat, +cap: U32, raw: R.DList<T>, gens: Array<U32>, m: Maybe<&2, E.Error>) -> {D.remove_ready(~T, E.H{owner, id, g}, (D.DL{tag, depth, cap, raw, gens}, m)) == D.project_value(~T, D.checked(~T, E.Remove{E.H{owner, id, g}}, (D.DL{tag, depth, cap, raw, gens}, m))) : D.DList<T> & Result<&2, &2, E.Error, T>}:
  match m:
    case Some{e}:
      {==}
    case None{}:
      {==}

def rm_s(~T: Data, +owner: U32, +id: U32, +g: U32, s: D.DList<T>, m: Maybe<&2, E.Error>) -> {D.remove_ready(~T, E.H{owner, id, g}, (s, m)) == D.project_value(~T, D.checked(~T, E.Remove{E.H{owner, id, g}}, (s, m))) : D.DList<T> & Result<&2, &2, E.Error, T>}:
  match s:
    case D.DL{+tag, +depth, +cap, raw, gens}:
      rm_m(~T, owner, id, g, tag, depth, cap, raw, gens, m)

def rm_r(~T: Data, +h: E.Handle, r: D.DList<T> & Maybe<&2, E.Error>) -> {D.remove_ready(~T, h, r) == D.project_value(~T, D.checked(~T, E.Remove{h}, r)) : D.DList<T> & Result<&2, &2, E.Error, T>}:
  match h r:
    case E.H{+owner, +id, +g} Tuple{s, m}:
      rm_s(~T, owner, id, g, s, m)

def nx_m(~T: Data, +h: E.Handle, +tag: U32, +depth: Nat, +cap: U32, raw: R.DList<T>, gens: Array<U32>, m: Maybe<&2, E.Error>) -> {D.next_ready(~T, h, (D.DL{tag, depth, cap, raw, gens}, m)) == D.project_neighbour(~T, D.checked(~T, E.Next{h}, (D.DL{tag, depth, cap, raw, gens}, m))) : D.DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>}:
  match m:
    case Some{e}:
      {==}
    case None{}:
      {==}

def nx_s(~T: Data, +h: E.Handle, s: D.DList<T>, m: Maybe<&2, E.Error>) -> {D.next_ready(~T, h, (s, m)) == D.project_neighbour(~T, D.checked(~T, E.Next{h}, (s, m))) : D.DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>}:
  match s:
    case D.DL{+tag, +depth, +cap, raw, gens}:
      nx_m(~T, h, tag, depth, cap, raw, gens, m)

def nx_r(~T: Data, +h: E.Handle, r: D.DList<T> & Maybe<&2, E.Error>) -> {D.next_ready(~T, h, r) == D.project_neighbour(~T, D.checked(~T, E.Next{h}, r)) : D.DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>}:
  match r:
    case Tuple{s, m}:
      nx_s(~T, h, s, m)

def pv_m(~T: Data, +h: E.Handle, +tag: U32, +depth: Nat, +cap: U32, raw: R.DList<T>, gens: Array<U32>, m: Maybe<&2, E.Error>) -> {D.prev_ready(~T, h, (D.DL{tag, depth, cap, raw, gens}, m)) == D.project_neighbour(~T, D.checked(~T, E.Prev{h}, (D.DL{tag, depth, cap, raw, gens}, m))) : D.DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>}:
  match m:
    case Some{e}:
      {==}
    case None{}:
      {==}

def pv_s(~T: Data, +h: E.Handle, s: D.DList<T>, m: Maybe<&2, E.Error>) -> {D.prev_ready(~T, h, (s, m)) == D.project_neighbour(~T, D.checked(~T, E.Prev{h}, (s, m))) : D.DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>}:
  match s:
    case D.DL{+tag, +depth, +cap, raw, gens}:
      pv_m(~T, h, tag, depth, cap, raw, gens, m)

def pv_r(~T: Data, +h: E.Handle, r: D.DList<T> & Maybe<&2, E.Error>) -> {D.prev_ready(~T, h, r) == D.project_neighbour(~T, D.checked(~T, E.Prev{h}, r)) : D.DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>}:
  match r:
    case Tuple{s, m}:
      pv_s(~T, h, s, m)

def ib_m(~T: Data, +h: E.Handle, +x: T, +tag: U32, +depth: Nat, +cap: U32, raw: R.DList<T>, gens: Array<U32>, m: Maybe<&2, E.Error>) -> {D.insert_before_ready(~T, h, x, (D.DL{tag, depth, cap, raw, gens}, m)) == D.project_insert(~T, D.checked(~T, E.InsertBefore{h, x}, (D.DL{tag, depth, cap, raw, gens}, m))) : D.DList<T> & Result<&2, &2, E.Error, E.Handle>}:
  match m:
    case Some{e}:
      {==}
    case None{}:
      {==}

def ib_s(~T: Data, +h: E.Handle, +x: T, s: D.DList<T>, m: Maybe<&2, E.Error>) -> {D.insert_before_ready(~T, h, x, (s, m)) == D.project_insert(~T, D.checked(~T, E.InsertBefore{h, x}, (s, m))) : D.DList<T> & Result<&2, &2, E.Error, E.Handle>}:
  match s:
    case D.DL{+tag, +depth, +cap, raw, gens}:
      ib_m(~T, h, x, tag, depth, cap, raw, gens, m)

def ib_r(~T: Data, +h: E.Handle, +x: T, r: D.DList<T> & Maybe<&2, E.Error>) -> {D.insert_before_ready(~T, h, x, r) == D.project_insert(~T, D.checked(~T, E.InsertBefore{h, x}, r)) : D.DList<T> & Result<&2, &2, E.Error, E.Handle>}:
  match r:
    case Tuple{s, m}:
      ib_s(~T, h, x, s, m)

def ia_m(~T: Data, +h: E.Handle, +x: T, +tag: U32, +depth: Nat, +cap: U32, raw: R.DList<T>, gens: Array<U32>, m: Maybe<&2, E.Error>) -> {D.insert_after_ready(~T, h, x, (D.DL{tag, depth, cap, raw, gens}, m)) == D.project_insert(~T, D.checked(~T, E.InsertAfter{h, x}, (D.DL{tag, depth, cap, raw, gens}, m))) : D.DList<T> & Result<&2, &2, E.Error, E.Handle>}:
  match m:
    case Some{e}:
      {==}
    case None{}:
      {==}

def ia_s(~T: Data, +h: E.Handle, +x: T, s: D.DList<T>, m: Maybe<&2, E.Error>) -> {D.insert_after_ready(~T, h, x, (s, m)) == D.project_insert(~T, D.checked(~T, E.InsertAfter{h, x}, (s, m))) : D.DList<T> & Result<&2, &2, E.Error, E.Handle>}:
  match s:
    case D.DL{+tag, +depth, +cap, raw, gens}:
      ia_m(~T, h, x, tag, depth, cap, raw, gens, m)

def ia_r(~T: Data, +h: E.Handle, +x: T, r: D.DList<T> & Maybe<&2, E.Error>) -> {D.insert_after_ready(~T, h, x, r) == D.project_insert(~T, D.checked(~T, E.InsertAfter{h, x}, r)) : D.DList<T> & Result<&2, &2, E.Error, E.Handle>}:
  match r:
    case Tuple{s, m}:
      ia_s(~T, h, x, s, m)

# ---- the direct operations are projected steps ----

def get_step(~T: Data, s: D.DList<T>, +h: E.Handle) -> {D.get(~T, s, h) == D.project_value(~T, D.step(~T, s, E.Get{h})) : D.DList<T> & Result<&2, &2, E.Error, T>}:
  get_r(~T, h, D.validate(~T, s, h))

def set_step(~T: Data, s: D.DList<T>, +h: E.Handle, +x: T) -> {D.set(~T, s, h, x) == D.project_unit(~T, D.step(~T, s, E.Set{h, x})) : D.DList<T> & Result<&2, &2, E.Error, Unit>}:
  set_r(~T, h, x, D.validate(~T, s, h))

def remove_step(~T: Data, s: D.DList<T>, +h: E.Handle) -> {D.remove(~T, s, h) == D.project_value(~T, D.step(~T, s, E.Remove{h})) : D.DList<T> & Result<&2, &2, E.Error, T>}:
  rm_r(~T, h, D.validate(~T, s, h))

def next_step(~T: Data, s: D.DList<T>, +h: E.Handle) -> {D.next(~T, s, h) == D.project_neighbour(~T, D.step(~T, s, E.Next{h})) : D.DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>}:
  nx_r(~T, h, D.validate(~T, s, h))

def prev_step(~T: Data, s: D.DList<T>, +h: E.Handle) -> {D.prev(~T, s, h) == D.project_neighbour(~T, D.step(~T, s, E.Prev{h})) : D.DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>}:
  pv_r(~T, h, D.validate(~T, s, h))

def before_step(~T: Data, s: D.DList<T>, +h: E.Handle, +x: T) -> {D.insert_before(~T, s, h, x) == D.project_insert(~T, D.step(~T, s, E.InsertBefore{h, x})) : D.DList<T> & Result<&2, &2, E.Error, E.Handle>}:
  ib_r(~T, h, x, D.validate(~T, s, h))

def after_step(~T: Data, s: D.DList<T>, +h: E.Handle, +x: T) -> {D.insert_after(~T, s, h, x) == D.project_insert(~T, D.step(~T, s, E.InsertAfter{h, x})) : D.DList<T> & Result<&2, &2, E.Error, E.Handle>}:
  ia_r(~T, h, x, D.validate(~T, s, h))
