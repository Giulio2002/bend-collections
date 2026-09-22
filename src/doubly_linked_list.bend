import Base
import ./internal/dlist_storage.bend as R
import ../types/internal_dlist.bend as I
import ../types/doubly_linked_list.bend as E

# Public generational handles over the shared indexed DLL storage.
# Removed slots are reused. A generation at UINT32_MAX is retired forever
# instead of wrapping; capacity therefore follows peak live + exhausted slots.
# Values are released by remove, but the pool keeps capacity for later use.
type DList<-T: Data> is Type:
  DL{tag: U32, depth: Nat, cap: U32, storage: R.DList<T>, generations: Array<U32>}

def new(~T: Data, +tag: U32) -> DList<T>:
  DL{tag, 0n, 1, R.new(~T, tag), Array.new(U32, 0n, 0)}

def error(e: I.Error) -> E.Error:
  match e:
    case I.ForeignHandle{}:
      E.ForeignHandle{}
    case I.StaleHandle{}:
      E.StaleHandle{}

def old_handle(h: E.Handle) -> I.Handle:
  E.H{tag, id, generation} = h
  I.H{tag, id}

def inserted_gen(~T: Data, +tag: U32, depth: Nat, cap: U32, raw: R.DList<T>, id: U32, r: Array<U32> & U32) -> DList<T> & E.Handle:
  (gens, generation) = r
  (DL{tag, depth, cap, raw, gens}, E.H{tag, id, generation})

def inserted_room(~T: Data, +tag: U32, +depth: Nat, +cap: U32, raw: R.DList<T>, gens: Array<U32>, +id: U32, grow: Bool) -> DList<T> & E.Handle:
  match grow:
    case False{}:
      inserted_gen(~T, tag, depth, cap, raw, id, Array.get(U32, gens, id))
    case True{}:
      inserted_gen(~T, tag, 1n+depth, U32.shl(cap), raw, id, Array.get(U32, ANode{gens, Array.new(U32, depth, 0)}, id))

def inserted(~T: Data, +tag: U32, depth: Nat, +cap: U32, gens: Array<U32>, r: R.DList<T> & I.Handle) -> DList<T> & E.Handle:
  (raw, I.H{rtag, +id}) = r
  inserted_room(~T, tag, depth, cap, raw, gens, id, U32.is_eq(id, cap))

def push_front(~T: Data, s: DList<T>, x: T) -> DList<T> & E.Handle:
  DL{+tag, depth, +cap, raw, gens} = s
  inserted(~T, tag, depth, cap, gens, R.push_front_free(~T, raw, x))

def push_back(~T: Data, s: DList<T>, x: T) -> DList<T> & E.Handle:
  DL{+tag, depth, +cap, raw, gens} = s
  inserted(~T, tag, depth, cap, gens, R.push_back_free(~T, raw, x))

def generation_error(same: Bool) -> Maybe<&2, E.Error>:
  match same:
    case True{}:
      None{}
    case False{}:
      Some{E.StaleHandle{}}

def valid_gen(~T: Data, tag: U32, depth: Nat, cap: U32, raw: R.DList<T>, expected: U32, r: Array<U32> & U32) -> DList<T> & Maybe<&2, E.Error>:
  (gens, actual) = r
  (DL{tag, depth, cap, raw, gens}, generation_error(U32.is_eq(actual, expected)))

def valid_bounds(~T: Data, tag: U32, depth: Nat, cap: U32, raw: R.DList<T>, gens: Array<U32>, id: U32, expected: U32, same: Bool, inside: Bool) -> DList<T> & Maybe<&2, E.Error>:
  match same inside:
    case False{} _:
      (DL{tag, depth, cap, raw, gens}, Some{E.ForeignHandle{}})
    case True{} False{}:
      (DL{tag, depth, cap, raw, gens}, Some{E.StaleHandle{}})
    case True{} True{}:
      valid_gen(~T, tag, depth, cap, raw, expected, Array.get(U32, gens, id))

def validate(~T: Data, s: DList<T>, h: E.Handle) -> DList<T> & Maybe<&2, E.Error>:
  DL{+tag, depth, +cap, raw, gens} = s
  E.H{owner, +id, expected} = h
  valid_bounds(~T, tag, depth, cap, raw, gens, id, expected, U32.is_eq(tag, owner), U32.is_lt(id, cap))

def item_result(~T: Data, r: Result<&2, &2, I.Error, T>) -> Result<&2, &2, E.Error, T>:
  match r:
    case Done{x}:
      Done{x}
    case Fail{e}:
      Fail{error(e)}

def value_result(~T: Data, tag: U32, depth: Nat, cap: U32, gens: Array<U32>, r: R.DList<T> & Result<&2, &2, I.Error, T>) -> DList<T> & E.Obs<T>:
  (raw, result) = r
  (DL{tag, depth, cap, raw, gens}, E.OVal{item_result(~T, result)})

def unit_result(~T: Data, tag: U32, depth: Nat, cap: U32, gens: Array<U32>, r: R.DList<T> & Result<&2, &2, I.Error, Unit>) -> DList<T> & E.Obs<T>:
  (raw, result) = r
  (DL{tag, depth, cap, raw, gens}, E.OUnit{item_result(~Unit, result)})

def retire(~T: Data, tag: U32, depth: Nat, cap: U32, raw: R.DList<T>, gens: Array<U32>, +id: U32, +generation: U32, v: T, exhausted: Bool) -> DList<T> & E.Obs<T>:
  match exhausted:
    case True{}:
      (DL{tag, depth, cap, raw, gens}, E.OVal{Done{v}})
    case False{}:
      (DL{tag, depth, cap, R.recycle_slot(~T, raw, id), Array.set(U32, gens, id, U32.inc(generation))}, E.OVal{Done{v}})

def removed(~T: Data, tag: U32, depth: Nat, cap: U32, gens: Array<U32>, id: U32, +generation: U32, r: R.DList<T> & Result<&2, &2, I.Error, T>) -> DList<T> & E.Obs<T>:
  match r:
    case Tuple{raw, Fail{e}}:
      (DL{tag, depth, cap, raw, gens}, E.OVal{Fail{error(e)}})
    case Tuple{raw, Done{v}}:
      retire(~T, tag, depth, cap, raw, gens, id, generation, v, U32.is_eq(generation, 4294967295))

def relative_done(~T: Data, r: DList<T> & E.Handle) -> DList<T> & E.Obs<T>:
  (s, h) = r
  (s, E.OInsert{Done{h}})

def relative_result(~T: Data, +tag: U32, depth: Nat, +cap: U32, gens: Array<U32>, r: R.DList<T> & Result<&2, &2, I.Error, I.Handle>) -> DList<T> & E.Obs<T>:
  match r:
    case Tuple{raw, Fail{e}}:
      (DL{tag, depth, cap, raw, gens}, E.OInsert{Fail{error(e)}})
    case Tuple{raw, Done{I.H{owner, +id}}}:
      relative_done(~T, inserted_room(~T, tag, depth, cap, raw, gens, id, U32.is_eq(id, cap)))

def neighbour_gen(~T: Data, tag: U32, depth: Nat, cap: U32, raw: R.DList<T>, owner: U32, id: U32, r: Array<U32> & U32) -> DList<T> & E.Obs<T>:
  (gens, generation) = r
  (DL{tag, depth, cap, raw, gens}, E.ONbr{Done{Some{E.H{owner, id, generation}}}})

def neighbour_result(~T: Data, tag: U32, depth: Nat, cap: U32, gens: Array<U32>, r: R.DList<T> & Result<&2, &2, I.Error, Maybe<&2, I.Handle>>) -> DList<T> & E.Obs<T>:
  match r:
    case Tuple{raw, Fail{e}}:
      (DL{tag, depth, cap, raw, gens}, E.ONbr{Fail{error(e)}})
    case Tuple{raw, Done{None{}}}:
      (DL{tag, depth, cap, raw, gens}, E.ONbr{Done{None{}}})
    case Tuple{raw, Done{Some{I.H{owner, +id}}}}:
      neighbour_gen(~T, tag, depth, cap, raw, owner, id, Array.get(U32, gens, id))

def length_result(~T: Data, tag: U32, depth: Nat, cap: U32, gens: Array<U32>, r: R.DList<T> & Nat) -> DList<T> & E.Obs<T>:
  (raw, n) = r
  (DL{tag, depth, cap, raw, gens}, E.ONat{n})

def list_result(~T: Data, tag: U32, depth: Nat, cap: U32, gens: Array<U32>, r: R.DList<T> & List<&2, T>) -> DList<T> & E.Obs<T>:
  (raw, xs) = r
  (DL{tag, depth, cap, raw, gens}, E.OList{xs})

def pushed_obs(~T: Data, r: DList<T> & E.Handle) -> DList<T> & E.Obs<T>:
  (s, h) = r
  (s, E.OHandle{h})

def dispatch(~T: Data, s: DList<T>, op: E.Op<T>) -> DList<T> & E.Obs<T>:
  DL{+tag, +depth, +cap, raw, gens} = s
  match op:
    case E.Length{}:
      length_result(~T, tag, depth, cap, gens, R.length(~T, raw))
    case E.ToList{}:
      list_result(~T, tag, depth, cap, gens, R.to_list(~T, raw))
    case E.PushFront{x}:
      pushed_obs(~T, inserted(~T, tag, depth, cap, gens, R.push_front_free(~T, raw, x)))
    case E.PushBack{x}:
      pushed_obs(~T, inserted(~T, tag, depth, cap, gens, R.push_back_free(~T, raw, x)))
    case E.Get{h}:
      value_result(~T, tag, depth, cap, gens, R.get(~T, raw, old_handle(h)))
    case E.Set{h, x}:
      unit_result(~T, tag, depth, cap, gens, R.set(~T, raw, old_handle(h), x))
    case E.Remove{E.H{+owner, +id, generation}}:
      removed(~T, tag, depth, cap, gens, id, generation, R.remove(~T, raw, I.H{owner, id}))
    case E.Next{h}:
      neighbour_result(~T, tag, depth, cap, gens, R.next(~T, raw, old_handle(h)))
    case E.Prev{h}:
      neighbour_result(~T, tag, depth, cap, gens, R.prev(~T, raw, old_handle(h)))
    case E.InsertBefore{h, x}:
      relative_result(~T, tag, depth, cap, gens, R.insert_before_reuse(~T, raw, old_handle(h), x))
    case E.InsertAfter{h, x}:
      relative_result(~T, tag, depth, cap, gens, R.insert_after_reuse(~T, raw, old_handle(h), x))

def op_handle(~T: Data, op: E.Op<T>) -> Maybe<&2, E.Handle>:
  match op:
    case E.Get{h}:
      Some{h}
    case E.Set{h, x}:
      Some{h}
    case E.Remove{h}:
      Some{h}
    case E.Next{h}:
      Some{h}
    case E.Prev{h}:
      Some{h}
    case E.InsertBefore{h, x}:
      Some{h}
    case E.InsertAfter{h, x}:
      Some{h}
    case _:
      None{}

def failed(~T: Data, op: E.Op<T>, e: E.Error) -> E.Obs<T>:
  match op:
    case E.Set{h, x}:
      E.OUnit{Fail{e}}
    case E.Next{h}:
      E.ONbr{Fail{e}}
    case E.Prev{h}:
      E.ONbr{Fail{e}}
    case E.InsertBefore{h, x}:
      E.OInsert{Fail{e}}
    case E.InsertAfter{h, x}:
      E.OInsert{Fail{e}}
    case _:
      E.OVal{Fail{e}}

def checked(~T: Data, op: E.Op<T>, r: DList<T> & Maybe<&2, E.Error>) -> DList<T> & E.Obs<T>:
  match r:
    case Tuple{s, None{}}:
      dispatch(~T, s, op)
    case Tuple{s, Some{e}}:
      (s, failed(~T, op, e))

def step_handle(~T: Data, s: DList<T>, op: E.Op<T>, h: Maybe<&2, E.Handle>) -> DList<T> & E.Obs<T>:
  match h:
    case None{}:
      dispatch(~T, s, op)
    case Some{handle}:
      checked(~T, op, validate(~T, s, handle))

def step(~T: Data, s: DList<T>, +op: E.Op<T>) -> DList<T> & E.Obs<T>:
  step_handle(~T, s, op, op_handle(~T, op))

def project_value(~T: Data, r: DList<T> & E.Obs<T>) -> DList<T> & Result<&2, &2, E.Error, T>:
  match r:
    case Tuple{s, E.OVal{x}}:
      (s, x)
    case Tuple{s, other}:
      (s, Fail{E.StaleHandle{}})

def project_unit(~T: Data, r: DList<T> & E.Obs<T>) -> DList<T> & Result<&2, &2, E.Error, Unit>:
  match r:
    case Tuple{s, E.OUnit{x}}:
      (s, x)
    case Tuple{s, other}:
      (s, Fail{E.StaleHandle{}})

def project_insert(~T: Data, r: DList<T> & E.Obs<T>) -> DList<T> & Result<&2, &2, E.Error, E.Handle>:
  match r:
    case Tuple{s, E.OInsert{x}}:
      (s, x)
    case Tuple{s, other}:
      (s, Fail{E.StaleHandle{}})

def project_neighbour(~T: Data, r: DList<T> & E.Obs<T>) -> DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>:
  match r:
    case Tuple{s, E.ONbr{x}}:
      (s, x)
    case Tuple{s, other}:
      (s, Fail{E.StaleHandle{}})

def project_length(~T: Data, r: DList<T> & E.Obs<T>) -> DList<T> & Nat:
  match r:
    case Tuple{s, E.ONat{x}}:
      (s, x)
    case Tuple{s, other}:
      (s, 0n)

def project_list(~T: Data, r: DList<T> & E.Obs<T>) -> DList<T> & List<&2, T>:
  match r:
    case Tuple{s, E.OList{x}}:
      (s, x)
    case Tuple{s, other}:
      (s, Nil{})

def length_direct_result(~T: Data, tag: U32, depth: Nat, cap: U32, gens: Array<U32>, r: R.DList<T> & Nat) -> DList<T> & Nat:
  (raw, n) = r
  (DL{tag, depth, cap, raw, gens}, n)

def length(~T: Data, s: DList<T>) -> DList<T> & Nat:
  DL{tag, depth, cap, raw, gens} = s
  length_direct_result(~T, tag, depth, cap, gens, R.length(~T, raw))

def to_list_direct_result(~T: Data, tag: U32, depth: Nat, cap: U32, gens: Array<U32>, r: R.DList<T> & List<&2, T>) -> DList<T> & List<&2, T>:
  (raw, xs) = r
  (DL{tag, depth, cap, raw, gens}, xs)

def to_list(~T: Data, s: DList<T>) -> DList<T> & List<&2, T>:
  DL{tag, depth, cap, raw, gens} = s
  to_list_direct_result(~T, tag, depth, cap, gens, R.to_list(~T, raw))

# Direct public read path. Keep generation validation, but avoid allocating an
# Op/Obs envelope and executing the general trace dispatcher for one get.
def get_result(~T: Data, tag: U32, depth: Nat, cap: U32, gens: Array<U32>, r: R.DList<T> & Result<&2, &2, I.Error, T>) -> DList<T> & Result<&2, &2, E.Error, T>:
  (raw, result) = r
  (DL{tag, depth, cap, raw, gens}, item_result(~T, result))

def get_ready(~T: Data, h: E.Handle, r: DList<T> & Maybe<&2, E.Error>) -> DList<T> & Result<&2, &2, E.Error, T>:
  match r:
    case Tuple{s, Some{e}}:
      (s, Fail{e})
    case Tuple{DL{tag, depth, cap, raw, gens}, None{}}:
      get_result(~T, tag, depth, cap, gens, R.get(~T, raw, old_handle(h)))

def get(~T: Data, s: DList<T>, +h: E.Handle) -> DList<T> & Result<&2, &2, E.Error, T>:
  get_ready(~T, h, validate(~T, s, h))

def remove_ready(~T: Data, h: E.Handle, r: DList<T> & Maybe<&2, E.Error>) -> DList<T> & Result<&2, &2, E.Error, T>:
  match h r:
    case E.H{owner, id, generation} Tuple{s, Some{e}}:
      (s, Fail{e})
    case E.H{+owner, +id, generation} Tuple{DL{tag, depth, cap, raw, gens}, None{}}:
      project_value(~T, removed(~T, tag, depth, cap, gens, id, generation, R.remove(~T, raw, I.H{owner, id})))

def remove(~T: Data, s: DList<T>, +h: E.Handle) -> DList<T> & Result<&2, &2, E.Error, T>:
  remove_ready(~T, h, validate(~T, s, h))

def set_result(~T: Data, tag: U32, depth: Nat, cap: U32, gens: Array<U32>, r: R.DList<T> & Result<&2, &2, I.Error, Unit>) -> DList<T> & Result<&2, &2, E.Error, Unit>:
  (raw, result) = r
  (DL{tag, depth, cap, raw, gens}, item_result(~Unit, result))

def set_ready(~T: Data, +h: E.Handle, x: T, r: DList<T> & Maybe<&2, E.Error>) -> DList<T> & Result<&2, &2, E.Error, Unit>:
  match r:
    case Tuple{s, Some{e}}:
      (s, Fail{e})
    case Tuple{DL{tag, depth, cap, raw, gens}, None{}}:
      set_result(~T, tag, depth, cap, gens, R.set(~T, raw, old_handle(h), x))

def set(~T: Data, s: DList<T>, +h: E.Handle, x: T) -> DList<T> & Result<&2, &2, E.Error, Unit>:
  set_ready(~T, h, x, validate(~T, s, h))

def next_ready(~T: Data, +h: E.Handle, r: DList<T> & Maybe<&2, E.Error>) -> DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>:
  match r:
    case Tuple{s, Some{e}}:
      (s, Fail{e})
    case Tuple{DL{tag, depth, cap, raw, gens}, None{}}:
      project_neighbour(~T, neighbour_result(~T, tag, depth, cap, gens, R.next(~T, raw, old_handle(h))))

def next(~T: Data, s: DList<T>, +h: E.Handle) -> DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>:
  next_ready(~T, h, validate(~T, s, h))

def prev_ready(~T: Data, +h: E.Handle, r: DList<T> & Maybe<&2, E.Error>) -> DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>:
  match r:
    case Tuple{s, Some{e}}:
      (s, Fail{e})
    case Tuple{DL{tag, depth, cap, raw, gens}, None{}}:
      project_neighbour(~T, neighbour_result(~T, tag, depth, cap, gens, R.prev(~T, raw, old_handle(h))))

def prev(~T: Data, s: DList<T>, +h: E.Handle) -> DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>:
  prev_ready(~T, h, validate(~T, s, h))

def insert_before_ready(~T: Data, +h: E.Handle, +x: T, r: DList<T> & Maybe<&2, E.Error>) -> DList<T> & Result<&2, &2, E.Error, E.Handle>:
  match r:
    case Tuple{s, Some{e}}:
      (s, Fail{e})
    case Tuple{DL{tag, depth, cap, raw, gens}, None{}}:
      project_insert(~T, relative_result(~T, tag, depth, cap, gens, R.insert_before_reuse(~T, raw, old_handle(h), x)))

def insert_before(~T: Data, s: DList<T>, +h: E.Handle, x: T) -> DList<T> & Result<&2, &2, E.Error, E.Handle>:
  insert_before_ready(~T, h, x, validate(~T, s, h))

def insert_after_ready(~T: Data, +h: E.Handle, +x: T, r: DList<T> & Maybe<&2, E.Error>) -> DList<T> & Result<&2, &2, E.Error, E.Handle>:
  match r:
    case Tuple{s, Some{e}}:
      (s, Fail{e})
    case Tuple{DL{tag, depth, cap, raw, gens}, None{}}:
      project_insert(~T, relative_result(~T, tag, depth, cap, gens, R.insert_after_reuse(~T, raw, old_handle(h), x)))

def insert_after(~T: Data, s: DList<T>, +h: E.Handle, x: T) -> DList<T> & Result<&2, &2, E.Error, E.Handle>:
  insert_after_ready(~T, h, x, validate(~T, s, h))

def record(~T: Data, acc: List<&2, E.Obs<T>>, r: DList<T> & E.Obs<T>) -> DList<T> & List<&2, E.Obs<T>>:
  (s, o) = r
  (s, Con{o, acc})

def step_acc(~T: Data, op: E.Op<T>, st: DList<T> & List<&2, E.Obs<T>>) -> DList<T> & List<&2, E.Obs<T>>:
  (s, acc) = st
  record(~T, acc, step(~T, s, op))

def run_acc(~T: Data, ops: List<&2, E.Op<T>>, st: DList<T> & List<&2, E.Obs<T>>) -> DList<T> & List<&2, E.Obs<T>>:
  match ops:
    case Nil{}:
      st
    case Con{op, rest}:
      run_acc(~T, rest, step_acc(~T, op, st))

def finish(~T: Data, st: DList<T> & List<&2, E.Obs<T>>) -> DList<T> & List<&2, E.Obs<T>>:
  (s, acc) = st
  (s, List.reverse(&2, E.Obs<T>, acc))

def run(~T: Data, ops: List<&2, E.Op<T>>, s: DList<T>) -> DList<T> & List<&2, E.Obs<T>>:
  finish(~T, run_acc(~T, ops, (s, Nil{})))
