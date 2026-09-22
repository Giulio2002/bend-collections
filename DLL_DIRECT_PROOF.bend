import Base
import ./src/doubly_linked_list.bend as D
import ./src/internal/dlist_storage.bend as R
import ./types/doubly_linked_list.bend as E
import ./types/internal_dlist.bend as I

def result_same(~T: Data, tag: U32, depth: Nat, cap: U32, gens: Array<U32>, r: R.DList<T> & Result<&2, &2, I.Error, T>) -> {D.get_result(~T, tag, depth, cap, gens, r) == D.project_value(~T, D.value_result(~T, tag, depth, cap, gens, r)) : D.DList<T> & Result<&2, &2, E.Error, T>}:
  match r:
    case Tuple{raw, result}:
      {==}

def ready_same(~T: Data, +h: E.Handle, r: D.DList<T> & Maybe<&2, E.Error>) -> {D.get_ready(~T, h, r) == D.project_value(~T, D.checked(~T, E.Get{h}, r)) : D.DList<T> & Result<&2, &2, E.Error, T>}:
  match r:
    case Tuple{D.DL{tag, depth, cap, raw, gens}, Some{e}}:
      {==}
    case Tuple{D.DL{tag, depth, cap, raw, gens}, None{}}:
      result_same(~T, tag, depth, cap, gens, R.get(~T, raw, D.old_handle(h)))

def get_same(~T: Data, s: D.DList<T>, +h: E.Handle) -> {D.get(~T, s, h) == D.project_value(~T, D.step(~T, s, E.Get{h})) : D.DList<T> & Result<&2, &2, E.Error, T>}:
  ready_same(~T, h, D.validate(~T, s, h))

def get_u32(s: D.DList<U32>, +h: E.Handle) -> {D.get(~U32, s, h) == D.project_value(~U32, D.step(~U32, s, E.Get{h})) : D.DList<U32> & Result<&2, &2, E.Error, U32>}:
  get_same(~U32, s, h)

def get_string(s: D.DList<String>, +h: E.Handle) -> {D.get(~String, s, h) == D.project_value(~String, D.step(~String, s, E.Get{h})) : D.DList<String> & Result<&2, &2, E.Error, String>}:
  get_same(~String, s, h)

def set_result_same(~T: Data, tag: U32, depth: Nat, cap: U32, gens: Array<U32>, r: R.DList<T> & Result<&2, &2, I.Error, Unit>) -> {D.set_result(~T, tag, depth, cap, gens, r) == D.project_unit(~T, D.unit_result(~T, tag, depth, cap, gens, r)) : D.DList<T> & Result<&2, &2, E.Error, Unit>}:
  match r:
    case Tuple{raw, result}:
      {==}

def set_ready_same(~T: Data, +h: E.Handle, +x: T, r: D.DList<T> & Maybe<&2, E.Error>) -> {D.set_ready(~T, h, x, r) == D.project_unit(~T, D.checked(~T, E.Set{h, x}, r)) : D.DList<T> & Result<&2, &2, E.Error, Unit>}:
  match r:
    case Tuple{D.DL{tag, depth, cap, raw, gens}, Some{e}}:
      {==}
    case Tuple{D.DL{tag, depth, cap, raw, gens}, None{}}:
      set_result_same(~T, tag, depth, cap, gens, R.set(~T, raw, D.old_handle(h), x))

def set_same(~T: Data, s: D.DList<T>, +h: E.Handle, +x: T) -> {D.set(~T, s, h, x) == D.project_unit(~T, D.step(~T, s, E.Set{h, x})) : D.DList<T> & Result<&2, &2, E.Error, Unit>}:
  set_ready_same(~T, h, x, D.validate(~T, s, h))

def set_u32(s: D.DList<U32>, +h: E.Handle, +x: U32) -> {D.set(~U32, s, h, x) == D.project_unit(~U32, D.step(~U32, s, E.Set{h, x})) : D.DList<U32> & Result<&2, &2, E.Error, Unit>}:
  set_same(~U32, s, h, x)

def set_string(s: D.DList<String>, +h: E.Handle, +x: String) -> {D.set(~String, s, h, x) == D.project_unit(~String, D.step(~String, s, E.Set{h, x})) : D.DList<String> & Result<&2, &2, E.Error, Unit>}:
  set_same(~String, s, h, x)

def length_result_same(tag: U32, depth: Nat, cap: U32, gens: Array<U32>, r: R.DList<U32> & Nat) -> {D.length_direct_result(~U32, tag, depth, cap, gens, r) == D.project_length(~U32, D.length_result(~U32, tag, depth, cap, gens, r)) : D.DList<U32> & Nat}:
  match r:
    case Tuple{raw, x}:
      {==}

def length_same(s: D.DList<U32>) -> {D.length(~U32, s) == D.project_length(~U32, D.step(~U32, s, E.Length{})) : D.DList<U32> & Nat}:
  match s:
    case D.DL{tag, depth, cap, raw, gens}:
      length_result_same(tag, depth, cap, gens, R.length(~U32, raw))

def to_list_result_same(tag: U32, depth: Nat, cap: U32, gens: Array<U32>, r: R.DList<U32> & List<&2, U32>) -> {D.to_list_direct_result(~U32, tag, depth, cap, gens, r) == D.project_list(~U32, D.list_result(~U32, tag, depth, cap, gens, r)) : D.DList<U32> & List<&2, U32>}:
  match r:
    case Tuple{raw, x}:
      {==}

def to_list_same(s: D.DList<U32>) -> {D.to_list(~U32, s) == D.project_list(~U32, D.step(~U32, s, E.ToList{})) : D.DList<U32> & List<&2, U32>}:
  match s:
    case D.DL{tag, depth, cap, raw, gens}:
      to_list_result_same(tag, depth, cap, gens, R.to_list(~U32, raw))

def next_ready_same(~T: Data, +h: E.Handle, r: D.DList<T> & Maybe<&2, E.Error>) -> {D.next_ready(~T, h, r) == D.project_neighbour(~T, D.checked(~T, E.Next{h}, r)) : D.DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>}:
  match r:
    case Tuple{D.DL{tag, depth, cap, raw, gens}, Some{e}}:
      {==}
    case Tuple{D.DL{tag, depth, cap, raw, gens}, None{}}:
      {==}

def next_U32(s: D.DList<U32>, +h: E.Handle) -> {D.next(~U32, s, h) == D.project_neighbour(~U32, D.step(~U32, s, E.Next{h})) : D.DList<U32> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>}:
  next_ready_same(~U32, h, D.validate(~U32, s, h))

def next_String(s: D.DList<String>, +h: E.Handle) -> {D.next(~String, s, h) == D.project_neighbour(~String, D.step(~String, s, E.Next{h})) : D.DList<String> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>}:
  next_ready_same(~String, h, D.validate(~String, s, h))

def prev_ready_same(~T: Data, +h: E.Handle, r: D.DList<T> & Maybe<&2, E.Error>) -> {D.prev_ready(~T, h, r) == D.project_neighbour(~T, D.checked(~T, E.Prev{h}, r)) : D.DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>}:
  match r:
    case Tuple{D.DL{tag, depth, cap, raw, gens}, Some{e}}:
      {==}
    case Tuple{D.DL{tag, depth, cap, raw, gens}, None{}}:
      {==}

def prev_U32(s: D.DList<U32>, +h: E.Handle) -> {D.prev(~U32, s, h) == D.project_neighbour(~U32, D.step(~U32, s, E.Prev{h})) : D.DList<U32> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>}:
  prev_ready_same(~U32, h, D.validate(~U32, s, h))

def prev_String(s: D.DList<String>, +h: E.Handle) -> {D.prev(~String, s, h) == D.project_neighbour(~String, D.step(~String, s, E.Prev{h})) : D.DList<String> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>}:
  prev_ready_same(~String, h, D.validate(~String, s, h))

def insert_before_ready_same(~T: Data, +h: E.Handle, +x: T, r: D.DList<T> & Maybe<&2, E.Error>) -> {D.insert_before_ready(~T, h, x, r) == D.project_insert(~T, D.checked(~T, E.InsertBefore{h, x}, r)) : D.DList<T> & Result<&2, &2, E.Error, E.Handle>}:
  match r:
    case Tuple{D.DL{tag, depth, cap, raw, gens}, Some{e}}:
      {==}
    case Tuple{D.DL{tag, depth, cap, raw, gens}, None{}}:
      {==}

def insert_before_U32(s: D.DList<U32>, +h: E.Handle, +x: U32) -> {D.insert_before(~U32, s, h, x) == D.project_insert(~U32, D.step(~U32, s, E.InsertBefore{h, x})) : D.DList<U32> & Result<&2, &2, E.Error, E.Handle>}:
  insert_before_ready_same(~U32, h, x, D.validate(~U32, s, h))

def insert_before_String(s: D.DList<String>, +h: E.Handle, +x: String) -> {D.insert_before(~String, s, h, x) == D.project_insert(~String, D.step(~String, s, E.InsertBefore{h, x})) : D.DList<String> & Result<&2, &2, E.Error, E.Handle>}:
  insert_before_ready_same(~String, h, x, D.validate(~String, s, h))

def insert_after_ready_same(~T: Data, +h: E.Handle, +x: T, r: D.DList<T> & Maybe<&2, E.Error>) -> {D.insert_after_ready(~T, h, x, r) == D.project_insert(~T, D.checked(~T, E.InsertAfter{h, x}, r)) : D.DList<T> & Result<&2, &2, E.Error, E.Handle>}:
  match r:
    case Tuple{D.DL{tag, depth, cap, raw, gens}, Some{e}}:
      {==}
    case Tuple{D.DL{tag, depth, cap, raw, gens}, None{}}:
      {==}

def insert_after_U32(s: D.DList<U32>, +h: E.Handle, +x: U32) -> {D.insert_after(~U32, s, h, x) == D.project_insert(~U32, D.step(~U32, s, E.InsertAfter{h, x})) : D.DList<U32> & Result<&2, &2, E.Error, E.Handle>}:
  insert_after_ready_same(~U32, h, x, D.validate(~U32, s, h))

def insert_after_String(s: D.DList<String>, +h: E.Handle, +x: String) -> {D.insert_after(~String, s, h, x) == D.project_insert(~String, D.step(~String, s, E.InsertAfter{h, x})) : D.DList<String> & Result<&2, &2, E.Error, E.Handle>}:
  insert_after_ready_same(~String, h, x, D.validate(~String, s, h))

def remove_ready_same(~T: Data, +h: E.Handle, r: D.DList<T> & Maybe<&2, E.Error>) -> {D.remove_ready(~T, h, r) == D.project_value(~T, D.checked(~T, E.Remove{h}, r)) : D.DList<T> & Result<&2, &2, E.Error, T>}:
  match h r:
    case E.H{owner, id, generation} Tuple{D.DL{tag, depth, cap, raw, gens}, Some{e}}:
      {==}
    case E.H{owner, id, generation} Tuple{D.DL{tag, depth, cap, raw, gens}, None{}}:
      {==}

def remove_U32(s: D.DList<U32>, +h: E.Handle) -> {D.remove(~U32, s, h) == D.project_value(~U32, D.step(~U32, s, E.Remove{h})) : D.DList<U32> & Result<&2, &2, E.Error, U32>}:
  remove_ready_same(~U32, h, D.validate(~U32, s, h))

def remove_String(s: D.DList<String>, +h: E.Handle) -> {D.remove(~String, s, h) == D.project_value(~String, D.step(~String, s, E.Remove{h})) : D.DList<String> & Result<&2, &2, E.Error, String>}:
  remove_ready_same(~String, h, D.validate(~String, s, h))

