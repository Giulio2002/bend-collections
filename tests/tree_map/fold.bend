import Base
import ../../src/balanced_search_tree.bend as M
import ../../src/dynamic_array.bend as D
import ../support/text.bend as X

def rev(a: U32, b: U32) -> Cmp:
  U32.cmp(b, a)

def groups(a: U32, b: U32) -> Cmp:
  U32.cmp(U32.div(a, 10), U32.div(b, 10))

def value(v: Maybe<&2, U32>) -> String:
  match v:
    case None{}:
      "-"
    case Some{x}:
      U32.show(x)

def entry(v: Maybe<&2, M.Entry<U32, U32>>) -> String:
  match v:
    case None{}:
      "-"
    case Some{M.Entry{k, v}}:
      U32.show(k) ++ "=" ++ U32.show(v)

def node(x: M.Node<U32>) -> String:
  match x:
    case M.Free{next}:
      "F," ++ Nat.show(next)
    case M.N{c, l, r, p, k}:
      "N," ++ M.pick(String, c, "1", "0") ++ "," ++ Nat.show(l) ++ "," ++ Nat.show(r) ++ "," ++ Nat.show(p) ++ "," ++ U32.show(k)

def val(~cmp: U32 -> U32 -> Cmp, r: M.TreeMap<U32, U32, cmp> & Maybe<&2, U32>) -> M.TreeMap<U32, U32, cmp> & String:
  (m, v) = r
  (m, value(v))

def ent(~cmp: U32 -> U32 -> Cmp, r: M.TreeMap<U32, U32, cmp> & Maybe<&2, M.Entry<U32, U32>>) -> M.TreeMap<U32, U32, cmp> & String:
  (m, v) = r
  (m, entry(v))

def put(~cmp: U32 -> U32 -> Cmp, r: M.TreeMap<U32, U32, cmp> & Result<&2, &2, M.Rejected<U32, U32>, Maybe<&2, U32>>) -> M.TreeMap<U32, U32, cmp> & String:
  match r:
    case Tuple{m, Done{v}}:
      (m, value(v))
    case Tuple{m, Fail{e}}:
      (m, "ERROR")

def count(~cmp: U32 -> U32 -> Cmp, r: M.TreeMap<U32, U32, cmp> & Nat) -> M.TreeMap<U32, U32, cmp> & String:
  (m, n) = r
  (m, Nat.show(n))

def flag(~cmp: U32 -> U32 -> Cmp, r: M.TreeMap<U32, U32, cmp> & Bool) -> M.TreeMap<U32, U32, cmp> & String:
  (m, b) = r
  (m, M.pick(String, b, "1", "0"))

def slot_value(~cmp: U32 -> U32 -> Cmp, n: String, r: M.TreeMap<U32, U32, cmp> & Maybe<&2, U32>) -> M.TreeMap<U32, U32, cmp> & String:
  (m, v) = r
  (m, n ++ "," ++ value(v))

def slot_node(~cmp: U32 -> U32 -> Cmp, +i: Nat, r: M.TreeMap<U32, U32, cmp> & M.Node<U32>) -> M.TreeMap<U32, U32, cmp> & String:
  (m, n) = r
  slot_value(~cmp, node(n), M.get_id(~U32, ~U32, ~cmp, m, i))

def slot(~cmp: U32 -> U32 -> Cmp, m: M.TreeMap<U32, U32, cmp>, +i: Nat) -> M.TreeMap<U32, U32, cmp> & String:
  slot_node(~cmp, i, M.read(~U32, ~U32, ~cmp, m, i))

def slots(~cmp: U32 -> U32 -> Cmp, fuel: Nat, +i: Nat, acc: String, st: M.TreeMap<U32, U32, cmp> & String) -> M.TreeMap<U32, U32, cmp> & String:
  match fuel st:
    case 0n Tuple{m, v}:
      (m, acc)
    case 1n+f Tuple{m, v}:
      slots(~cmp, f, 1n+i, acc ++ ";" ++ v, slot(~cmp, m, 1n+i))

def dump_count(~cmp: U32 -> U32 -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, values: D.DynArray<&2, Maybe<&2, U32>>, r: D.DynArray<&2, M.Node<U32>> & Nat) -> M.TreeMap<U32, U32, cmp> & String:
  (nodes, +used) = r
  slots(~cmp, used, 1n, Nat.show(n) ++ "," ++ Nat.show(root) ++ "," ++ Nat.show(lo) ++ "," ++ Nat.show(hi) ++ "," ++ Nat.show(free), slot(~cmp, M.TM{n, root, lo, hi, free, nodes, values}, 1n))

def dump(~cmp: U32 -> U32 -> Cmp, m: M.TreeMap<U32, U32, cmp>) -> M.TreeMap<U32, U32, cmp> & String:
  M.TM{+n, +root, +lo, +hi, +free, nodes, values} = m
  dump_count(~cmp, n, root, lo, hi, free, values, D.length(M.Node<U32>, nodes))

def walk_modified(~cmp: U32 -> U32 -> Cmp, r: M.Cursor<U32, U32, cmp> & Maybe<&2, U32>) -> M.Cursor<U32, U32, cmp>:
  (cursor, old) = r
  cursor

def walk_set(~cmp: U32 -> U32 -> Cmp, r: M.Cursor<U32, U32, cmp> & Result<&2, &2, M.Error, U32>) -> M.Cursor<U32, U32, cmp>:
  (cursor, old) = r
  cursor

def walk_action(~cmp: U32 -> U32 -> Cmp, mode: Nat, cursor: M.Cursor<U32, U32, cmp>, v: U32) -> M.Cursor<U32, U32, cmp>:
  match mode:
    case 1n:
      walk_modified(~cmp, M.iterator_remove(~U32, ~U32, ~cmp, cursor))
    case 2n:
      walk_set(~cmp, M.iterator_set_value(~U32, ~U32, ~cmp, cursor, v))
    case _:
      cursor

def walk(~cmp: U32 -> U32 -> Cmp, fuel: Nat, +mode: Nat, out: String, st: M.Cursor<U32, U32, cmp> & Maybe<&2, M.Entry<U32, U32>>) -> M.TreeMap<U32, U32, cmp> & String:
  match fuel st:
    case 0n Tuple{cursor, x}:
      (M.iterator_finish(~U32, ~U32, ~cmp, cursor), "FUEL")
    case 1n+f Tuple{cursor, None{}}:
      (M.iterator_finish(~U32, ~U32, ~cmp, cursor), out)
    case 1n+f Tuple{cursor, Some{M.Entry{+k, +v}}}:
      walk(~cmp, f, mode, out ++ ";" ++ U32.show(k) ++ "=" ++ U32.show(v), M.iterator_next(~U32, ~U32, ~cmp, walk_action(~cmp, mode, cursor, U32.add(v, 1))))

def walk_start(~cmp: U32 -> U32 -> Cmp, mode: Nat, cursor: M.Cursor<U32, U32, cmp>) -> M.TreeMap<U32, U32, cmp> & String:
  walk(~cmp, 10000n, mode, "entries", M.iterator_next(~U32, ~U32, ~cmp, cursor))

def collect(acc: String, key: U32, value: U32) -> String:
  acc ++ ";" ++ U32.show(key) ++ "=" ++ U32.show(value)

def folded_view(~cmp: U32 -> U32 -> Cmp, r: M.View<U32, U32, cmp> & String) -> M.TreeMap<U32, U32, cmp> & String:
  (view, acc) = r
  (M.view_finish(~U32, ~U32, ~cmp, view), acc)

def view_ready(~cmp: U32 -> U32 -> Cmp, r: Result<&1, &1, M.InvalidView<U32, U32, cmp>, M.View<U32, U32, cmp>>) -> M.TreeMap<U32, U32, cmp> & String:
  match r:
    case Fail{M.InvalidView{m, e}}:
      (m, "bounds")
    case Done{view}:
      folded_view(~cmp, M.view_fold(~U32, ~U32, ~cmp, ~String, ~collect, view, "entries"))

def view_put_result(~cmp: U32 -> U32 -> Cmp, r: M.View<U32, U32, cmp> & Result<&2, &2, M.Rejected<U32, U32>, Maybe<&2, U32>>) -> M.TreeMap<U32, U32, cmp> & String:
  match r:
    case Tuple{view, Done{v}}:
      (M.view_finish(~U32, ~U32, ~cmp, view), value(v))
    case Tuple{view, Fail{e}}:
      (M.view_finish(~U32, ~U32, ~cmp, view), "range")

def view_val_result(~cmp: U32 -> U32 -> Cmp, r: M.View<U32, U32, cmp> & Maybe<&2, U32>) -> M.TreeMap<U32, U32, cmp> & String:
  (view, v) = r
  (M.view_finish(~U32, ~U32, ~cmp, view), value(v))

def default_result(~cmp: U32 -> U32 -> Cmp, r: M.TreeMap<U32, U32, cmp> & U32) -> M.TreeMap<U32, U32, cmp> & String:
  (m, v) = r
  (m, U32.show(v))

def vent(~cmp: U32 -> U32 -> Cmp, r: M.View<U32, U32, cmp> & Maybe<&2, M.Entry<U32, U32>>) -> M.TreeMap<U32, U32, cmp> & String:
  (view, x) = r
  (M.view_finish(~U32, ~U32, ~cmp, view), entry(x))

def vcount(~cmp: U32 -> U32 -> Cmp, r: M.View<U32, U32, cmp> & Nat) -> M.TreeMap<U32, U32, cmp> & String:
  (view, x) = r
  (M.view_finish(~U32, ~U32, ~cmp, view), Nat.show(x))

def vflag(~cmp: U32 -> U32 -> Cmp, r: M.View<U32, U32, cmp> & Bool) -> M.TreeMap<U32, U32, cmp> & String:
  (view, x) = r
  (M.view_finish(~U32, ~U32, ~cmp, view), M.pick(String, x, "1", "0"))

def cflag(~cmp: U32 -> U32 -> Cmp, r: M.Cursor<U32, U32, cmp> & Bool) -> M.TreeMap<U32, U32, cmp> & String:
  (cursor, x) = r
  (M.iterator_finish(~U32, ~U32, ~cmp, cursor), M.pick(String, x, "1", "0"))

def walk_key(~cmp: U32 -> U32 -> Cmp, fuel: Nat, out: String, st: M.Cursor<U32, U32, cmp> & Maybe<&2, U32>) -> M.TreeMap<U32, U32, cmp> & String:
  match fuel st:
    case 0n Tuple{cursor, x}:
      (M.iterator_finish(~U32, ~U32, ~cmp, cursor), "FUEL")
    case 1n+f Tuple{cursor, None{}}:
      (M.iterator_finish(~U32, ~U32, ~cmp, cursor), out)
    case 1n+f Tuple{cursor, Some{v}}:
      walk_key(~cmp, f, out ++ ";" ++ U32.show(v), M.iterator_next_key(~U32, ~U32, ~cmp, cursor))

def walk_value(~cmp: U32 -> U32 -> Cmp, fuel: Nat, out: String, st: M.Cursor<U32, U32, cmp> & Maybe<&2, U32>) -> M.TreeMap<U32, U32, cmp> & String:
  match fuel st:
    case 0n Tuple{cursor, x}:
      (M.iterator_finish(~U32, ~U32, ~cmp, cursor), "FUEL")
    case 1n+f Tuple{cursor, None{}}:
      (M.iterator_finish(~U32, ~U32, ~cmp, cursor), out)
    case 1n+f Tuple{cursor, Some{v}}:
      walk_value(~cmp, f, out ++ ";" ++ U32.show(v), M.iterator_next_value(~U32, ~U32, ~cmp, cursor))

def bounded_fold(~cmp: U32 -> U32 -> Cmp, m: M.TreeMap<U32, U32, cmp>, lower: M.Bound<U32>, upper: M.Bound<U32>, descending: Bool) -> M.TreeMap<U32, U32, cmp> & String:
  folded_view(~cmp, M.view_fold(~U32, ~U32, ~cmp, ~String, ~collect, M.View{m, lower, upper, descending}, "entries"))

def step(~cmp: U32 -> U32 -> Cmp, op: Nat, m: M.TreeMap<U32, U32, cmp>, k: U32, +v: U32) -> M.TreeMap<U32, U32, cmp> & String:
  match op:
    case 0n:
      put(~cmp, M.put(~U32, ~U32, ~cmp, m, k, v))
    case 1n:
      val(~cmp, M.get(~U32, ~U32, ~cmp, m, k))
    case 2n:
      val(~cmp, M.remove(~U32, ~U32, ~cmp, m, k))
    case 3n:
      count(~cmp, M.size(~U32, ~U32, ~cmp, m))
    case 4n:
      (M.clear(~U32, ~U32, ~cmp, m), "ok")
    case 5n:
      flag(~cmp, M.contains_key(~U32, ~U32, ~cmp, m, k))
    case 6n:
      ent(~cmp, M.first_entry(~U32, ~U32, ~cmp, m))
    case 7n:
      ent(~cmp, M.last_entry(~U32, ~U32, ~cmp, m))
    case 8n:
      ent(~cmp, M.lower_entry(~U32, ~U32, ~cmp, m, k))
    case 9n:
      ent(~cmp, M.floor_entry(~U32, ~U32, ~cmp, m, k))
    case 10n:
      ent(~cmp, M.ceiling_entry(~U32, ~U32, ~cmp, m, k))
    case 11n:
      ent(~cmp, M.higher_entry(~U32, ~U32, ~cmp, m, k))
    case 12n:
      ent(~cmp, M.poll_first_entry(~U32, ~U32, ~cmp, m))
    case 13n:
      ent(~cmp, M.poll_last_entry(~U32, ~U32, ~cmp, m))
    case 14n:
      val(~cmp, M.first_key(~U32, ~U32, ~cmp, m))
    case 15n:
      val(~cmp, M.last_key(~U32, ~U32, ~cmp, m))
    case 16n:
      val(~cmp, M.lower_key(~U32, ~U32, ~cmp, m, k))
    case 17n:
      val(~cmp, M.floor_key(~U32, ~U32, ~cmp, m, k))
    case 18n:
      val(~cmp, M.ceiling_key(~U32, ~U32, ~cmp, m, k))
    case 19n:
      val(~cmp, M.higher_key(~U32, ~U32, ~cmp, m, k))
    case 20n:
      flag(~cmp, M.is_empty(~U32, ~U32, ~cmp, m))
    case 21n:
      put(~cmp, M.put_if_absent(~U32, ~U32, ~cmp, m, k, v))
    case 22n:
      val(~cmp, M.replace(~U32, ~U32, ~cmp, m, k, v))
    case 23n:
      default_result(~cmp, M.get_or_default(~U32, ~U32, ~cmp, m, k, v))
    case 24n:
      M.fold(~U32, ~U32, ~cmp, ~String, ~collect, m, "entries")
    case 25n:
      folded_view(~cmp, M.view_fold(~U32, ~U32, ~cmp, ~String, ~collect, M.descending_map(~U32, ~U32, ~cmp, m), "entries"))
    case 26n:
      view_ready(~cmp, M.sub_map(~U32, ~U32, ~cmp, m, M.Inclusive{k}, M.Exclusive{v}))
    case 27n:
      walk_start(~cmp, 1n, M.iterator(~U32, ~U32, ~cmp, m))
    case 28n:
      walk_start(~cmp, 2n, M.descending_iterator(~U32, ~U32, ~cmp, m))
    case 29n:
      view_put_result(~cmp, M.view_put(~U32, ~U32, ~cmp, M.head_map(~U32, ~U32, ~cmp, m, M.Exclusive{50}), k, v))
    case 30n:
      view_val_result(~cmp, M.view_remove(~U32, ~U32, ~cmp, M.tail_map(~U32, ~U32, ~cmp, m, M.Inclusive{50}), k))
    case 31n:
      view_val_result(~cmp, M.view_get(~U32, ~U32, ~cmp, M.tail_map(~U32, ~U32, ~cmp, m, M.Inclusive{50}), k))
    case 33n:
      flag(~cmp, M.remove_if_equal(~U32, ~U32, ~cmp, ~U32.is_eq, m, k, v))
    case 34n:
      flag(~cmp, M.replace_if_equal(~U32, ~U32, ~cmp, ~U32.is_eq, m, k, v, U32.add(v, 1)))
    case 35n:
      flag(~cmp, M.contains_value(~U32, ~U32, ~cmp, ~U32.is_eq, m, v))
    case 36n:
      vent(~cmp, M.view_floor_entry(~U32, ~U32, ~cmp, M.head_map(~U32, ~U32, ~cmp, m, M.Exclusive{50}), k))
    case 37n:
      vent(~cmp, M.view_ceiling_entry(~U32, ~U32, ~cmp, M.head_map(~U32, ~U32, ~cmp, m, M.Exclusive{50}), k))
    case 38n:
      vent(~cmp, M.view_lower_entry(~U32, ~U32, ~cmp, M.head_map(~U32, ~U32, ~cmp, m, M.Exclusive{50}), k))
    case 39n:
      vent(~cmp, M.view_higher_entry(~U32, ~U32, ~cmp, M.head_map(~U32, ~U32, ~cmp, m, M.Exclusive{50}), k))
    case 40n:
      vent(~cmp, M.view_floor_entry(~U32, ~U32, ~cmp, M.view_reverse(~U32, ~U32, ~cmp, M.head_map(~U32, ~U32, ~cmp, m, M.Exclusive{50})), k))
    case 41n:
      vent(~cmp, M.view_first_entry(~U32, ~U32, ~cmp, M.head_map(~U32, ~U32, ~cmp, m, M.Exclusive{50})))
    case 42n:
      vent(~cmp, M.view_last_entry(~U32, ~U32, ~cmp, M.head_map(~U32, ~U32, ~cmp, m, M.Exclusive{50})))
    case 43n:
      vcount(~cmp, M.view_size(~U32, ~U32, ~cmp, M.head_map(~U32, ~U32, ~cmp, m, M.Exclusive{50})))
    case 44n:
      (M.view_finish(~U32, ~U32, ~cmp, M.view_clear(~U32, ~U32, ~cmp, M.head_map(~U32, ~U32, ~cmp, m, M.Exclusive{50}))), "ok")
    case 45n:
      cflag(~cmp, M.iterator_has_next(~U32, ~U32, ~cmp, M.iterator(~U32, ~U32, ~cmp, m)))
    case 46n:
      vflag(~cmp, M.view_contains_key(~U32, ~U32, ~cmp, M.head_map(~U32, ~U32, ~cmp, m, M.Exclusive{50}), k))
    case 47n:
      walk_key(~cmp, 10000n, "items", M.iterator_next_key(~U32, ~U32, ~cmp, M.key_set(~U32, ~U32, ~cmp, m)))
    case 48n:
      walk_value(~cmp, 10000n, "items", M.iterator_next_value(~U32, ~U32, ~cmp, M.values(~U32, ~U32, ~cmp, m)))
    case 49n:
      walk_start(~cmp, 0n, M.entry_set(~U32, ~U32, ~cmp, m))
    case 50n:
      walk_start(~cmp, 0n, M.view_iterator(~U32, ~U32, ~cmp, M.descending_map(~U32, ~U32, ~cmp, m)))
    case 51n:
      bounded_fold(~cmp, m, M.Exclusive{k}, M.Exclusive{v}, False{})
    case 52n:
      bounded_fold(~cmp, m, M.Inclusive{k}, M.Exclusive{v}, False{})
    case 53n:
      bounded_fold(~cmp, m, M.Exclusive{k}, M.Inclusive{v}, False{})
    case 54n:
      bounded_fold(~cmp, m, M.Inclusive{k}, M.Inclusive{v}, False{})
    case 55n:
      bounded_fold(~cmp, m, M.Exclusive{k}, M.Exclusive{v}, True{})
    case 56n:
      bounded_fold(~cmp, m, M.Inclusive{k}, M.Exclusive{v}, True{})
    case 57n:
      bounded_fold(~cmp, m, M.Exclusive{k}, M.Inclusive{v}, True{})
    case 58n:
      bounded_fold(~cmp, m, M.Inclusive{k}, M.Inclusive{v}, True{})
    case 32n:
      (M.with_limit(~U32, ~U32, ~cmp, U32.to_nat(k)), "ok")
    case _:
      dump(~cmp, m)

def run(~cmp: U32 -> U32 -> Cmp, ops: List<&2, String>, st: M.TreeMap<U32, U32, cmp> & String) -> List<&2, String>:
  match ops st:
    case Nil{} Tuple{m, out}:
      Con{out, Nil{}}
    case Con{h, tail} Tuple{m, out}:
      +fields = X.fields(h)
      Con{out, run(~cmp, tail, step(~cmp, X.nat_field(fields, 0n), m, X.u32_field(fields, 1n), X.u32_field(fields, 2n)))}

def start_groups(hit: Bool, ops: List<&2, String>) -> List<&2, String>:
  match hit:
    case True{}:
      run(~groups, ops, (M.new(~U32, ~U32, ~groups), "start"))
    case False{}:
      run(~U32.cmp, ops, (M.new(~U32, ~U32, ~U32.cmp), "start"))

def start_reverse(hit: Bool, kind: String, ops: List<&2, String>) -> List<&2, String>:
  match hit:
    case True{}:
      run(~rev, ops, (M.new(~U32, ~U32, ~rev), "start"))
    case False{}:
      start_groups(String.eq(kind, "groups"), ops)

def start(args: List<&2, String>) -> List<&2, String>:
  match args:
    case Nil{}:
      Nil{}
    case Con{+kind, ops}:
      start_reverse(String.eq(kind, "reverse"), kind, ops)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    X.print_lines(start(X.shared(args)))
