import Base
import ./lib/logic.bend as L
import ./lib/order.bend as O
import ../spec/balanced_search_tree.bend as S
import ../src/balanced_search_tree.bend as B
import ../types/balanced_search_tree.bend as E
import ./balanced_search_tree/sorted.bend as SO
import ./balanced_search_tree/specops.bend as SP
import ./balanced_search_tree/tree.bend as T
import ./balanced_search_tree/query.bend as Q
import ./balanced_search_tree/steps.bend as ST
import ./balanced_search_tree/trace.bend as TR

# Balanced search tree (RED-BLACK BINARY tree ordered map): public proof
# entry point.
# Laws are templates over a key comparator ~cmp with total-order laws
# ~o : O.Order(~K, ~cmp); each is instantiated, and thereby checked, below
# for (U32, U32.cmp, O.u32_order) and (String, String.order,
# O.string_order), the instances src/ exposes. Values are an erased type.
#   abstraction  ST.abs (in-order entry list)
#   invariant    ST.inv (strictly increasing keys, the red-black invariant
#                T.bal, and cached size = entry count)
#
# T.bal t = the root is black and T.ok t; T.ok is "both subtrees are proper,
# their black heights agree and a red node has no red child". The laws below
# also restate the textbook form directly: black root, black empty leaves,
# no red-red parent/child edge anywhere (T.nrr_all), and the same number of
# black nodes on every root-to-leaf path (T.all_eq over T.paths).

def new_abs(~K: Data, ~cmp: K -> K -> Cmp, -V: Data) -> {ST.abs(~K, ~cmp, V, B.new(K, V)) == Nil{} : List<&2, E.Entry<K, V>>}:
  {==}

def new_inv(~K: Data, ~cmp: K -> K -> Cmp, -V: Data) -> {ST.inv(~K, ~cmp, V, B.new(K, V)) == True{} : Bool}:
  {==}

def step_ok(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +s: B.OrdMap<K, V>, +op: E.Op<K, V>, +g: {ST.inv(~K, ~cmp, V, s) == True{} : Bool}) -> ST.StepOK(~K, ~cmp, V, s, op):
  ST.step_ok(~K, ~cmp, ~o, V, s, op, g)

# Balance is preserved by the tree-level insert and remove on their own.
def insert_balanced(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +t: B.Tree<K, V>, +k: K, +v: V, +b: {T.bal(K, V, t) == True{} : Bool}) -> {T.bal(K, V, B.insert_tree(~K, ~cmp, V, t, k, v)) == True{} : Bool}:
  T.insert_bal(~K, ~cmp, V, t, k, v, b)

def remove_balanced(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +t: B.Tree<K, V>, +k: K, +b: {T.bal(K, V, t) == True{} : Bool}) -> {T.bal(K, V, B.remove_tree(~K, ~cmp, V, t, k)) == True{} : Bool}:
  T.remove_bal(~K, ~cmp, V, t, k, b)

def trace_new(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +ops: List<&2, E.Op<K, V>>) -> {TR.view(~K, ~cmp, ~o, V, B.run(~K, ~cmp, V, ops, B.new(K, V))) == S.run(~K, ~cmp, V, ops, Nil{}) : List<&2, E.Entry<K, V>> & List<&2, E.Obs<K, V>>}:
  TR.trace_from(~K, ~cmp, ~o, V, ops, B.new(K, V), {==})

def trace_new_inv(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +ops: List<&2, E.Op<K, V>>) -> {ST.inv(~K, ~cmp, V, Pair.fst(B.OrdMap<K, V>, List<&2, E.Obs<K, V>>, B.run(~K, ~cmp, V, ops, B.new(K, V)))) == True{} : Bool}:
  TR.inv_from(~K, ~cmp, ~o, V, ops, B.new(K, V), {==})

# ---- checked instances ----

def u32_step_ok(-V: Data, +s: B.OrdMap<U32, V>, +op: E.Op<U32, V>, +g: {ST.inv(~U32, ~U32.cmp, V, s) == True{} : Bool}) -> ST.StepOK(~U32, ~U32.cmp, V, s, op):
  step_ok(~U32, ~U32.cmp, ~O.u32_order, V, s, op, g)

def u32_trace(-V: Data, +ops: List<&2, E.Op<U32, V>>) -> {TR.view(~U32, ~U32.cmp, ~O.u32_order, V, B.run_u32(V, ops, B.new(U32, V))) == S.run(~U32, ~U32.cmp, V, ops, Nil{}) : List<&2, E.Entry<U32, V>> & List<&2, E.Obs<U32, V>>}:
  trace_new(~U32, ~U32.cmp, ~O.u32_order, V, ops)

def u32_trace_inv(-V: Data, +ops: List<&2, E.Op<U32, V>>) -> {ST.inv(~U32, ~U32.cmp, V, Pair.fst(B.OrdMap<U32, V>, List<&2, E.Obs<U32, V>>, B.run_u32(V, ops, B.new(U32, V)))) == True{} : Bool}:
  trace_new_inv(~U32, ~U32.cmp, ~O.u32_order, V, ops)

def string_step_ok(-V: Data, +s: B.OrdMap<String, V>, +op: E.Op<String, V>, +g: {ST.inv(~String, ~String.order, V, s) == True{} : Bool}) -> ST.StepOK(~String, ~String.order, V, s, op):
  step_ok(~String, ~String.order, ~O.string_order, V, s, op, g)

def string_trace(-V: Data, +ops: List<&2, E.Op<String, V>>) -> {TR.view(~String, ~String.order, ~O.string_order, V, B.run_string(V, ops, B.new(String, V))) == S.run(~String, ~String.order, V, ops, Nil{}) : List<&2, E.Entry<String, V>> & List<&2, E.Obs<String, V>>}:
  trace_new(~String, ~String.order, ~O.string_order, V, ops)

def string_trace_inv(-V: Data, +ops: List<&2, E.Op<String, V>>) -> {ST.inv(~String, ~String.order, V, Pair.fst(B.OrdMap<String, V>, List<&2, E.Obs<String, V>>, B.run_string(V, ops, B.new(String, V)))) == True{} : Bool}:
  trace_new_inv(~String, ~String.order, ~O.string_order, V, ops)

def u32_insert_balanced(-V: Data, +t: B.Tree<U32, V>, +k: U32, +v: V, +b: {T.bal(U32, V, t) == True{} : Bool}) -> {T.bal(U32, V, B.insert_tree(~U32, ~U32.cmp, V, t, k, v)) == True{} : Bool}:
  insert_balanced(~U32, ~U32.cmp, V, t, k, v, b)

def u32_remove_balanced(-V: Data, +t: B.Tree<U32, V>, +k: U32, +b: {T.bal(U32, V, t) == True{} : Bool}) -> {T.bal(U32, V, B.remove_tree(~U32, ~U32.cmp, V, t, k)) == True{} : Bool}:
  remove_balanced(~U32, ~U32.cmp, V, t, k, b)

def string_insert_balanced(-V: Data, +t: B.Tree<String, V>, +k: String, +v: V, +b: {T.bal(String, V, t) == True{} : Bool}) -> {T.bal(String, V, B.insert_tree(~String, ~String.order, V, t, k, v)) == True{} : Bool}:
  insert_balanced(~String, ~String.order, V, t, k, v, b)

def string_remove_balanced(-V: Data, +t: B.Tree<String, V>, +k: String, +b: {T.bal(String, V, t) == True{} : Bool}) -> {T.bal(String, V, B.remove_tree(~String, ~String.order, V, t, k)) == True{} : Bool}:
  remove_balanced(~String, ~String.order, V, t, k, b)

# ---- the red-black structural properties, stated directly ----

def new_balanced(-K: Data, -V: Data) -> {T.bal(K, V, B.Leaf{}) == True{} : Bool}:
  T.new_bal(K, V)

def leaf_black(-K: Data, -V: Data) -> {B.is_red(K, V, B.Leaf{}) == False{} : Bool}:
  T.leaf_black(K, V)

def root_black(-K: Data, -V: Data, +t: B.Tree<K, V>, +b: {T.bal(K, V, t) == True{} : Bool}) -> {B.is_red(K, V, t) == False{} : Bool}:
  T.bal_root_black(K, V, t, b)

def no_red_red(-K: Data, -V: Data, +t: B.Tree<K, V>, +b: {T.bal(K, V, t) == True{} : Bool}) -> {T.nrr_all(K, V, t) == True{} : Bool}:
  T.ok_nrr(K, V, t, T.bal_ok(K, V, t, b))

def uniform_black_height(-K: Data, -V: Data, +t: B.Tree<K, V>, +b: {T.bal(K, V, t) == True{} : Bool}) -> {T.all_eq(T.bh(K, V, t), T.paths(K, V, t)) == True{} : Bool}:
  T.ok_paths(K, V, t, T.bal_ok(K, V, t, b))

def u32_root_black(-V: Data, +t: B.Tree<U32, V>, +b: {T.bal(U32, V, t) == True{} : Bool}) -> {B.is_red(U32, V, t) == False{} : Bool}:
  root_black(U32, V, t, b)

def u32_no_red_red(-V: Data, +t: B.Tree<U32, V>, +b: {T.bal(U32, V, t) == True{} : Bool}) -> {T.nrr_all(U32, V, t) == True{} : Bool}:
  no_red_red(U32, V, t, b)

def u32_uniform_black_height(-V: Data, +t: B.Tree<U32, V>, +b: {T.bal(U32, V, t) == True{} : Bool}) -> {T.all_eq(T.bh(U32, V, t), T.paths(U32, V, t)) == True{} : Bool}:
  uniform_black_height(U32, V, t, b)

def u32_new_balanced(-V: Data) -> {T.bal(U32, V, B.Leaf{}) == True{} : Bool}:
  new_balanced(U32, V)

def string_root_black(-V: Data, +t: B.Tree<String, V>, +b: {T.bal(String, V, t) == True{} : Bool}) -> {B.is_red(String, V, t) == False{} : Bool}:
  root_black(String, V, t, b)

def string_no_red_red(-V: Data, +t: B.Tree<String, V>, +b: {T.bal(String, V, t) == True{} : Bool}) -> {T.nrr_all(String, V, t) == True{} : Bool}:
  no_red_red(String, V, t, b)

def string_uniform_black_height(-V: Data, +t: B.Tree<String, V>, +b: {T.bal(String, V, t) == True{} : Bool}) -> {T.all_eq(T.bh(String, V, t), T.paths(String, V, t)) == True{} : Bool}:
  uniform_black_height(String, V, t, b)

def string_new_balanced(-V: Data) -> {T.bal(String, V, B.Leaf{}) == True{} : Bool}:
  new_balanced(String, V)
