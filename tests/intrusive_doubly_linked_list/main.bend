import Base
import ./fixture.bend as F
import ./churn.bend as C
import ../../src/containers/compat/intrusive_doubly_linked_list.bend as L
import ../../src/containers/types/intrusive_doubly_linked_list.bend as E
import ../support/text.bend as X

def error(e: E.Error) -> String:
  match e:
    case E.LimitExceeded{}: "ERR limit"
    case E.InvalidTraversal{}: "ERR traversal"

def bool(b: Bool) -> String:
  match b:
    case True{}: "1"
    case False{}: "0"

def maybe(m: Maybe<&2, U32>) -> String:
  match m:
    case None{}: "none"
    case Some{n}: U32.show(n)

def owned(xs: List<U32>) -> List<&2, U32>:
  match xs:
    case Nil{}: Nil{}
    case Con{v, rest}: Con{v, owned(rest)}

def result_unit(r: F.World & Result<&2, &1, E.Error, Unit>) -> F.World & String:
  match r:
    case Tuple{s, Fail{e}}: (s, error(e))
    case Tuple{s, Done{x}}: (s, "OK")

def result_num(r: F.World & Result<&2, &1, E.Error, U32>) -> F.World & String:
  match r:
    case Tuple{s, Fail{e}}: (s, error(e))
    case Tuple{s, Done{x}}: (s, U32.show(x))

def result_nat(r: F.World & Result<&2, &1, E.Error, Nat>) -> F.World & String:
  match r:
    case Tuple{s, Fail{e}}: (s, error(e))
    case Tuple{s, Done{x}}: (s, Nat.show(x))

def result_bool(r: F.World & Result<&2, &1, E.Error, Bool>) -> F.World & String:
  match r:
    case Tuple{s, Fail{e}}: (s, error(e))
    case Tuple{s, Done{x}}: (s, bool(x))

def result_maybe(r: F.World & Result<&2, &1, E.Error, Maybe<&2, U32>>) -> F.World & String:
  match r:
    case Tuple{s, Fail{e}}: (s, error(e))
    case Tuple{s, Done{x}}: (s, maybe(x))

def result_list(r: F.World & Result<&2, &1, E.Error, List<U32>>) -> F.World & String:
  match r:
    case Tuple{s, Fail{e}}: (s, error(e))
    case Tuple{s, Done{x}}: (s, X.join_u32(owned(x)))

def out_num(r: F.World & U32) -> F.World & String:
  (s, x) = r
  (s, U32.show(x))

def out_bool(r: F.World & Bool) -> F.World & String:
  (s, x) = r
  (s, bool(x))

def out_maybe(r: F.World & Maybe<&2, U32>) -> F.World & String:
  (s, x) = r
  (s, maybe(x))

def built(r: F.World & Maybe<&2, U32>) -> F.World & String:
  (s, +head) = r
  (F.write(s, 0, C.encode(head)), maybe(head))

def dispatch_0(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: (F.prepend(s, x, y), "OK")
    case False{}: (s, "ERR command")

def dispatch_1(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: (F.remove(s, x, y), "OK")
    case False{}: dispatch_0(s, op, x, y, fuel, String.eq(op, "p"))

def dispatch_2(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: (F.prepend2(s, x, y), "OK")
    case False{}: dispatch_1(s, op, x, y, fuel, String.eq(op, "r"))

def dispatch_3(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: (F.remove2(s, x, y), "OK")
    case False{}: dispatch_2(s, op, x, y, fuel, String.eq(op, "p2"))

def dispatch_4(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: (L.prepend(~F.World, ~U32, ~F.Reader, ~F.get_head, ~F.set_next, ~F.set_prev, ~(s => h => n => F.full_same(s, h, n)), s, F.Room{x}, y), "OK")
    case False{}: dispatch_3(s, op, x, y, fuel, String.eq(op, "r2"))

def dispatch_5(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: out_maybe(L.next(~F.World, ~U32, ~F.next, s, x))
    case False{}: dispatch_4(s, op, x, y, fuel, String.eq(op, "ps"))

def dispatch_6(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: out_maybe(L.prev(~F.World, ~U32, ~F.prev, s, x))
    case False{}: dispatch_5(s, op, x, y, fuel, String.eq(op, "next"))

def dispatch_7(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: out_num(L.value(~F.World, ~U32, ~U32, ~F.value, s, x))
    case False{}: dispatch_6(s, op, x, y, fuel, String.eq(op, "prev"))

def dispatch_8(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: out_maybe(L.get_head(~F.World, ~U32, ~F.Reader, ~F.get_head, s, F.Room{x}))
    case False{}: dispatch_7(s, op, x, y, fuel, String.eq(op, "value"))

def dispatch_9(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: (F.pool_new(s, fuel), "OK")
    case False{}: dispatch_8(s, op, x, y, fuel, String.eq(op, "head"))

def dispatch_10(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: (F.free(s, 0, x), "OK")
    case False{}: dispatch_9(s, op, x, y, fuel, String.eq(op, "pool-new"))

def dispatch_11(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: out_num(F.take(s))
    case False{}: dispatch_10(s, op, x, y, fuel, String.eq(op, "pool-free"))

def dispatch_12(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: out_bool(L.is_empty(~F.World, ~U32, ~F.Reader, ~F.get_head, s, F.Room{x}))
    case False{}: dispatch_11(s, op, x, y, fuel, String.eq(op, "pool-next"))

def dispatch_13(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: out_bool(L.non_empty(~F.World, ~U32, ~F.Reader, ~F.get_head, s, F.Room{x}))
    case False{}: dispatch_12(s, op, x, y, fuel, String.eq(op, "is_empty"))

def dispatch_14(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: out_bool(L.at_least_two(~F.World, ~U32, ~F.Reader, ~F.get_head, ~F.next, s, F.Room{x}))
    case False{}: dispatch_13(s, op, x, y, fuel, String.eq(op, "non_empty"))

def dispatch_15(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: result_nat(L.length(~F.World, ~U32, ~F.Reader, ~F.get_head, ~F.next, fuel, s, F.Room{x}))
    case False{}: dispatch_14(s, op, x, y, fuel, String.eq(op, "at_least_two"))

def dispatch_16(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: result_maybe(L.find(~F.World, ~U32, ~U32, ~U32, ~F.Reader, ~F.get_head, ~F.next, ~F.value, ~(s => c => v => F.predicate(s, c, v)), fuel, s, F.Room{x}, y))
    case False{}: dispatch_15(s, op, x, y, fuel, String.eq(op, "length"))

def dispatch_17(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: result_maybe(L.find_some_this(~F.World, ~U32, ~U32, ~U32, ~F.Reader, ~F.get_head, ~F.next, ~F.value, ~(s => c => v => F.predicate(s, c, v)), fuel, s, F.Room{x}, y))
    case False{}: dispatch_16(s, op, x, y, fuel, String.eq(op, "find"))

def dispatch_18(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: result_bool(L.exists(~F.World, ~U32, ~U32, ~U32, ~F.Reader, ~F.get_head, ~F.next, ~F.value, ~(s => c => v => F.predicate(s, c, v)), fuel, s, F.Room{x}, y))
    case False{}: dispatch_17(s, op, x, y, fuel, String.eq(op, "find_some_this"))

def dispatch_19(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: result_bool(L.forall(~F.World, ~U32, ~U32, ~U32, ~F.Reader, ~F.get_head, ~F.next, ~F.value, ~(s => c => v => F.predicate(s, c, v)), fuel, s, F.Room{x}, y))
    case False{}: dispatch_18(s, op, x, y, fuel, String.eq(op, "exists"))

def dispatch_20(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: result_nat(L.count(~F.World, ~U32, ~U32, ~U32, ~F.Reader, ~F.get_head, ~F.next, ~F.value, ~(s => c => v => F.predicate(s, c, v)), fuel, s, F.Room{x}, y))
    case False{}: dispatch_19(s, op, x, y, fuel, String.eq(op, "forall"))

def dispatch_21(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: result_maybe(L.find_convert(~F.World, ~U32, ~U32, ~U32, ~U32, ~F.Reader, ~F.get_head, ~F.next, ~F.value, ~(s => v => F.convert(s, v)), ~(s => c => v => F.predicate(s, c, v)), fuel, s, F.Room{x}, y))
    case False{}: dispatch_20(s, op, x, y, fuel, String.eq(op, "count"))

def dispatch_22(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: result_maybe(L.find_value(~F.World, ~U32, ~U32, ~F.Reader, ~F.get_head, ~F.next, ~F.value, ~(a => b => U32.is_eq(a, b)), fuel, s, F.Room{x}, y))
    case False{}: dispatch_21(s, op, x, y, fuel, String.eq(op, "find_convert"))

def dispatch_23(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: result_maybe(L.find_value_convert(~F.World, ~U32, ~U32, ~U32, ~F.Reader, ~F.get_head, ~F.next, ~F.value, ~(s => v => F.convert(s, v)), ~(a => b => U32.is_eq(a, b)), fuel, s, F.Room{x}, y))
    case False{}: dispatch_22(s, op, x, y, fuel, String.eq(op, "find_value"))

def dispatch_24(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: result_unit(L.foreach(~F.World, ~U32, ~U32, ~U32, ~F.Reader, ~F.get_head, ~F.next, ~F.value, ~(s => c => v => F.visit(s, c, v)), fuel, s, F.Room{x}, y))
    case False{}: dispatch_23(s, op, x, y, fuel, String.eq(op, "find_value_convert"))

def dispatch_25(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: result_unit(L.foreach(~F.World, ~U32, ~U32, ~U32, ~F.Reader, ~F.get_head, ~F.next, ~F.value, ~(s => c => v => F.visit_remove(s, c, v)), fuel, s, F.Room{x}, y))
    case False{}: dispatch_24(s, op, x, y, fuel, String.eq(op, "foreach"))

def dispatch_26(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: result_num(L.fold_left(~F.World, ~U32, ~U32, ~U32, ~U32, ~F.Reader, ~F.get_head, ~F.next, ~F.value, ~(s => c => a => v => F.sum(s, c, a, v)), fuel, s, F.Room{x}, y, 0))
    case False{}: dispatch_25(s, op, x, y, fuel, String.eq(op, "foreach-remove"))

def dispatch_27(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: result_unit(L.clear_list_as(~F.World, ~U32, ~F.Reader, ~F.Writer, ~U32, ~F.get_head, ~F.next, ~F.set_next, ~F.set_prev, ~F.set_head, ~(s => c => n => F.after_remove(s, c, n)), fuel, s, F.Room{x}, F.Commander{x}, y))
    case False{}: dispatch_26(s, op, x, y, fuel, String.eq(op, "fold"))

def dispatch_28(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: result_unit(L.clear_list(~F.World, ~U32, ~F.Reader, ~U32, ~F.get_head, ~F.next, ~F.set_next, ~F.set_prev, ~F.set_same, ~(s => c => n => F.after_remove(s, c, n)), fuel, s, F.Room{x}, y))
    case False{}: dispatch_27(s, op, x, y, fuel, String.eq(op, "clear_list"))

def dispatch_29(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: result_unit(L.clear_list_with_pool_as(~F.World, ~U32, ~F.Reader, ~F.Writer, ~U32, ~F.get_head, ~F.next, ~F.set_next, ~F.set_prev, ~F.set_head, ~(s => c => n => F.free(s, c, n)), fuel, s, F.Room{x}, F.Commander{x}, y))
    case False{}: dispatch_28(s, op, x, y, fuel, String.eq(op, "clear_list_same"))

def dispatch_30(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: result_unit(L.clear_list_with_pool(~F.World, ~U32, ~F.Reader, ~U32, ~F.get_head, ~F.next, ~F.set_next, ~F.set_prev, ~F.set_same, ~(s => c => n => F.free(s, c, n)), fuel, s, F.Room{x}, y))
    case False{}: dispatch_29(s, op, x, y, fuel, String.eq(op, "clear_list_with_pool"))

def dispatch_31(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: result_unit(L.foreach_remove_filter_as(~F.World, ~U32, ~U32, ~F.Reader, ~F.Writer, ~U32, ~F.get_head, ~F.next, ~F.prev, ~F.set_next, ~F.set_prev, ~F.set_head, ~F.value, ~(s => c => v => F.predicate(s, c, v)), ~(s => c => n => F.after_remove(s, c, n)), fuel, s, F.Room{x}, F.Commander{x}, y))
    case False{}: dispatch_30(s, op, x, y, fuel, String.eq(op, "clear_list_with_pool_same"))

def dispatch_32(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: result_unit(L.foreach_remove_filter(~F.World, ~U32, ~U32, ~F.Reader, ~U32, ~F.get_head, ~F.next, ~F.prev, ~F.set_next, ~F.set_prev, ~F.set_same, ~F.value, ~(s => c => v => F.predicate(s, c, v)), ~(s => c => n => F.after_remove(s, c, n)), fuel, s, F.Room{x}, y))
    case False{}: dispatch_31(s, op, x, y, fuel, String.eq(op, "foreach_remove_filter"))

def dispatch_33(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: result_unit(L.foreach_remove_convert_as(~F.World, ~U32, ~U32, ~U32, ~F.Reader, ~F.Writer, ~U32, ~F.get_head, ~F.next, ~F.prev, ~F.set_next, ~F.set_prev, ~F.set_head, ~F.value, ~(s => v => F.convert(s, v)), ~(s => c => v => F.visit(s, c, v)), ~(s => c => n => F.after_remove(s, c, n)), fuel, s, F.Room{x}, F.Commander{x}, y))
    case False{}: dispatch_32(s, op, x, y, fuel, String.eq(op, "foreach_remove_filter_same"))

def dispatch_34(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: result_unit(L.foreach_remove_convert(~F.World, ~U32, ~U32, ~U32, ~F.Reader, ~U32, ~F.get_head, ~F.next, ~F.prev, ~F.set_next, ~F.set_prev, ~F.set_same, ~F.value, ~(s => v => F.convert(s, v)), ~(s => c => v => F.visit(s, c, v)), ~(s => c => n => F.after_remove(s, c, n)), fuel, s, F.Room{x}, y))
    case False{}: dispatch_33(s, op, x, y, fuel, String.eq(op, "foreach_remove_convert"))

def dispatch_35(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: result_unit(L.foreach_remove_convert_filter_as(~F.World, ~U32, ~U32, ~U32, ~F.Reader, ~F.Writer, ~U32, ~F.get_head, ~F.next, ~F.prev, ~F.set_next, ~F.set_prev, ~F.set_head, ~F.value, ~(s => v => F.convert(s, v)), ~(s => c => v => F.predicate(s, c, v)), ~(s => c => n => F.after_remove(s, c, n)), fuel, s, F.Room{x}, F.Commander{x}, y))
    case False{}: dispatch_34(s, op, x, y, fuel, String.eq(op, "foreach_remove_convert_same"))

def dispatch_36(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: result_unit(L.foreach_remove_convert_filter(~F.World, ~U32, ~U32, ~U32, ~F.Reader, ~U32, ~F.get_head, ~F.next, ~F.prev, ~F.set_next, ~F.set_prev, ~F.set_same, ~F.value, ~(s => v => F.convert(s, v)), ~(s => c => v => F.predicate(s, c, v)), ~(s => c => n => F.after_remove(s, c, n)), fuel, s, F.Room{x}, y))
    case False{}: dispatch_35(s, op, x, y, fuel, String.eq(op, "foreach_remove_convert_filter"))

def dispatch_37(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: result_list(L.map_to_list(~F.World, ~U32, ~U32, ~U32, ~U32, ~F.Reader, ~F.get_head, ~F.next, ~F.prev, ~F.value, ~(s => c => v => F.mapped(s, c, v)), fuel, s, F.Room{x}, y))
    case False{}: dispatch_36(s, op, x, y, fuel, String.eq(op, "foreach_remove_convert_filter_same"))

def dispatch_38(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: result_list(L.flat_map_to_list(~F.World, ~U32, ~U32, ~U32, ~U32, ~F.Reader, ~F.get_head, ~F.next, ~F.prev, ~F.value, ~(s => c => v => F.flat(s, c, v)), fuel, s, F.Room{x}, y))
    case False{}: dispatch_37(s, op, x, y, fuel, String.eq(op, "map_to_list"))

def dispatch_39(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: result_list(L.to_list(~F.World, ~U32, ~U32, ~F.Reader, ~F.get_head, ~F.next, ~F.prev, ~F.value, fuel, s, F.Room{x}))
    case False{}: dispatch_38(s, op, x, y, fuel, String.eq(op, "flat_map_to_list"))

def dispatch_40(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: built(L.from_nodes(~F.World, ~U32, ~F.set_next, ~F.set_prev, s, Con{x, Con{y, Nil{}}}))
    case False{}: dispatch_39(s, op, x, y, fuel, String.eq(op, "to_list"))

def dispatch_41(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: built(L.from_nodes(~F.World, ~U32, ~F.set_next, ~F.set_prev, s, Nil{}))
    case False{}: dispatch_40(s, op, x, y, fuel, String.eq(op, "from_nodes"))

def dispatch_42(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: built(L.from_values(~F.World, ~U32, ~U32, ~U32, ~F.set_next, ~F.set_prev, ~(s => c => v => F.make(s, c, v)), s, Con{x, Con{y, Nil{}}}, 0))
    case False{}: dispatch_41(s, op, x, y, fuel, String.eq(op, "from_empty"))

def dispatch_43(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: built(L.map_from_nodes(~F.World, ~U32, ~U32, ~U32, ~F.set_next, ~F.set_prev, ~(s => c => v => F.make(s, c, v)), s, Con{x, Con{y, Nil{}}}, 0))
    case False{}: dispatch_42(s, op, x, y, fuel, String.eq(op, "from_values"))

def dispatch_44(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat, hit: Bool) -> F.World & String:
  match hit:
    case True{}: built(L.map_from_values(~F.World, ~U32, ~U32, ~U32, ~U32, ~F.set_next, ~F.set_prev, ~(s => c => v => F.mapped(s, c, v)), ~(s => c => v => F.make(s, c, v)), s, Con{x, Con{y, Nil{}}}, 0))
    case False{}: dispatch_43(s, op, x, y, fuel, String.eq(op, "map_from_nodes"))

def apply(s: F.World, +op: String, +x: U32, +y: U32, +fuel: Nat) -> F.World & String:
  dispatch_44(s, op, x, y, fuel, String.eq(op, "map_from_values"))

def reset_or_apply(s: F.World, +parts: List<&2, String>, reset: Bool) -> F.World & String:
  match reset:
    case True{}: (F.new(), "OK")
    case False{}: apply(s, X.field(parts, 0n), X.u32_field(parts, 1n), X.u32_field(parts, 2n), X.nat_field(parts, 3n))

def token(s: F.World, +parts: List<&2, String>) -> F.World & String:
  F.snapshot(reset_or_apply(s, parts, String.eq(X.field(parts, 0n), "reset")))

def step_done(acc: List<&2, String>, r: F.World & String) -> F.World & List<&2, String>:
  (s, out) = r
  (s, Con{out, acc})

def step(t: String, r: F.World & List<&2, String>) -> F.World & List<&2, String>:
  (s, acc) = r
  step_done(acc, token(s, X.fields(t)))

def run(tokens: List<&2, String>, r: F.World & List<&2, String>) -> List<&2, String>:
  match tokens:
    case Nil{}:
      (s, out) = r
      List.reverse(&2, String, out)
    case Con{t, rest}: run(rest, step(t, r))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    X.print_lines(run(X.shared(args), (F.new(), Nil{})))
