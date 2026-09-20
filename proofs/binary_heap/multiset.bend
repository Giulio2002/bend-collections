import Base
import ../lib/logic.bend as L
import ../lib/order.bend as O
import ../lib/list.bend as LL
import ../../spec/common.bend as SC
import ../../spec/binary_heap.bend as S

# Insertion-sorted lists as canonical multisets, under a total order ~o.
# All lemmas are templates over (~A, ~cmp, ~o); they are checked through the
# U32 and String instances at the end of this file and in END_TO_END.bend.

def all_ge(~A: Data, ~cmp: A -> A -> Cmp, +z: A, xs: List<&2, A>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(S.le(~A, ~cmp, z, h), all_ge(~A, ~cmp, z, t))

def and_swap(+a: Bool, +b: Bool, +c: Bool) -> {Bool.and(a, Bool.and(b, c)) == Bool.and(b, Bool.and(a, c)) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def ins_cons(~A: Data, ~cmp: A -> A -> Cmp, +x: A, +h: A, +t: List<&2, A>, +b: Bool, +e: {S.le(~A, ~cmp, x, h) == b : Bool}) -> {S.ins(~A, ~cmp, x, Con{h, t}) == Bool.pick(List<&2, A>, b, Con{x, Con{h, t}}, Con{h, S.ins(~A, ~cmp, x, t)}) : List<&2, A>}:
  %e : {S.ins(~A, ~cmp, x, Con{h, t}) == Bool.pick(List<&2, A>, _, Con{x, Con{h, t}}, Con{h, S.ins(~A, ~cmp, x, t)}) : List<&2, A>}
  {==}

def all_ge_ins_c(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +z: A, +x: A, +h: A, +t: List<&2, A>, +b: Bool, +e: {S.le(~A, ~cmp, x, h) == b : Bool}, +ih: {all_ge(~A, ~cmp, z, S.ins(~A, ~cmp, x, t)) == Bool.and(S.le(~A, ~cmp, z, x), all_ge(~A, ~cmp, z, t)) : Bool}) -> {all_ge(~A, ~cmp, z, S.ins(~A, ~cmp, x, Con{h, t})) == Bool.and(S.le(~A, ~cmp, z, x), all_ge(~A, ~cmp, z, Con{h, t})) : Bool}:
  match b:
    case True{}:
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, x, Con{h, t}), Con{x, Con{h, t}}, ins_cons(~A, ~cmp, x, h, t, True{}, e)) : {all_ge(~A, ~cmp, z, _) == Bool.and(S.le(~A, ~cmp, z, x), all_ge(~A, ~cmp, z, Con{h, t})) : Bool}
      {==}
    case False{}:
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, x, Con{h, t}), Con{h, S.ins(~A, ~cmp, x, t)}, ins_cons(~A, ~cmp, x, h, t, False{}, e)) : {all_ge(~A, ~cmp, z, _) == Bool.and(S.le(~A, ~cmp, z, x), all_ge(~A, ~cmp, z, Con{h, t})) : Bool}
      %Equal.sym(Bool, all_ge(~A, ~cmp, z, S.ins(~A, ~cmp, x, t)), Bool.and(S.le(~A, ~cmp, z, x), all_ge(~A, ~cmp, z, t)), ih) : {Bool.and(S.le(~A, ~cmp, z, h), _) == Bool.and(S.le(~A, ~cmp, z, x), Bool.and(S.le(~A, ~cmp, z, h), all_ge(~A, ~cmp, z, t))) : Bool}
      and_swap(S.le(~A, ~cmp, z, h), S.le(~A, ~cmp, z, x), all_ge(~A, ~cmp, z, t))

def all_ge_ins(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +z: A, +x: A, +xs: List<&2, A>) -> {all_ge(~A, ~cmp, z, S.ins(~A, ~cmp, x, xs)) == Bool.and(S.le(~A, ~cmp, z, x), all_ge(~A, ~cmp, z, xs)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      all_ge_ins_c(~A, ~cmp, ~o, z, x, h, t, S.le(~A, ~cmp, x, h), {==}, all_ge_ins(~A, ~cmp, ~o, z, x, t))

# A value not larger than every element goes first.
def ins_min(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +x: A, +xs: List<&2, A>, +h: {all_ge(~A, ~cmp, x, xs) == True{} : Bool}) -> {S.ins(~A, ~cmp, x, xs) == Con{x, xs} : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      %Equal.sym(Bool, S.le(~A, ~cmp, x, y), True{}, L.and_left(S.le(~A, ~cmp, x, y), all_ge(~A, ~cmp, x, t), h)) : {Bool.pick(List<&2, A>, _, Con{x, Con{y, t}}, Con{y, S.ins(~A, ~cmp, x, t)}) == Con{x, Con{y, t}} : List<&2, A>}
      {==}

# Insertion order is irrelevant (uses totality, transitivity, antisymmetry).
def comm_nil(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +x: A, +y: A, +bxy: Bool, +exy: {S.le(~A, ~cmp, x, y) == bxy : Bool}, +byx: Bool, +eyx: {S.le(~A, ~cmp, y, x) == byx : Bool}) -> {S.ins(~A, ~cmp, x, S.ins(~A, ~cmp, y, Nil{})) == S.ins(~A, ~cmp, y, S.ins(~A, ~cmp, x, Nil{})) : List<&2, A>}:
  match bxy byx:
    case True{} True{}:
      %O.le_antisym(~A, ~cmp, ~o, x, y, exy, eyx) : {S.ins(~A, ~cmp, x, S.ins(~A, ~cmp, _, Nil{})) == S.ins(~A, ~cmp, _, S.ins(~A, ~cmp, x, Nil{})) : List<&2, A>}
      {==}
    case True{} False{}:
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, x, Con{y, Nil{}}), Con{x, Con{y, Nil{}}}, ins_cons(~A, ~cmp, x, y, Nil{}, True{}, exy)) : {_ == S.ins(~A, ~cmp, y, Con{x, Nil{}}) : List<&2, A>}
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, y, Con{x, Nil{}}), Con{x, Con{y, Nil{}}}, ins_cons(~A, ~cmp, y, x, Nil{}, False{}, eyx)) : {Con{x, Con{y, Nil{}}} == _ : List<&2, A>}
      {==}
    case False{} True{}:
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, x, Con{y, Nil{}}), Con{y, Con{x, Nil{}}}, ins_cons(~A, ~cmp, x, y, Nil{}, False{}, exy)) : {_ == S.ins(~A, ~cmp, y, Con{x, Nil{}}) : List<&2, A>}
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, y, Con{x, Nil{}}), Con{y, Con{x, Nil{}}}, ins_cons(~A, ~cmp, y, x, Nil{}, True{}, eyx)) : {Con{y, Con{x, Nil{}}} == _ : List<&2, A>}
      {==}
    case False{} False{}:
      Empty.absurd({S.ins(~A, ~cmp, x, S.ins(~A, ~cmp, y, Nil{})) == S.ins(~A, ~cmp, y, S.ins(~A, ~cmp, x, Nil{})) : List<&2, A>}, L.true_not_false(S.le(~A, ~cmp, y, x), O.total(~A, ~cmp, ~o, x, y, exy), eyx))

def comm_cons(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +x: A, +y: A, +h: A, +t: List<&2, A>, +bxy: Bool, +exy: {S.le(~A, ~cmp, x, y) == bxy : Bool}, +byx: Bool, +eyx: {S.le(~A, ~cmp, y, x) == byx : Bool}, +bxh: Bool, +exh: {S.le(~A, ~cmp, x, h) == bxh : Bool}, +byh: Bool, +eyh: {S.le(~A, ~cmp, y, h) == byh : Bool}, +ih: {S.ins(~A, ~cmp, x, S.ins(~A, ~cmp, y, t)) == S.ins(~A, ~cmp, y, S.ins(~A, ~cmp, x, t)) : List<&2, A>}) -> {S.ins(~A, ~cmp, x, S.ins(~A, ~cmp, y, Con{h, t})) == S.ins(~A, ~cmp, y, S.ins(~A, ~cmp, x, Con{h, t})) : List<&2, A>}:
  match bxy byx bxh byh:
    case False{} False{} _ _:
      Empty.absurd({S.ins(~A, ~cmp, x, S.ins(~A, ~cmp, y, Con{h, t})) == S.ins(~A, ~cmp, y, S.ins(~A, ~cmp, x, Con{h, t})) : List<&2, A>}, L.true_not_false(S.le(~A, ~cmp, y, x), O.total(~A, ~cmp, ~o, x, y, exy), eyx))
    case True{} True{} _ _:
      %O.le_antisym(~A, ~cmp, ~o, x, y, exy, eyx) : {S.ins(~A, ~cmp, x, S.ins(~A, ~cmp, _, Con{h, t})) == S.ins(~A, ~cmp, _, S.ins(~A, ~cmp, x, Con{h, t})) : List<&2, A>}
      {==}
    case True{} False{} True{} True{}:
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, y, Con{h, t}), Con{y, Con{h, t}}, ins_cons(~A, ~cmp, y, h, t, True{}, eyh)) : {S.ins(~A, ~cmp, x, _) == S.ins(~A, ~cmp, y, S.ins(~A, ~cmp, x, Con{h, t})) : List<&2, A>}
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, x, Con{h, t}), Con{x, Con{h, t}}, ins_cons(~A, ~cmp, x, h, t, True{}, exh)) : {S.ins(~A, ~cmp, x, Con{y, Con{h, t}}) == S.ins(~A, ~cmp, y, _) : List<&2, A>}
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, x, Con{y, Con{h, t}}), Con{x, Con{y, Con{h, t}}}, ins_cons(~A, ~cmp, x, y, Con{h, t}, True{}, exy)) : {_ == S.ins(~A, ~cmp, y, Con{x, Con{h, t}}) : List<&2, A>}
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, y, Con{x, Con{h, t}}), Con{x, S.ins(~A, ~cmp, y, Con{h, t})}, ins_cons(~A, ~cmp, y, x, Con{h, t}, False{}, eyx)) : {Con{x, Con{y, Con{h, t}}} == _ : List<&2, A>}
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, y, Con{h, t}), Con{y, Con{h, t}}, ins_cons(~A, ~cmp, y, h, t, True{}, eyh)) : {Con{x, Con{y, Con{h, t}}} == Con{x, _} : List<&2, A>}
      {==}
    case True{} False{} False{} True{}:
      Empty.absurd({S.ins(~A, ~cmp, x, S.ins(~A, ~cmp, y, Con{h, t})) == S.ins(~A, ~cmp, y, S.ins(~A, ~cmp, x, Con{h, t})) : List<&2, A>}, L.true_not_false(S.le(~A, ~cmp, x, h), O.trans(~A, ~cmp, o, x, y, h, exy, eyh), exh))
    case True{} False{} True{} False{}:
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, y, Con{h, t}), Con{h, S.ins(~A, ~cmp, y, t)}, ins_cons(~A, ~cmp, y, h, t, False{}, eyh)) : {S.ins(~A, ~cmp, x, _) == S.ins(~A, ~cmp, y, S.ins(~A, ~cmp, x, Con{h, t})) : List<&2, A>}
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, x, Con{h, S.ins(~A, ~cmp, y, t)}), Con{x, Con{h, S.ins(~A, ~cmp, y, t)}}, ins_cons(~A, ~cmp, x, h, S.ins(~A, ~cmp, y, t), True{}, exh)) : {_ == S.ins(~A, ~cmp, y, S.ins(~A, ~cmp, x, Con{h, t})) : List<&2, A>}
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, x, Con{h, t}), Con{x, Con{h, t}}, ins_cons(~A, ~cmp, x, h, t, True{}, exh)) : {Con{x, Con{h, S.ins(~A, ~cmp, y, t)}} == S.ins(~A, ~cmp, y, _) : List<&2, A>}
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, y, Con{x, Con{h, t}}), Con{x, S.ins(~A, ~cmp, y, Con{h, t})}, ins_cons(~A, ~cmp, y, x, Con{h, t}, False{}, eyx)) : {Con{x, Con{h, S.ins(~A, ~cmp, y, t)}} == _ : List<&2, A>}
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, y, Con{h, t}), Con{h, S.ins(~A, ~cmp, y, t)}, ins_cons(~A, ~cmp, y, h, t, False{}, eyh)) : {Con{x, Con{h, S.ins(~A, ~cmp, y, t)}} == Con{x, _} : List<&2, A>}
      {==}
    case True{} False{} False{} False{}:
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, y, Con{h, t}), Con{h, S.ins(~A, ~cmp, y, t)}, ins_cons(~A, ~cmp, y, h, t, False{}, eyh)) : {S.ins(~A, ~cmp, x, _) == S.ins(~A, ~cmp, y, S.ins(~A, ~cmp, x, Con{h, t})) : List<&2, A>}
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, x, Con{h, S.ins(~A, ~cmp, y, t)}), Con{h, S.ins(~A, ~cmp, x, S.ins(~A, ~cmp, y, t))}, ins_cons(~A, ~cmp, x, h, S.ins(~A, ~cmp, y, t), False{}, exh)) : {_ == S.ins(~A, ~cmp, y, S.ins(~A, ~cmp, x, Con{h, t})) : List<&2, A>}
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, x, Con{h, t}), Con{h, S.ins(~A, ~cmp, x, t)}, ins_cons(~A, ~cmp, x, h, t, False{}, exh)) : {Con{h, S.ins(~A, ~cmp, x, S.ins(~A, ~cmp, y, t))} == S.ins(~A, ~cmp, y, _) : List<&2, A>}
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, y, Con{h, S.ins(~A, ~cmp, x, t)}), Con{h, S.ins(~A, ~cmp, y, S.ins(~A, ~cmp, x, t))}, ins_cons(~A, ~cmp, y, h, S.ins(~A, ~cmp, x, t), False{}, eyh)) : {Con{h, S.ins(~A, ~cmp, x, S.ins(~A, ~cmp, y, t))} == _ : List<&2, A>}
      LL.cons_cong(A, h, S.ins(~A, ~cmp, x, S.ins(~A, ~cmp, y, t)), S.ins(~A, ~cmp, y, S.ins(~A, ~cmp, x, t)), ih)
    case False{} True{} True{} True{}:
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, y, Con{h, t}), Con{y, Con{h, t}}, ins_cons(~A, ~cmp, y, h, t, True{}, eyh)) : {S.ins(~A, ~cmp, x, _) == S.ins(~A, ~cmp, y, S.ins(~A, ~cmp, x, Con{h, t})) : List<&2, A>}
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, x, Con{y, Con{h, t}}), Con{y, S.ins(~A, ~cmp, x, Con{h, t})}, ins_cons(~A, ~cmp, x, y, Con{h, t}, False{}, exy)) : {_ == S.ins(~A, ~cmp, y, S.ins(~A, ~cmp, x, Con{h, t})) : List<&2, A>}
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, x, Con{h, t}), Con{x, Con{h, t}}, ins_cons(~A, ~cmp, x, h, t, True{}, exh)) : {Con{y, _} == S.ins(~A, ~cmp, y, _) : List<&2, A>}
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, y, Con{x, Con{h, t}}), Con{y, Con{x, Con{h, t}}}, ins_cons(~A, ~cmp, y, x, Con{h, t}, True{}, eyx)) : {Con{y, Con{x, Con{h, t}}} == _ : List<&2, A>}
      {==}
    case False{} True{} False{} True{}:
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, y, Con{h, t}), Con{y, Con{h, t}}, ins_cons(~A, ~cmp, y, h, t, True{}, eyh)) : {S.ins(~A, ~cmp, x, _) == S.ins(~A, ~cmp, y, S.ins(~A, ~cmp, x, Con{h, t})) : List<&2, A>}
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, x, Con{y, Con{h, t}}), Con{y, S.ins(~A, ~cmp, x, Con{h, t})}, ins_cons(~A, ~cmp, x, y, Con{h, t}, False{}, exy)) : {_ == S.ins(~A, ~cmp, y, S.ins(~A, ~cmp, x, Con{h, t})) : List<&2, A>}
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, x, Con{h, t}), Con{h, S.ins(~A, ~cmp, x, t)}, ins_cons(~A, ~cmp, x, h, t, False{}, exh)) : {Con{y, _} == S.ins(~A, ~cmp, y, _) : List<&2, A>}
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, y, Con{h, S.ins(~A, ~cmp, x, t)}), Con{y, Con{h, S.ins(~A, ~cmp, x, t)}}, ins_cons(~A, ~cmp, y, h, S.ins(~A, ~cmp, x, t), True{}, eyh)) : {Con{y, Con{h, S.ins(~A, ~cmp, x, t)}} == _ : List<&2, A>}
      {==}
    case False{} True{} True{} False{}:
      Empty.absurd({S.ins(~A, ~cmp, x, S.ins(~A, ~cmp, y, Con{h, t})) == S.ins(~A, ~cmp, y, S.ins(~A, ~cmp, x, Con{h, t})) : List<&2, A>}, L.true_not_false(S.le(~A, ~cmp, y, h), O.trans(~A, ~cmp, o, y, x, h, eyx, exh), eyh))
    case False{} True{} False{} False{}:
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, y, Con{h, t}), Con{h, S.ins(~A, ~cmp, y, t)}, ins_cons(~A, ~cmp, y, h, t, False{}, eyh)) : {S.ins(~A, ~cmp, x, _) == S.ins(~A, ~cmp, y, S.ins(~A, ~cmp, x, Con{h, t})) : List<&2, A>}
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, x, Con{h, S.ins(~A, ~cmp, y, t)}), Con{h, S.ins(~A, ~cmp, x, S.ins(~A, ~cmp, y, t))}, ins_cons(~A, ~cmp, x, h, S.ins(~A, ~cmp, y, t), False{}, exh)) : {_ == S.ins(~A, ~cmp, y, S.ins(~A, ~cmp, x, Con{h, t})) : List<&2, A>}
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, x, Con{h, t}), Con{h, S.ins(~A, ~cmp, x, t)}, ins_cons(~A, ~cmp, x, h, t, False{}, exh)) : {Con{h, S.ins(~A, ~cmp, x, S.ins(~A, ~cmp, y, t))} == S.ins(~A, ~cmp, y, _) : List<&2, A>}
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, y, Con{h, S.ins(~A, ~cmp, x, t)}), Con{h, S.ins(~A, ~cmp, y, S.ins(~A, ~cmp, x, t))}, ins_cons(~A, ~cmp, y, h, S.ins(~A, ~cmp, x, t), False{}, eyh)) : {Con{h, S.ins(~A, ~cmp, x, S.ins(~A, ~cmp, y, t))} == _ : List<&2, A>}
      LL.cons_cong(A, h, S.ins(~A, ~cmp, x, S.ins(~A, ~cmp, y, t)), S.ins(~A, ~cmp, y, S.ins(~A, ~cmp, x, t)), ih)

def ins_comm(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +x: A, +y: A, +s: List<&2, A>) -> {S.ins(~A, ~cmp, x, S.ins(~A, ~cmp, y, s)) == S.ins(~A, ~cmp, y, S.ins(~A, ~cmp, x, s)) : List<&2, A>}:
  match s:
    case Nil{}:
      comm_nil(~A, ~cmp, ~o, x, y, S.le(~A, ~cmp, x, y), {==}, S.le(~A, ~cmp, y, x), {==})
    case Con{+h, +t}:
      comm_cons(~A, ~cmp, ~o, x, y, h, t, S.le(~A, ~cmp, x, y), {==}, S.le(~A, ~cmp, y, x), {==}, S.le(~A, ~cmp, x, h), {==}, S.le(~A, ~cmp, y, h), {==}, ins_comm(~A, ~cmp, ~o, x, y, t))
