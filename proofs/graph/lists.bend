import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/order.bend as O
import ../balanced_search_tree/sorted.bend as SO
import ../../spec/common.bend as SC
import ../../spec/balanced_search_tree.bend as S
import ../../types/balanced_search_tree.bend as BE
import ./state.bend as ST
import ./lb.bend as LB

# List-level editing used by the neighbour-block updates: deleting or
# inserting at an index, their images under `uset`, and the facts that doing
# so AT THE LOWER BOUND is the specification's `del` / `ins`.

# ---- index editing of plain U32 lists ----

def dl(ws: List<&2, U32>, l: Nat) -> List<&2, U32>:
  match ws l:
    case Nil{} l0:
      Nil{}
    case Con{w, t} 0n:
      t
    case Con{w, t} 1n+p:
      Con{w, dl(t, p)}

def il(ws: List<&2, U32>, l: Nat, +x: U32) -> List<&2, U32>:
  match ws l:
    case ys 0n:
      Con{x, ys}
    case Nil{} 1n+p:
      Con{x, Nil{}}
    case Con{w, t} 1n+p:
      Con{w, il(t, p, x)}

def uset_dl(+ws: List<&2, U32>, +l: Nat) -> {ST.uset(dl(ws, l)) == LB.del_at(Unit, ST.uset(ws), l) : List<&2, BE.Entry<U32, Unit>>}:
  match ws l:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      {==}
    case Con{+w, +t} 0n:
      {==}
    case Con{+w, +t} 1n+p:
      Equal.cong(List<&2, BE.Entry<U32, Unit>>, List<&2, BE.Entry<U32, Unit>>, z => Con{BE.Entry{w, Unit{}}, z}, ST.uset(dl(t, p)), LB.del_at(Unit, ST.uset(t), p), uset_dl(t, p))

def uset_il(+ws: List<&2, U32>, +l: Nat, +x: U32) -> {ST.uset(il(ws, l, x)) == LB.ins_at(Unit, ST.uset(ws), l, BE.Entry{x, Unit{}}) : List<&2, BE.Entry<U32, Unit>>}:
  match ws l:
    case Nil{} 0n:
      {==}
    case Con{w0, t0} 0n:
      {==}
    case Nil{} 1n+p:
      {==}
    case Con{+w, +t} 1n+p:
      Equal.cong(List<&2, BE.Entry<U32, Unit>>, List<&2, BE.Entry<U32, Unit>>, z => Con{BE.Entry{w, Unit{}}, z}, ST.uset(il(t, p, x)), LB.ins_at(Unit, ST.uset(t), p, BE.Entry{x, Unit{}}), uset_il(t, p, x))

# A sorted neighbour set is an ascending list.
def above_back(+k: U32, +ws: List<&2, U32>, +h: {SO.above(~U32, ~U32.cmp, Unit, ST.uset(ws), k) == True{} : Bool}) -> {ST.above(k, ws) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{+w, +t}:
      L.and_intro(Cmp.is_lt(U32.cmp(k, w)), ST.above(k, t),
        L.and_left(Cmp.is_lt(U32.cmp(k, w)), SO.above(~U32, ~U32.cmp, Unit, ST.uset(t), k), h),
        above_back(k, t, L.and_right(Cmp.is_lt(U32.cmp(k, w)), SO.above(~U32, ~U32.cmp, Unit, ST.uset(t), k), h)))

def asc_back(+ws: List<&2, U32>, +h: {SO.sorted(~U32, ~U32.cmp, Unit, ST.uset(ws)) == True{} : Bool}) -> {ST.asc(ws) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{+w, +t}:
      L.and_intro(ST.above(w, t), ST.asc(t),
        above_back(w, t, L.and_left(SO.above(~U32, ~U32.cmp, Unit, ST.uset(t), w), SO.sorted(~U32, ~U32.cmp, Unit, ST.uset(t)), h)),
        asc_back(t, L.and_right(SO.above(~U32, ~U32.cmp, Unit, ST.uset(t), w), SO.sorted(~U32, ~U32.cmp, Unit, ST.uset(t)), h)))

# ---- `find`, `del`, `ins` on sorted association lists at the lower bound ----

# Every key above v: v is absent.
def find_none_gt(-V: Data, +es: List<&2, BE.Entry<U32, V>>, +v: U32, +hab: {SO.above(~U32, ~U32.cmp, V, es, v) == True{} : Bool}) -> {S.find(~U32, ~U32.cmp, V, v, es) == None{} : Maybe<&2, V>}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      L.subst(Cmp, c => {S.find_at(U32, V, c, e, S.find(~U32, ~U32.cmp, V, v, t)) == None{} : Maybe<&2, V>}, LT{}, U32.cmp(v, BE.key(U32, V, e)),
        Equal.sym(Cmp, U32.cmp(v, BE.key(U32, V, e)), LT{}, SO.ab_head(~U32, ~U32.cmp, V, e, t, v, hab)),
        find_none_gt(V, t, v, SO.ab_tail(~U32, ~U32.cmp, V, e, t, v, hab)))

def del_none_gt(-V: Data, +es: List<&2, BE.Entry<U32, V>>, +v: U32, +hab: {SO.above(~U32, ~U32.cmp, V, es, v) == True{} : Bool}) -> {S.del(~U32, ~U32.cmp, V, v, es) == es : List<&2, BE.Entry<U32, V>>}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      L.subst(Cmp, c => {S.keep_at(U32, V, S.keep(c), e, S.del(~U32, ~U32.cmp, V, v, t)) == Con{e, t} : List<&2, BE.Entry<U32, V>>}, LT{}, U32.cmp(v, BE.key(U32, V, e)),
        Equal.sym(Cmp, U32.cmp(v, BE.key(U32, V, e)), LT{}, SO.ab_head(~U32, ~U32.cmp, V, e, t, v, hab)),
        LL.cons_cong(BE.Entry<U32, V>, e, S.del(~U32, ~U32.cmp, V, v, t), t, del_none_gt(V, t, v, SO.ab_tail(~U32, ~U32.cmp, V, e, t, v, hab))))

def keys_above_eq(+k: U32, +v: U32, -V: Data, +t: List<&2, BE.Entry<U32, V>>, +ec: {U32.cmp(v, k) == EQ{} : Cmp}, +hab: {SO.above(~U32, ~U32.cmp, V, t, k) == True{} : Bool}) -> {SO.above(~U32, ~U32.cmp, V, t, v) == True{} : Bool}:
  SO.above_eq(~U32, ~U32.cmp, ~O.u32_order, V, t, k, v, hab, LB.flip_eq(v, k, ec))

def DelIH(-V: Data, +t: List<&2, BE.Entry<U32, V>>, +v: U32) -> Type:
  @+hf2: {LB.eq_at(LB.keys_of(V, t), LB.lbx(V, v, t), v) == True{} : Bool} -> {LB.del_at(V, t, LB.lbx(V, v, t)) == S.del(~U32, ~U32.cmp, V, v, t) : List<&2, BE.Entry<U32, V>>}

def AbsIH(-V: Data, +t: List<&2, BE.Entry<U32, V>>, +v: U32) -> Type:
  @+hf2: {S.find(~U32, ~U32.cmp, V, v, t) == None{} : Maybe<&2, V>} -> {S.del(~U32, ~U32.cmp, V, v, t) == t : List<&2, BE.Entry<U32, V>>}

def InsIH(-V: Data, +t: List<&2, BE.Entry<U32, V>>, +v: U32, +x: V) -> Type:
  @+hf2: {LB.eq_at(LB.keys_of(V, t), LB.lbx(V, v, t), v) == True{} : Bool} -> {LB.upd_at(V, t, LB.lbx(V, v, t), BE.Entry{v, x}) == S.ins(~U32, ~U32.cmp, V, v, x, t) : List<&2, BE.Entry<U32, V>>}

# Deleting at the lower bound of a present key is `del`.
def del_found_c(-V: Data, +k: U32, +val: V, +t: List<&2, BE.Entry<U32, V>>, +v: U32, +hs: {SO.sorted(~U32, ~U32.cmp, V, Con{BE.Entry{k, val}, t}) == True{} : Bool}, +hf: {LB.eq_at(LB.keys_of(V, Con{BE.Entry{k, val}, t}), LB.lbx(V, v, Con{BE.Entry{k, val}, t}), v) == True{} : Bool}, c: Cmp, +ec: {U32.cmp(v, k) == c : Cmp}, ih: DelIH(V, t, v)) -> {LB.del_at(V, Con{BE.Entry{k, val}, t}, LB.lbx(V, v, Con{BE.Entry{k, val}, t})) == S.del(~U32, ~U32.cmp, V, v, Con{BE.Entry{k, val}, t}) : List<&2, BE.Entry<U32, V>>}:
  match c:
    case EQ{}:
      +hab = L.and_left(SO.above(~U32, ~U32.cmp, V, t, k), SO.sorted(~U32, ~U32.cmp, V, t), hs)
      L.subst(Cmp, z => {LB.del_at(V, Con{BE.Entry{k, val}, t}, LB.lbx(V, v, Con{BE.Entry{k, val}, t})) == S.keep_at(U32, V, S.keep(z), BE.Entry{k, val}, S.del(~U32, ~U32.cmp, V, v, t)) : List<&2, BE.Entry<U32, V>>}, EQ{}, U32.cmp(v, k), Equal.sym(Cmp, U32.cmp(v, k), EQ{}, ec),
        L.subst(Bool, b => {LB.del_at(V, Con{BE.Entry{k, val}, t}, LB.lbx_step(b, LB.lbx(V, v, t))) == S.del(~U32, ~U32.cmp, V, v, t) : List<&2, BE.Entry<U32, V>>}, False{}, Cmp.is_lt(U32.cmp(k, v)), Equal.sym(Bool, Cmp.is_lt(U32.cmp(k, v)), False{}, LB.eq_not_lt(k, v, LB.flip_eq(v, k, ec))),
          Equal.sym(List<&2, BE.Entry<U32, V>>, S.del(~U32, ~U32.cmp, V, v, t), t, del_none_gt(V, t, v, keys_above_eq(k, v, V, t, ec, hab)))))
    case LT{}:
      Empty.absurd({LB.del_at(V, Con{BE.Entry{k, val}, t}, LB.lbx(V, v, Con{BE.Entry{k, val}, t})) == S.del(~U32, ~U32.cmp, V, v, Con{BE.Entry{k, val}, t}) : List<&2, BE.Entry<U32, V>>},
        L.false_true(
          Equal.trans(Bool, False{}, Cmp.is_eq(U32.cmp(k, v)), True{}, Equal.sym(Bool, Cmp.is_eq(U32.cmp(k, v)), False{}, LB.lt_not_eq(v, k, ec)),
            L.subst(Bool, b => {LB.eq_at(Con{k, LB.keys_of(V, t)}, LB.lbx_step(b, LB.lbx(V, v, t)), v) == True{} : Bool}, Cmp.is_lt(U32.cmp(k, v)), False{}, LB.lt_not_gt(v, k, ec), hf))))
    case GT{}:
      L.subst(Cmp, z => {LB.del_at(V, Con{BE.Entry{k, val}, t}, LB.lbx(V, v, Con{BE.Entry{k, val}, t})) == S.keep_at(U32, V, S.keep(z), BE.Entry{k, val}, S.del(~U32, ~U32.cmp, V, v, t)) : List<&2, BE.Entry<U32, V>>}, GT{}, U32.cmp(v, k), Equal.sym(Cmp, U32.cmp(v, k), GT{}, ec),
        L.subst(Bool, b => {LB.del_at(V, Con{BE.Entry{k, val}, t}, LB.lbx_step(b, LB.lbx(V, v, t))) == Con{BE.Entry{k, val}, S.del(~U32, ~U32.cmp, V, v, t)} : List<&2, BE.Entry<U32, V>>}, True{}, Cmp.is_lt(U32.cmp(k, v)), Equal.sym(Bool, Cmp.is_lt(U32.cmp(k, v)), True{}, LB.gt_flip(v, k, ec)),
          LL.cons_cong(BE.Entry<U32, V>, BE.Entry{k, val}, LB.del_at(V, t, LB.lbx(V, v, t)), S.del(~U32, ~U32.cmp, V, v, t),
            ih(L.subst(Bool, b => {LB.eq_at(Con{k, LB.keys_of(V, t)}, LB.lbx_step(b, LB.lbx(V, v, t)), v) == True{} : Bool}, Cmp.is_lt(U32.cmp(k, v)), True{}, LB.gt_flip(v, k, ec), hf)))))

def del_found(-V: Data, +es: List<&2, BE.Entry<U32, V>>, +v: U32, +hs: {SO.sorted(~U32, ~U32.cmp, V, es) == True{} : Bool}, +hf: {LB.eq_at(LB.keys_of(V, es), LB.lbx(V, v, es), v) == True{} : Bool}) -> {LB.del_at(V, es, LB.lbx(V, v, es)) == S.del(~U32, ~U32.cmp, V, v, es) : List<&2, BE.Entry<U32, V>>}:
  match es:
    case Nil{}:
      {==}
    case Con{BE.Entry{+k, +val}, +t}:
      del_found_c(V, k, val, t, v, hs, hf, U32.cmp(v, k), {==},
        hf2 => del_found(V, t, v, L.and_right(SO.above(~U32, ~U32.cmp, V, t, k), SO.sorted(~U32, ~U32.cmp, V, t), hs), hf2))

# `del` of an absent key changes nothing (no sortedness needed).
def eq_found_absurd(-V: Data, +e: BE.Entry<U32, V>, +t: List<&2, BE.Entry<U32, V>>, +v: U32, +ec: {U32.cmp(v, BE.key(U32, V, e)) == EQ{} : Cmp}, +hf: {S.find(~U32, ~U32.cmp, V, v, Con{e, t}) == None{} : Maybe<&2, V>}) -> Empty:
  match e:
    case BE.Entry{+k, +x}:
      L.false_true(Equal.cong(Maybe<&2, V>, Bool, m => S.is_some(V, m), None{}, Some{x},
        Equal.sym(Maybe<&2, V>, Some{x}, None{}, L.subst(Cmp, z => {S.find_at(U32, V, z, BE.Entry{k, x}, S.find(~U32, ~U32.cmp, V, v, t)) == None{} : Maybe<&2, V>}, U32.cmp(v, k), EQ{}, ec, hf))))

# Replacing at the lower bound of a present key is `ins`.
def del_absent_c(-V: Data, +e: BE.Entry<U32, V>, +t: List<&2, BE.Entry<U32, V>>, +v: U32, c: Cmp, +ec: {U32.cmp(v, BE.key(U32, V, e)) == c : Cmp}, +hf: {S.find(~U32, ~U32.cmp, V, v, Con{e, t}) == None{} : Maybe<&2, V>}, ih: AbsIH(V, t, v)) -> {S.del(~U32, ~U32.cmp, V, v, Con{e, t}) == Con{e, t} : List<&2, BE.Entry<U32, V>>}:
  match c:
    case EQ{}:
      Empty.absurd({S.del(~U32, ~U32.cmp, V, v, Con{e, t}) == Con{e, t} : List<&2, BE.Entry<U32, V>>}, eq_found_absurd(V, e, t, v, ec, hf))
    case LT{}:
      L.subst(Cmp, z => {S.keep_at(U32, V, S.keep(z), e, S.del(~U32, ~U32.cmp, V, v, t)) == Con{e, t} : List<&2, BE.Entry<U32, V>>}, LT{}, U32.cmp(v, BE.key(U32, V, e)), Equal.sym(Cmp, U32.cmp(v, BE.key(U32, V, e)), LT{}, ec),
        LL.cons_cong(BE.Entry<U32, V>, e, S.del(~U32, ~U32.cmp, V, v, t), t, ih(L.subst(Cmp, z => {S.find_at(U32, V, z, e, S.find(~U32, ~U32.cmp, V, v, t)) == None{} : Maybe<&2, V>}, U32.cmp(v, BE.key(U32, V, e)), LT{}, ec, hf))))
    case GT{}:
      L.subst(Cmp, z => {S.keep_at(U32, V, S.keep(z), e, S.del(~U32, ~U32.cmp, V, v, t)) == Con{e, t} : List<&2, BE.Entry<U32, V>>}, GT{}, U32.cmp(v, BE.key(U32, V, e)), Equal.sym(Cmp, U32.cmp(v, BE.key(U32, V, e)), GT{}, ec),
        LL.cons_cong(BE.Entry<U32, V>, e, S.del(~U32, ~U32.cmp, V, v, t), t, ih(L.subst(Cmp, z => {S.find_at(U32, V, z, e, S.find(~U32, ~U32.cmp, V, v, t)) == None{} : Maybe<&2, V>}, U32.cmp(v, BE.key(U32, V, e)), GT{}, ec, hf))))

def del_absent(-V: Data, +es: List<&2, BE.Entry<U32, V>>, +v: U32, +hf: {S.find(~U32, ~U32.cmp, V, v, es) == None{} : Maybe<&2, V>}) -> {S.del(~U32, ~U32.cmp, V, v, es) == es : List<&2, BE.Entry<U32, V>>}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      del_absent_c(V, e, t, v, U32.cmp(v, BE.key(U32, V, e)), {==}, hf, hf2 => del_absent(V, t, v, hf2))

def ins_old_c(-V: Data, +k: U32, +val: V, +t: List<&2, BE.Entry<U32, V>>, +v: U32, +x: V, +hf: {LB.eq_at(LB.keys_of(V, Con{BE.Entry{k, val}, t}), LB.lbx(V, v, Con{BE.Entry{k, val}, t}), v) == True{} : Bool}, c: Cmp, +ec: {U32.cmp(v, k) == c : Cmp}, ih: InsIH(V, t, v, x)) -> {LB.upd_at(V, Con{BE.Entry{k, val}, t}, LB.lbx(V, v, Con{BE.Entry{k, val}, t}), BE.Entry{v, x}) == S.ins(~U32, ~U32.cmp, V, v, x, Con{BE.Entry{k, val}, t}) : List<&2, BE.Entry<U32, V>>}:
  match c:
    case EQ{}:
      L.subst(Cmp, z => {LB.upd_at(V, Con{BE.Entry{k, val}, t}, LB.lbx(V, v, Con{BE.Entry{k, val}, t}), BE.Entry{v, x}) == S.ins_at(~U32, ~U32.cmp, V, z, v, x, BE.Entry{k, val}, t, S.ins(~U32, ~U32.cmp, V, v, x, t)) : List<&2, BE.Entry<U32, V>>}, EQ{}, U32.cmp(v, k), Equal.sym(Cmp, U32.cmp(v, k), EQ{}, ec),
        L.subst(Bool, b => {LB.upd_at(V, Con{BE.Entry{k, val}, t}, LB.lbx_step(b, LB.lbx(V, v, t)), BE.Entry{v, x}) == Con{BE.Entry{v, x}, t} : List<&2, BE.Entry<U32, V>>}, False{}, Cmp.is_lt(U32.cmp(k, v)), Equal.sym(Bool, Cmp.is_lt(U32.cmp(k, v)), False{}, LB.eq_not_lt(k, v, LB.flip_eq(v, k, ec))), {==}))
    case LT{}:
      Empty.absurd({LB.upd_at(V, Con{BE.Entry{k, val}, t}, LB.lbx(V, v, Con{BE.Entry{k, val}, t}), BE.Entry{v, x}) == S.ins(~U32, ~U32.cmp, V, v, x, Con{BE.Entry{k, val}, t}) : List<&2, BE.Entry<U32, V>>},
        L.false_true(
          Equal.trans(Bool, False{}, Cmp.is_eq(U32.cmp(k, v)), True{}, Equal.sym(Bool, Cmp.is_eq(U32.cmp(k, v)), False{}, LB.lt_not_eq(v, k, ec)),
            L.subst(Bool, b => {LB.eq_at(Con{k, LB.keys_of(V, t)}, LB.lbx_step(b, LB.lbx(V, v, t)), v) == True{} : Bool}, Cmp.is_lt(U32.cmp(k, v)), False{}, LB.lt_not_gt(v, k, ec), hf))))
    case GT{}:
      L.subst(Cmp, z => {LB.upd_at(V, Con{BE.Entry{k, val}, t}, LB.lbx(V, v, Con{BE.Entry{k, val}, t}), BE.Entry{v, x}) == S.ins_at(~U32, ~U32.cmp, V, z, v, x, BE.Entry{k, val}, t, S.ins(~U32, ~U32.cmp, V, v, x, t)) : List<&2, BE.Entry<U32, V>>}, GT{}, U32.cmp(v, k), Equal.sym(Cmp, U32.cmp(v, k), GT{}, ec),
        L.subst(Bool, b => {LB.upd_at(V, Con{BE.Entry{k, val}, t}, LB.lbx_step(b, LB.lbx(V, v, t)), BE.Entry{v, x}) == Con{BE.Entry{k, val}, S.ins(~U32, ~U32.cmp, V, v, x, t)} : List<&2, BE.Entry<U32, V>>}, True{}, Cmp.is_lt(U32.cmp(k, v)), Equal.sym(Bool, Cmp.is_lt(U32.cmp(k, v)), True{}, LB.gt_flip(v, k, ec)),
          LL.cons_cong(BE.Entry<U32, V>, BE.Entry{k, val}, LB.upd_at(V, t, LB.lbx(V, v, t), BE.Entry{v, x}), S.ins(~U32, ~U32.cmp, V, v, x, t),
            ih(L.subst(Bool, b => {LB.eq_at(Con{k, LB.keys_of(V, t)}, LB.lbx_step(b, LB.lbx(V, v, t)), v) == True{} : Bool}, Cmp.is_lt(U32.cmp(k, v)), True{}, LB.gt_flip(v, k, ec), hf)))))

def ins_old(-V: Data, +es: List<&2, BE.Entry<U32, V>>, +v: U32, +x: V, +hf: {LB.eq_at(LB.keys_of(V, es), LB.lbx(V, v, es), v) == True{} : Bool}) -> {LB.upd_at(V, es, LB.lbx(V, v, es), BE.Entry{v, x}) == S.ins(~U32, ~U32.cmp, V, v, x, es) : List<&2, BE.Entry<U32, V>>}:
  match es:
    case Nil{}:
      Empty.absurd({LB.upd_at(V, Nil{}, LB.lbx(V, v, Nil{}), BE.Entry{v, x}) == S.ins(~U32, ~U32.cmp, V, v, x, Nil{}) : List<&2, BE.Entry<U32, V>>}, L.false_true(hf))
    case Con{BE.Entry{+k, +val}, +t}:
      ins_old_c(V, k, val, t, v, x, hf, U32.cmp(v, k), {==}, hf2 => ins_old(V, t, v, x, hf2))
