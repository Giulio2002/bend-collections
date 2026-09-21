import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/array.bend as AR
import ../graph/shift.bend as SH
import ../../spec/common.bend as SC
import ../../spec/doubly_linked_list.bend as DS
import ../../src/doubly_linked_list.bend as D
import ../../types/doubly_linked_list.bend as E
import ./state.bend as ST
import ./facts.bend as F
import ./links.bend as LK
import ./items.bend as IT

# One step of the runtime refines the specification, preserves the invariant
# and raises `fresh` by at most the number of ids it may issue.

def sfresh(~T: Data, sh: ST.Shadow<T>) -> Nat:
  match sh:
    case ST.Sh{tag, +fresh, depth, tv, tp, tn, ord}:
      fresh

def icost(-T: Data, op: E.Op<T>) -> Nat:
  match op:
    case E.PushFront{x}:
      1n
    case E.PushBack{x}:
      1n
    case E.InsertBefore{h, x}:
      1n
    case E.InsertAfter{h, x}:
      1n
    case _:
      0n

def StepOK(~T: Data, sh: ST.Shadow<T>, op: E.Op<T>) -> Type:
  Sigma<&1, &1, ST.Shadow<T>, sh2 => Sigma<&1, &1, E.Obs<T>, o => {D.step(~T, ST.real(~T, sh), op) == (ST.real(~T, sh2), o) : D.DList<T> & E.Obs<T>} & ({ST.good(~T, sh2) == True{} : Bool} & ({(ST.model(~T, sh2), o) == DS.step(T, ST.model(~T, sh), op) : DS.Model<T> & E.Obs<T>} & {Nat.is_le(sfresh(~T, sh2), Nat.add(sfresh(~T, sh), icost(T, op))) == True{} : Bool}))>>

def mk(~T: Data, -sh: ST.Shadow<T>, -op: E.Op<T>, sh2: ST.Shadow<T>, o: E.Obs<T>, e1: {D.step(~T, ST.real(~T, sh), op) == (ST.real(~T, sh2), o) : D.DList<T> & E.Obs<T>}, e2: {ST.good(~T, sh2) == True{} : Bool}, e3: {(ST.model(~T, sh2), o) == DS.step(T, ST.model(~T, sh), op) : DS.Model<T> & E.Obs<T>}, e4: {Nat.is_le(sfresh(~T, sh2), Nat.add(sfresh(~T, sh), icost(T, op))) == True{} : Bool}) -> StepOK(~T, sh, op):
  (sh2, (o, (e1, (e2, (e3, e4)))))

# An unchanged shadow does not grow.
def same_fresh(~T: Data, +sh: ST.Shadow<T>, +op: E.Op<T>) -> {Nat.is_le(sfresh(~T, sh), Nat.add(sfresh(~T, sh), icost(T, op))) == True{} : Bool}:
  N.le_add_right(sfresh(~T, sh), icost(T, op))

# ---- the value arena and the order ----

def lv_get(-T: Data, k: Nat, +xs: List<&2, Maybe<&2, T>>, +p: Nat, +ord: List<&2, Nat>, +h: {ST.lv(T, k, xs, p, ord) == True{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, k) == True{} : Bool}) -> {ST.beq(ST.is_some(T, ST.vat(T, xs, Nat.add(j, p))), ST.lmem(Nat.add(j, p), ord)) == True{} : Bool}:
  match k j:
    case 0n j0:
      Empty.absurd({ST.beq(ST.is_some(T, ST.vat(T, xs, Nat.add(j0, p))), ST.lmem(Nat.add(j0, p), ord)) == True{} : Bool}, L.false_true(Equal.trans(Bool, False{}, Nat.is_lt(j0, 0n), True{}, Equal.sym(Bool, Nat.is_lt(j0, 0n), False{}, N.not_lt_zero(j0)), hj)))
    case 1n+ +m 0n:
      L.and_left(ST.beq(ST.is_some(T, ST.vat(T, xs, p)), ST.lmem(p, ord)), ST.lv(T, m, xs, 1n+p, ord), h)
    case 1n+ +m 1n+ +q:
      L.subst(Nat, z => {ST.beq(ST.is_some(T, ST.vat(T, xs, z)), ST.lmem(z, ord)) == True{} : Bool}, Nat.add(q, 1n+p), 1n+Nat.add(q, p), N.add_succ(q, p),
        lv_get(T, m, xs, 1n+p, ord, L.and_right(ST.beq(ST.is_some(T, ST.vat(T, xs, p)), ST.lmem(p, ord)), ST.lv(T, m, xs, 1n+p, ord), h), q, hj))

def gv_beq(-T: Data, m: Maybe<&2, T>, b: Bool, +h: {ST.beq(ST.is_some(T, m), b) == True{} : Bool}) -> {IT.gv(T, b, m) == m : Maybe<&2, T>}:
  match m b:
    case None{} True{}:
      Empty.absurd({IT.gv(T, True{}, None{}) == None{} : Maybe<&2, T>}, L.false_true(h))
    case None{} False{}:
      {==}
    case Some{v} True{}:
      {==}
    case Some{v} False{}:
      Empty.absurd({IT.gv(T, False{}, Some{v}) == Some{v} : Maybe<&2, T>}, L.false_true(h))

def alllt_mono(+xs: List<&2, Nat>, +a: Nat, +b: Nat, +hab: {Nat.is_le(a, b) == True{} : Bool}, +h: {ST.alllt(xs, a) == True{} : Bool}) -> {ST.alllt(xs, b) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.and_intro(Nat.is_lt(x, b), ST.alllt(t, b), N.lt_le_trans(x, a, b, IT.lt_head(x, t, a, h), hab), alllt_mono(t, a, b, hab, IT.lt_tail(x, t, a, h)))

def lmem_ge(+xs: List<&2, Nat>, +n: Nat, +i: Nat, +h: {ST.alllt(xs, n) == True{} : Bool}, +hi: {Nat.is_le(n, i) == True{} : Bool}) -> {ST.lmem(i, xs) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +e1 = SH.ne_of_lt(x, i, N.lt_le_trans(x, n, i, IT.lt_head(x, t, n, h), hi))
      L.subst(Bool, b => {Bool.or(b, ST.lmem(i, t)) == False{} : Bool}, False{}, Nat.is_eq(x, i), Equal.sym(Bool, Nat.is_eq(x, i), False{}, e1), lmem_ge(t, n, i, IT.lt_tail(x, t, n, h), hi))

# A handle below fresh: the model's lookup is the value arena.
def getv_live(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +i: U32, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), fresh) == True{} : Bool}) -> {DS.getv(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i) == ST.vat(T, AR.slots(Maybe<&2, T>, tv), U32.to_nat(i)) : Maybe<&2, T>}:
  +xs = AR.slots(Maybe<&2, T>, tv)
  +n = U32.to_nat(i)
  +hb = L.subst(Nat, z => {ST.beq(ST.is_some(T, ST.vat(T, xs, z)), ST.lmem(z, ord)) == True{} : Bool}, Nat.add(n, 0n), n, N.add_zero(n), lv_get(T, fresh, xs, 0n, ord, F.g_lv(~T, tag, fresh, depth, tv, tp, tn, ord, h), n, hi))
  Equal.trans(Maybe<&2, T>, DS.getv(T, ST.items(T, xs, ord), i), IT.gv(T, ST.lmem(n, ord), ST.vat(T, xs, n)), ST.vat(T, xs, n),
    IT.getv_items(~T, xs, ord, i, depth, F.g_depth(~T, tag, fresh, depth, tv, tp, tn, ord, h), alllt_mono(ord, fresh, SC.pow2(depth), F.g_fresh(~T, tag, fresh, depth, tv, tp, tn, ord, h), F.g_lt(~T, tag, fresh, depth, tv, tp, tn, ord, h))),
    gv_beq(T, ST.vat(T, xs, n), ST.lmem(n, ord), hb))

# A handle at or above fresh was never issued.
def getv_dead(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +i: U32, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, +hi: {Nat.is_le(fresh, U32.to_nat(i)) == True{} : Bool}) -> {DS.getv(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i) == None{} : Maybe<&2, T>}:
  +xs = AR.slots(Maybe<&2, T>, tv)
  +n = U32.to_nat(i)
  Equal.trans(Maybe<&2, T>, DS.getv(T, ST.items(T, xs, ord), i), IT.gv(T, ST.lmem(n, ord), ST.vat(T, xs, n)), None{},
    IT.getv_items(~T, xs, ord, i, depth, F.g_depth(~T, tag, fresh, depth, tv, tp, tn, ord, h), alllt_mono(ord, fresh, SC.pow2(depth), F.g_fresh(~T, tag, fresh, depth, tv, tp, tn, ord, h), F.g_lt(~T, tag, fresh, depth, tv, tp, tn, ord, h))),
    L.subst(Bool, b => {IT.gv(T, b, ST.vat(T, xs, n)) == None{} : Maybe<&2, T>}, False{}, ST.lmem(n, ord), Equal.sym(Bool, ST.lmem(n, ord), False{}, lmem_ge(ord, fresh, n, F.g_lt(~T, tag, fresh, depth, tv, tp, tn, ord, h), hi)), {==}))

# ---- a step statement about explicit runtime and specification results ----

def GCore(~T: Data, sh: ST.Shadow<T>, rt: D.DList<T> & E.Obs<T>, sp: DS.Model<T> & E.Obs<T>, +c: Nat) -> Type:
  Sigma<&1, &1, ST.Shadow<T>, sh2 => Sigma<&1, &1, E.Obs<T>, o => {rt == (ST.real(~T, sh2), o) : D.DList<T> & E.Obs<T>} & ({ST.good(~T, sh2) == True{} : Bool} & ({(ST.model(~T, sh2), o) == sp : DS.Model<T> & E.Obs<T>} & {Nat.is_le(sfresh(~T, sh2), Nat.add(sfresh(~T, sh), c)) == True{} : Bool}))>>

def gmk(~T: Data, -sh: ST.Shadow<T>, -rt: D.DList<T> & E.Obs<T>, -sp: DS.Model<T> & E.Obs<T>, -c: Nat, sh2: ST.Shadow<T>, o: E.Obs<T>, e1: {rt == (ST.real(~T, sh2), o) : D.DList<T> & E.Obs<T>}, e2: {ST.good(~T, sh2) == True{} : Bool}, e3: {(ST.model(~T, sh2), o) == sp : DS.Model<T> & E.Obs<T>}, e4: {Nat.is_le(sfresh(~T, sh2), Nat.add(sfresh(~T, sh), c)) == True{} : Bool}) -> GCore(~T, sh, rt, sp, c):
  (sh2, (o, (e1, (e2, (e3, e4)))))

def gconv(~T: Data, -sh: ST.Shadow<T>, -rt: D.DList<T> & E.Obs<T>, -rt1: D.DList<T> & E.Obs<T>, -sp: DS.Model<T> & E.Obs<T>, -sp1: DS.Model<T> & E.Obs<T>, +c: Nat, +ert: {rt1 == rt : D.DList<T> & E.Obs<T>}, +esp: {sp1 == sp : DS.Model<T> & E.Obs<T>}, core: GCore(~T, sh, rt1, sp1, c)) -> GCore(~T, sh, rt, sp, c):
  match core:
    case Tuple{sh2, Tuple{o, Tuple{e1, Tuple{e2, Tuple{e3, e4}}}}}:
      gmk(~T, sh, rt, sp, c, sh2, o, Equal.trans(D.DList<T> & E.Obs<T>, rt, rt1, (ST.real(~T, sh2), o), Equal.sym(D.DList<T> & E.Obs<T>, rt1, rt, ert), e1), e2, Equal.trans(DS.Model<T> & E.Obs<T>, (ST.model(~T, sh2), o), sp1, sp, e3, esp), e4)

# The shadow is unchanged.
def gsame(~T: Data, +sh: ST.Shadow<T>, -rt: D.DList<T> & E.Obs<T>, -sp: DS.Model<T> & E.Obs<T>, +c: Nat, +h: {ST.good(~T, sh) == True{} : Bool}, +o: E.Obs<T>, e1: {rt == (ST.real(~T, sh), o) : D.DList<T> & E.Obs<T>}, e3: {(ST.model(~T, sh), o) == sp : DS.Model<T> & E.Obs<T>}) -> GCore(~T, sh, rt, sp, c):
  gmk(~T, sh, rt, sp, c, sh, o, e1, h, e3, N.le_add_right(sfresh(~T, sh), c))
