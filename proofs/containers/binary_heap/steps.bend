import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/list.bend as LL
import ../../lib/order.bend as O
import ../../lib/u32.bend as U
import ../../lib/array.bend as AR
import ../../lib/spec_common.bend as SC
import ./spec.bend as S
import ../../../src/containers/binary_heap.bend as H
import ../../../src/containers/types/binary_heap.bend as E
import ./idx.bend as IX
import ./u32idx.bend as UX
import ./slots.bend as SL
import ./vals.bend as V
import ./root.bend as RT
import ./state.bend as ST
import ./push.bend as PU
import ./pop.bend as PO
import ./sorted.bend as SO
import ./budget.bend as BG

# One actual public operation on a good shadow's block yields the block of a
# new good shadow, and (abstract state, observation) equals the spec step.
#
# The fourth component bounds the new depth: a push doubles the block at most
# once and from_list at most once per element it pushes; every other
# operation leaves the depth alone. The capacity premise itself is stated in
# terms of the heap's size (see step_ok below), which is what lets the trace
# law carry a single premise for a whole operation list (trace.bend).

def pushcost(~A: Data, op: E.Op<A>) -> Nat:
  match op:
    case E.Length{}:
      0n
    case E.Push{x}:
      1n
    case E.Peek{}:
      0n
    case E.Pop{}:
      0n
    case E.FromList{items}:
      SC.length(A, items)
    case E.ToSortedList{}:
      0n

def StepOK(~A: Data, ~cmp: A -> A -> Cmp, sh: ST.Shadow<A>, op: E.Op<A>) -> Type:
  Sigma<&1, &1, ST.Shadow<A>, sh2 => Sigma<&1, &1, E.Obs<A>, o => {H.step(~A, ~cmp, ST.real(~A, sh), op) == (ST.real(~A, sh2), o) : H.Heap<A> & E.Obs<A>} & ({ST.good(~A, ~cmp, sh2) == True{} : Bool} & ({(ST.model(~A, ~cmp, sh2), o) == S.step(~A, ~cmp, ST.model(~A, ~cmp, sh), op) : List<&2, A> & E.Obs<A>} & {Nat.is_le(ST.sh_depth(~A, sh2), Nat.add(ST.sh_depth(~A, sh), pushcost(~A, op))) == True{} : Bool}))>>

def mk(~A: Data, ~cmp: A -> A -> Cmp, -sh: ST.Shadow<A>, -op: E.Op<A>, sh2: ST.Shadow<A>, o: E.Obs<A>, e1: {H.step(~A, ~cmp, ST.real(~A, sh), op) == (ST.real(~A, sh2), o) : H.Heap<A> & E.Obs<A>}, e2: {ST.good(~A, ~cmp, sh2) == True{} : Bool}, e3: {(ST.model(~A, ~cmp, sh2), o) == S.step(~A, ~cmp, ST.model(~A, ~cmp, sh), op) : List<&2, A> & E.Obs<A>}, e4: {Nat.is_le(ST.sh_depth(~A, sh2), Nat.add(ST.sh_depth(~A, sh), pushcost(~A, op))) == True{} : Bool}) -> StepOK(~A, ~cmp, sh, op):
  (sh2, (o, (e1, (e2, (e3, e4)))))

def le_same(+d: Nat) -> {Nat.is_le(d, Nat.add(d, 0n)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(d, 0n), d, N.add_zero(d)) : {Nat.is_le(d, _) == True{} : Bool}
  N.le_refl(d)

def le_succ_add(+d: Nat) -> {Nat.is_le(1n+d, Nat.add(d, 1n)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(d, 1n), 1n+Nat.add(d, 0n), N.add_succ(d, 0n)) : {Nat.is_le(1n+d, _) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(d, 0n), d, N.add_zero(d)) : {Nat.is_le(1n+d, 1n+_) == True{} : Bool}
  N.le_refl(1n+d)

# the empty/nonempty decision the implementation makes, in Nat
def empty_bridge(+size: Nat, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hs: {Nat.is_le(size, SC.pow2(depth)) == True{} : Bool}) -> {U32.is_eq(U32.from_nat(size), U32.from_nat(0n)) == Nat.is_eq(size, 0n) : Bool}:
  UX.eq_bridge(size, 0n, 1n+depth, hd,
    N.le_lt_trans(size, SC.pow2(depth), SC.pow2(1n+depth), hs, N.pow2_lt_succ(depth)),
    N.lt_le_trans(0n, SC.pow2(depth), SC.pow2(1n+depth), N.succ_le_lt(0n, SC.pow2(depth), N.pow2_pos(depth)), N.lt_le(SC.pow2(depth), SC.pow2(1n+depth), N.pow2_lt_succ(depth))))

# ---- length ----

def length_ok(~A: Data, ~cmp: A -> A -> Cmp, +size: Nat, +depth: Nat, +t: AR.Tree<Maybe<&2, A>>, +g: {ST.good(~A, ~cmp, ST.Sh{size, depth, t}) == True{} : Bool}) -> StepOK(~A, ~cmp, ST.Sh{size, depth, t}, E.Length{}):
  mk(~A, ~cmp, ST.Sh{size, depth, t}, E.Length{}, ST.Sh{size, depth, t}, E.ONat{size}, {==}, g,
    Equal.cong(Nat, List<&2, A> & E.Obs<A>, k => (ST.model(~A, ~cmp, ST.Sh{size, depth, t}), E.ONat{k}), size, SC.length(A, ST.model(~A, ~cmp, ST.Sh{size, depth, t})),
      Equal.sym(Nat, SC.length(A, ST.model(~A, ~cmp, ST.Sh{size, depth, t})), size, RT.model_length(~A, ~cmp, AR.slots(Maybe<&2, A>, t), size, ST.g_lay(~A, ~cmp, size, depth, t, g)))),
    le_same(depth))

# ---- peek ----

def peek_at(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +m: Nat, +depth: Nat, +t: AR.Tree<Maybe<&2, A>>, +root: A, +g: {ST.good(~A, ~cmp, ST.Sh{1n+m, depth, t}) == True{} : Bool}, +h0: {SL.slot(~A, AR.slots(Maybe<&2, A>, t), 0n) == Some{root} : Maybe<&2, A>}) -> StepOK(~A, ~cmp, ST.Sh{1n+m, depth, t}, E.Peek{}):
  +hd = ST.g_depth(~A, ~cmp, 1n+m, depth, t, g)
  +pf = ST.g_perfect(~A, ~cmp, 1n+m, depth, t, g)
  +hs = ST.g_size(~A, ~cmp, 1n+m, depth, t, g)
  mk(~A, ~cmp, ST.Sh{1n+m, depth, t}, E.Peek{}, ST.Sh{1n+m, depth, t}, E.OItem{Done{root}},
    %Equal.sym(Bool, U32.is_eq(U32.from_nat(1n+m), U32.from_nat(0n)), Nat.is_eq(1n+m, 0n), empty_bridge(1n+m, depth, hd, hs)) : {H.obs_item(~A, H.peek_go(~A, 1n+m, U32.from_nat(1n+m), depth, U.pow2u(depth), AR.thaw(Maybe<&2, A>, t), _)) == (ST.real(~A, ST.Sh{1n+m, depth, t}), E.OItem{Done{root}}) : H.Heap<A> & E.Obs<A>}
    %Equal.sym(Array<Maybe<&2, A>> & Maybe<&2, A>, Array.get(Maybe<&2, A>, AR.thaw(Maybe<&2, A>, t), 0), (AR.thaw(Maybe<&2, A>, t), Some{root}), PO.get_root(~A, depth, t, root, ST.depth_lt32(depth, hd), pf, h0)) : {H.obs_item(~A, H.peek_found(~A, 1n+m, U32.from_nat(1n+m), depth, U.pow2u(depth), _)) == (ST.real(~A, ST.Sh{1n+m, depth, t}), E.OItem{Done{root}}) : H.Heap<A> & E.Obs<A>}
    {==},
    g,
    Equal.cong(List<&2, A>, List<&2, A> & E.Obs<A>, zs => (ST.model(~A, ~cmp, ST.Sh{1n+m, depth, t}), E.OItem{S.item(A, SC.head(A, zs))}), Con{root, V.msort(~A, ~cmp, V.vals(~A, SC.update(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t), 0n, None{}), 1n+m))}, ST.model(~A, ~cmp, ST.Sh{1n+m, depth, t}),
      Equal.sym(List<&2, A>, ST.model(~A, ~cmp, ST.Sh{1n+m, depth, t}), Con{root, V.msort(~A, ~cmp, V.vals(~A, SC.update(Maybe<&2, A>, AR.slots(Maybe<&2, A>, t), 0n, None{}), 1n+m))},
        RT.head_root(~A, ~cmp, ~o, AR.slots(Maybe<&2, A>, t), 1n+m, root, N.succ_le_lt(0n, 1n+m, N.zero_le(m)), ST.g_ho(~A, ~cmp, 1n+m, depth, t, g), ST.g_lay(~A, ~cmp, 1n+m, depth, t, g), h0))),
    le_same(depth))

def peek_some(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +m: Nat, +depth: Nat, +t: AR.Tree<Maybe<&2, A>>, +g: {ST.good(~A, ~cmp, ST.Sh{1n+m, depth, t}) == True{} : Bool}, sig: Sigma<&1, &1, A, v => {SL.slot(~A, AR.slots(Maybe<&2, A>, t), 0n) == Some{v} : Maybe<&2, A>}>) -> StepOK(~A, ~cmp, ST.Sh{1n+m, depth, t}, E.Peek{}):
  match sig:
    case Tuple{+root, +h0}:
      peek_at(~A, ~cmp, ~o, m, depth, t, root, g, h0)

def peek_ok(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), size: Nat, +depth: Nat, +t: AR.Tree<Maybe<&2, A>>, +g: {ST.good(~A, ~cmp, ST.Sh{size, depth, t}) == True{} : Bool}) -> StepOK(~A, ~cmp, ST.Sh{size, depth, t}, E.Peek{}):
  match size:
    case 0n:
      mk(~A, ~cmp, ST.Sh{0n, depth, t}, E.Peek{}, ST.Sh{0n, depth, t}, E.OItem{Fail{E.EmptyHeap{}}}, {==}, g, {==}, le_same(depth))
    case 1n+ +m:
      peek_some(~A, ~cmp, ~o, m, depth, t, g,
        SL.slot_some(~A, SL.slot(~A, AR.slots(Maybe<&2, A>, t), 0n), SL.lay_at(~A, AR.slots(Maybe<&2, A>, t), 1n+m, 0n, ST.g_lay(~A, ~cmp, 1n+m, depth, t, g), N.succ_le_lt(0n, 1n+m, N.zero_le(m)))))

def or_true(b: Bool) -> {Bool.or(b, True{}) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# ---- push ----

def push_step(~A: Data, ~cmp: A -> A -> Cmp, +size: Nat, +depth: Nat, +t: AR.Tree<Maybe<&2, A>>, +x: A, r: PU.PushOK(~A, ~cmp, ST.Sh{size, depth, t}, x)) -> StepOK(~A, ~cmp, ST.Sh{size, depth, t}, E.Push{x}):
  match r:
    case Tuple{+sh2, Tuple{ereal, Tuple{g2, Tuple{ems, edd}}}}:
      mk(~A, ~cmp, ST.Sh{size, depth, t}, E.Push{x}, sh2, E.OUnit{},
        Equal.cong(H.Heap<A>, H.Heap<A> & E.Obs<A>, hh => (hh, E.OUnit{}), H.push(~A, ~cmp, ST.real(~A, ST.Sh{size, depth, t}), x), ST.real(~A, sh2), ereal),
        g2,
        Equal.cong(List<&2, A>, List<&2, A> & E.Obs<A>, zs => (zs, E.OUnit{}), ST.model(~A, ~cmp, sh2), S.ins(~A, ~cmp, x, ST.model(~A, ~cmp, ST.Sh{size, depth, t})), ems),
        N.le_trans(ST.sh_depth(~A, sh2), 1n+depth, Nat.add(depth, 1n), edd, le_succ_add(depth)))

def push_ok(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +size: Nat, +depth: Nat, +t: AR.Tree<Maybe<&2, A>>, +x: A, +g: {ST.good(~A, ~cmp, ST.Sh{size, depth, t}) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hs: {Nat.is_lt(size, SC.pow2(q)) == True{} : Bool}) -> StepOK(~A, ~cmp, ST.Sh{size, depth, t}, E.Push{x}):
  push_step(~A, ~cmp, size, depth, t, x,
    PU.push_ok(~A, ~cmp, ~o, size, depth, t, x, g, BG.room_or(size, depth, q, hq, hs), Nat.is_lt(size, SC.pow2(depth)), {==}))

# ---- pop ----

def pop_step(~A: Data, ~cmp: A -> A -> Cmp, +size: Nat, +depth: Nat, +t: AR.Tree<Maybe<&2, A>>, r: PO.PopRes(~A, ~cmp, ST.Sh{size, depth, t})) -> StepOK(~A, ~cmp, ST.Sh{size, depth, t}, E.Pop{}):
  match r:
    case Tuple{+sh2, Tuple{+res, Tuple{ereal, Tuple{g2, Tuple{espec, edep}}}}}:
      mk(~A, ~cmp, ST.Sh{size, depth, t}, E.Pop{}, sh2, E.OItem{res},
        Equal.cong(H.Heap<A> & Result<&2, &2, E.Error, A>, H.Heap<A> & E.Obs<A>, rr => H.obs_item(~A, rr), H.pop(~A, ~cmp, ST.real(~A, ST.Sh{size, depth, t})), (ST.real(~A, sh2), res), ereal),
        g2,
        espec,
        L.subst(Nat, z => {Nat.is_le(z, Nat.add(depth, 0n)) == True{} : Bool}, depth, ST.sh_depth(~A, sh2), Equal.sym(Nat, ST.sh_depth(~A, sh2), depth, edep), le_same(depth)))

def pop_ok(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +size: Nat, +depth: Nat, +t: AR.Tree<Maybe<&2, A>>, +g: {ST.good(~A, ~cmp, ST.Sh{size, depth, t}) == True{} : Bool}) -> StepOK(~A, ~cmp, ST.Sh{size, depth, t}, E.Pop{}):
  pop_step(~A, ~cmp, size, depth, t, PO.pop_ok(~A, ~cmp, ~o, size, depth, t, g))

# ---- to_sorted_list ----

def sorted_ok(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +size: Nat, +depth: Nat, +t: AR.Tree<Maybe<&2, A>>, +g: {ST.good(~A, ~cmp, ST.Sh{size, depth, t}) == True{} : Bool}) -> StepOK(~A, ~cmp, ST.Sh{size, depth, t}, E.ToSortedList{}):
  mk(~A, ~cmp, ST.Sh{size, depth, t}, E.ToSortedList{}, ST.Sh{size, depth, t}, E.OList{ST.model(~A, ~cmp, ST.Sh{size, depth, t})},
    Equal.cong(H.Heap<A> & List<&2, A>, H.Heap<A> & E.Obs<A>, rr => H.obs_list(~A, rr), H.to_sorted_list(~A, ~cmp, ST.real(~A, ST.Sh{size, depth, t})), (ST.real(~A, ST.Sh{size, depth, t}), ST.model(~A, ~cmp, ST.Sh{size, depth, t})),
      SO.to_sorted_ok(~A, ~cmp, ~o, size, depth, t, g)),
    g, {==}, le_same(depth))

# ---- from_list ----
#
# from_list replaces the heap by repeated push, so the capacity premise it
# carries is one doubling per element (the same conservative accounting the
# deque uses for its push budget).

def add_le_r(+a: Nat, +b: Nat, +c: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, c), Nat.add(b, c)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(a, c), Nat.add(c, a), N.add_comm(a, c)) : {Nat.is_le(_, Nat.add(b, c)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(b, c), Nat.add(c, b), N.add_comm(b, c)) : {Nat.is_le(Nat.add(c, a), _) == True{} : Bool}
  N.le_add_left(a, b, c, h)

def add_succ_l(+d: Nat, +l: Nat) -> {Nat.add(1n+d, l) == 1n+Nat.add(d, l) : Nat}:
  Equal.trans(Nat, Nat.add(1n+d, l), Nat.add(l, 1n+d), 1n+Nat.add(d, l),
    N.add_comm(1n+d, l),
    Equal.trans(Nat, Nat.add(l, 1n+d), 1n+Nat.add(l, d), 1n+Nat.add(d, l),
      N.add_succ(l, d),
      N.succ_cong(Nat.add(l, d), Nat.add(d, l), N.add_comm(l, d))))

def add_shift(+d: Nat, +l: Nat) -> {Nat.add(d, 1n+l) == Nat.add(1n+d, l) : Nat}:
  Equal.trans(Nat, Nat.add(d, 1n+l), 1n+Nat.add(d, l), Nat.add(1n+d, l),
    N.add_succ(d, l),
    Equal.sym(Nat, Nat.add(1n+d, l), 1n+Nat.add(d, l), add_succ_l(d, l)))

# the size budget after pushing y onto sh
def budget_rest(~A: Data, ~cmp: A -> A -> Cmp, +y: A, +rest: List<&2, A>, +sh: ST.Shadow<A>, +sh1: ST.Shadow<A>, +q: Nat, +g: {ST.good(~A, ~cmp, sh) == True{} : Bool}, +g1: {ST.good(~A, ~cmp, sh1) == True{} : Bool}, +ems: {ST.model(~A, ~cmp, sh1) == S.ins(~A, ~cmp, y, ST.model(~A, ~cmp, sh)) : List<&2, A>}, +h: {Nat.is_lt(Nat.add(ST.sh_size(~A, sh), 1n+SC.length(A, rest)), SC.pow2(q)) == True{} : Bool}) -> {Nat.is_lt(Nat.add(ST.sh_size(~A, sh1), SC.length(A, rest)), SC.pow2(q)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(Nat.add(z, SC.length(A, rest)), SC.pow2(q)) == True{} : Bool}, 1n+ST.sh_size(~A, sh), ST.sh_size(~A, sh1), Equal.sym(Nat, ST.sh_size(~A, sh1), 1n+ST.sh_size(~A, sh), BG.push_size(~A, ~cmp, y, sh, sh1, g, g1, ems)),
    L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(q)) == True{} : Bool}, Nat.add(ST.sh_size(~A, sh), 1n+SC.length(A, rest)), Nat.add(1n+ST.sh_size(~A, sh), SC.length(A, rest)), add_shift(ST.sh_size(~A, sh), SC.length(A, rest)), h))

def budget_shift(+d: Nat, +l: Nat) -> {Nat.is_le(Nat.add(1n+d, l), Nat.add(d, 1n+l)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(z, Nat.add(d, 1n+l)) == True{} : Bool}, Nat.add(d, 1n+l), Nat.add(1n+d, l), add_shift(d, l), N.le_refl(Nat.add(d, 1n+l)))

def FromOK(~A: Data, ~cmp: A -> A -> Cmp, ys: List<&2, A>, sh: ST.Shadow<A>) -> Type:
  Sigma<&1, &1, ST.Shadow<A>, sh2 => {H.from_list_go(~A, ~cmp, ys, ST.real(~A, sh)) == ST.real(~A, sh2) : H.Heap<A>} & ({ST.good(~A, ~cmp, sh2) == True{} : Bool} & ({ST.model(~A, ~cmp, sh2) == S.from_list(~A, ~cmp, ys, ST.model(~A, ~cmp, sh)) : List<&2, A>} & {Nat.is_le(ST.sh_depth(~A, sh2), Nat.add(ST.sh_depth(~A, sh), SC.length(A, ys))) == True{} : Bool}))>

def FromRec(~A: Data, ~cmp: A -> A -> Cmp, rest: List<&2, A>, +q: Nat) -> Type:
  @+sh1: ST.Shadow<A> -> @+g1: {ST.good(~A, ~cmp, sh1) == True{} : Bool} -> @+r1: {Nat.is_lt(Nat.add(ST.sh_size(~A, sh1), SC.length(A, rest)), SC.pow2(q)) == True{} : Bool} -> FromOK(~A, ~cmp, rest, sh1)

def from_rest(~A: Data, ~cmp: A -> A -> Cmp, +y: A, +rest: List<&2, A>, +sh: ST.Shadow<A>, +sh1: ST.Shadow<A>, +ereal: {H.push(~A, ~cmp, ST.real(~A, sh), y) == ST.real(~A, sh1) : H.Heap<A>}, +ems: {ST.model(~A, ~cmp, sh1) == S.ins(~A, ~cmp, y, ST.model(~A, ~cmp, sh)) : List<&2, A>}, +edd: {Nat.is_le(ST.sh_depth(~A, sh1), 1n+ST.sh_depth(~A, sh)) == True{} : Bool}, r: FromOK(~A, ~cmp, rest, sh1)) -> FromOK(~A, ~cmp, Con{y, rest}, sh):
  match r:
    case Tuple{+sh2, Tuple{ereal2, Tuple{g2, Tuple{ems2, edd2}}}}:
      (sh2,
       (Equal.trans(H.Heap<A>, H.from_list_go(~A, ~cmp, Con{y, rest}, ST.real(~A, sh)), H.from_list_go(~A, ~cmp, rest, ST.real(~A, sh1)), ST.real(~A, sh2),
          Equal.cong(H.Heap<A>, H.Heap<A>, hh => H.from_list_go(~A, ~cmp, rest, hh), H.push(~A, ~cmp, ST.real(~A, sh), y), ST.real(~A, sh1), ereal),
          ereal2),
        (g2,
         (Equal.trans(List<&2, A>, ST.model(~A, ~cmp, sh2), S.from_list(~A, ~cmp, rest, ST.model(~A, ~cmp, sh1)), S.from_list(~A, ~cmp, Con{y, rest}, ST.model(~A, ~cmp, sh)),
            ems2,
            Equal.cong(List<&2, A>, List<&2, A>, zs => S.from_list(~A, ~cmp, rest, zs), ST.model(~A, ~cmp, sh1), S.ins(~A, ~cmp, y, ST.model(~A, ~cmp, sh)), ems)),
          N.le_trans(ST.sh_depth(~A, sh2), Nat.add(ST.sh_depth(~A, sh1), SC.length(A, rest)), Nat.add(ST.sh_depth(~A, sh), 1n+SC.length(A, rest)),
            edd2,
            N.le_trans(Nat.add(ST.sh_depth(~A, sh1), SC.length(A, rest)), Nat.add(1n+ST.sh_depth(~A, sh), SC.length(A, rest)), Nat.add(ST.sh_depth(~A, sh), 1n+SC.length(A, rest)),
              add_le_r(ST.sh_depth(~A, sh1), 1n+ST.sh_depth(~A, sh), SC.length(A, rest), edd),
              budget_shift(ST.sh_depth(~A, sh), SC.length(A, rest))))))))

def from_push(~A: Data, ~cmp: A -> A -> Cmp, +y: A, +rest: List<&2, A>, +sh: ST.Shadow<A>, +g: {ST.good(~A, ~cmp, sh) == True{} : Bool}, +q: Nat, +room: {Nat.is_lt(Nat.add(ST.sh_size(~A, sh), 1n+SC.length(A, rest)), SC.pow2(q)) == True{} : Bool}, rec: FromRec(~A, ~cmp, rest, q), +sh1: ST.Shadow<A>, +ereal: {H.push(~A, ~cmp, ST.real(~A, sh), y) == ST.real(~A, sh1) : H.Heap<A>}, +g1: {ST.good(~A, ~cmp, sh1) == True{} : Bool}, +ems: {ST.model(~A, ~cmp, sh1) == S.ins(~A, ~cmp, y, ST.model(~A, ~cmp, sh)) : List<&2, A>}, +edd: {Nat.is_le(ST.sh_depth(~A, sh1), 1n+ST.sh_depth(~A, sh)) == True{} : Bool}) -> FromOK(~A, ~cmp, Con{y, rest}, sh):
  from_rest(~A, ~cmp, y, rest, sh, sh1, ereal, ems, edd,
    rec(sh1, g1, budget_rest(~A, ~cmp, y, rest, sh, sh1, q, g, g1, ems, room)))

def from_cons(~A: Data, ~cmp: A -> A -> Cmp, +y: A, +rest: List<&2, A>, +sh: ST.Shadow<A>, +g: {ST.good(~A, ~cmp, sh) == True{} : Bool}, +q: Nat, +room: {Nat.is_lt(Nat.add(ST.sh_size(~A, sh), 1n+SC.length(A, rest)), SC.pow2(q)) == True{} : Bool}, rec: FromRec(~A, ~cmp, rest, q), r: PU.PushOK(~A, ~cmp, sh, y)) -> FromOK(~A, ~cmp, Con{y, rest}, sh):
  match r:
    case Tuple{sh1, Tuple{ereal, Tuple{g1, Tuple{ems, edd}}}}:
      from_push(~A, ~cmp, y, rest, sh, g, q, room, rec, sh1, ereal, g1, ems, edd)

def from_list_ok(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), ys: List<&2, A>, sh: ST.Shadow<A>, +g: {ST.good(~A, ~cmp, sh) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +room: {Nat.is_lt(Nat.add(ST.sh_size(~A, sh), SC.length(A, ys)), SC.pow2(q)) == True{} : Bool}) -> FromOK(~A, ~cmp, ys, sh):
  match ys sh:
    case Nil{} ST.Sh{+size, +depth, +t}:
      (ST.Sh{size, depth, t}, ({==}, (g, ({==}, le_same(depth)))))
    case Con{+y, +rest} ST.Sh{+size, +depth, +t}:
      from_cons(~A, ~cmp, y, rest, ST.Sh{size, depth, t}, g, q, room,
        sh1 => g1 => r1 => from_list_ok(~A, ~cmp, ~o, rest, sh1, g1, q, hq, r1),
        PU.push_ok(~A, ~cmp, ~o, size, depth, t, y, g,
          BG.room_or(size, depth, q, hq, N.le_lt_trans(size, Nat.add(size, 1n+SC.length(A, rest)), SC.pow2(q), N.le_add_right(size, 1n+SC.length(A, rest)), room)),
          Nat.is_lt(size, SC.pow2(depth)), {==}))

def le_add_zero(+l: Nat, +d: Nat) -> {Nat.is_le(Nat.add(0n, l), Nat.add(d, l)) == True{} : Bool}:
  add_le_r(0n, d, l, N.zero_le(d))

def from_list_step(~A: Data, ~cmp: A -> A -> Cmp, +size: Nat, +depth: Nat, +t: AR.Tree<Maybe<&2, A>>, +ys: List<&2, A>, r: FromOK(~A, ~cmp, ys, ST.initial(~A))) -> StepOK(~A, ~cmp, ST.Sh{size, depth, t}, E.FromList{ys}):
  match r:
    case Tuple{+sh2, Tuple{ereal, Tuple{g2, Tuple{ems, edd}}}}:
      mk(~A, ~cmp, ST.Sh{size, depth, t}, E.FromList{ys}, sh2, E.OUnit{},
        %Equal.sym(H.Heap<A>, H.new(~A), ST.real(~A, ST.initial(~A)), ST.new_real(~A)) : {(H.from_list_go(~A, ~cmp, ys, _), E.OUnit{}) == (ST.real(~A, sh2), E.OUnit{}) : H.Heap<A> & E.Obs<A>}
        Equal.cong(H.Heap<A>, H.Heap<A> & E.Obs<A>, hh => (hh, E.OUnit{}), H.from_list_go(~A, ~cmp, ys, ST.real(~A, ST.initial(~A))), ST.real(~A, sh2), ereal),
        g2,
        Equal.cong(List<&2, A>, List<&2, A> & E.Obs<A>, zs => (zs, E.OUnit{}), ST.model(~A, ~cmp, sh2), S.from_list(~A, ~cmp, ys, Nil{}), ems),
        N.le_trans(ST.sh_depth(~A, sh2), Nat.add(0n, SC.length(A, ys)), Nat.add(depth, SC.length(A, ys)), edd, le_add_zero(SC.length(A, ys), depth)))

# ---- every operation ----
#
# `room` is the capacity condition of the representation for this step, in
# terms of the heap's size: size + pushcost(op) < 2^q with q <= 31. A push
# doubles only a full block, where 2^depth = size < 2^q forces depth < 31, so
# every slot index stays a representable U32. It is the only premise besides
# the invariant, and trace.bend discharges it for a whole operation list.

def step_ok(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), sh: ST.Shadow<A>, op: E.Op<A>, +g: {ST.good(~A, ~cmp, sh) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +room: {Nat.is_lt(Nat.add(ST.sh_size(~A, sh), pushcost(~A, op)), SC.pow2(q)) == True{} : Bool}) -> StepOK(~A, ~cmp, sh, op):
  match sh op:
    case ST.Sh{+size, +depth, +t} E.Length{}:
      length_ok(~A, ~cmp, size, depth, t, g)
    case ST.Sh{+size, +depth, +t} E.Push{+x}:
      push_ok(~A, ~cmp, ~o, size, depth, t, x, g, q, hq, N.le_lt_trans(size, Nat.add(size, 1n), SC.pow2(q), N.le_add_right(size, 1n), room))
    case ST.Sh{+size, +depth, +t} E.Peek{}:
      peek_ok(~A, ~cmp, ~o, size, depth, t, g)
    case ST.Sh{+size, +depth, +t} E.Pop{}:
      pop_ok(~A, ~cmp, ~o, size, depth, t, g)
    case ST.Sh{+size, +depth, +t} E.FromList{+ys}:
      from_list_step(~A, ~cmp, size, depth, t, ys,
        from_list_ok(~A, ~cmp, ~o, ys, ST.initial(~A), ST.new_good(~A, ~cmp), q, hq,
          N.le_lt_trans(Nat.add(0n, SC.length(A, ys)), Nat.add(size, SC.length(A, ys)), SC.pow2(q), le_add_zero(SC.length(A, ys), size), room)))
    case ST.Sh{+size, +depth, +t} E.ToSortedList{}:
      sorted_ok(~A, ~cmp, ~o, size, depth, t, g)
