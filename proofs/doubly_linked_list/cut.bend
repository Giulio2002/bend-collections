import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../../spec/common.bend as SC
import ../../spec/doubly_linked_list.bend as DS
import ../../types/doubly_linked_list.bend as E
import ./nodes.bend as NS
import ./links.bend as LK

# The specification's handle operations, stated through the cut of the item
# sequence at the first item with id i: pre (before it) and suf (from it).

def pre(-T: Data, xs: List<&2, E.Item<T>>, +i: Nat) -> List<&2, E.Item<T>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{E.Item{+j, +v}, +t}:
      DS.pick(T, Nat.is_eq(j, i), Nil{}, Con{E.Item{j, v}, pre(T, t, i)})

def suf(-T: Data, xs: List<&2, E.Item<T>>, +i: Nat) -> List<&2, E.Item<T>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{E.Item{+j, +v}, +t}:
      DS.pick(T, Nat.is_eq(j, i), Con{E.Item{j, v}, t}, suf(T, t, i))

def sufok(-T: Data, r: List<&2, E.Item<T>>, +i: Nat) -> Bool:
  match r:
    case Nil{}:
      True{}
    case Con{E.Item{j, v}, t}:
      Nat.is_eq(j, i)

def gets(-T: Data, r: List<&2, E.Item<T>>) -> Maybe<&2, T>:
  match r:
    case Nil{}:
      None{}
    case Con{E.Item{j, v}, t}:
      Some{v}

def ibs(-T: Data, r: List<&2, E.Item<T>>, +it: E.Item<T>) -> List<&2, E.Item<T>>:
  match r:
    case Nil{}:
      Nil{}
    case Con{x, q}:
      Con{it, Con{x, q}}

def ias(-T: Data, r: List<&2, E.Item<T>>, +it: E.Item<T>) -> List<&2, E.Item<T>>:
  match r:
    case Nil{}:
      Nil{}
    case Con{x, q}:
      Con{x, Con{it, q}}

def tl(-T: Data, r: List<&2, E.Item<T>>) -> List<&2, E.Item<T>>:
  match r:
    case Nil{}:
      Nil{}
    case Con{x, q}:
      q

def svs(-T: Data, r: List<&2, E.Item<T>>, +x: T) -> List<&2, E.Item<T>>:
  match r:
    case Nil{}:
      Nil{}
    case Con{E.Item{j, v}, q}:
      Con{E.Item{j, x}, q}

def nxs(-T: Data, r: List<&2, E.Item<T>>) -> Maybe<&2, Nat>:
  match r:
    case Nil{}:
      None{}
    case Con{x, q}:
      LK.fst(NS.ids(T, q), None{})

def pvs(-T: Data, r: List<&2, E.Item<T>>, a: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match r:
    case Nil{}:
      None{}
    case Con{x, q}:
      a

# ---- the cut ----

def cut_c(-T: Data, +j: Nat, +v: T, +t: List<&2, E.Item<T>>, +i: Nat, b: Bool, +eb: {Nat.is_eq(j, i) == b : Bool}, +ih: {t == SC.append(E.Item<T>, pre(T, t, i), suf(T, t, i)) : List<&2, E.Item<T>>}) -> {Con{E.Item{j, v}, t} == SC.append(E.Item<T>, pre(T, Con{E.Item{j, v}, t}, i), suf(T, Con{E.Item{j, v}, t}, i)) : List<&2, E.Item<T>>}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(j, i), True{}, eb) : {Con{E.Item{j, v}, t} == SC.append(E.Item<T>, DS.pick(T, _, Nil{}, Con{E.Item{j, v}, pre(T, t, i)}), DS.pick(T, _, Con{E.Item{j, v}, t}, suf(T, t, i))) : List<&2, E.Item<T>>}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(j, i), False{}, eb) : {Con{E.Item{j, v}, t} == SC.append(E.Item<T>, DS.pick(T, _, Nil{}, Con{E.Item{j, v}, pre(T, t, i)}), DS.pick(T, _, Con{E.Item{j, v}, t}, suf(T, t, i))) : List<&2, E.Item<T>>}
      LL.cons_cong(E.Item<T>, E.Item{j, v}, t, SC.append(E.Item<T>, pre(T, t, i), suf(T, t, i)), ih)

def cut_app(-T: Data, +xs: List<&2, E.Item<T>>, +i: Nat) -> {xs == SC.append(E.Item<T>, pre(T, xs, i), suf(T, xs, i)) : List<&2, E.Item<T>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{E.Item{+j, +v}, +t}:
      cut_c(T, j, v, t, i, Nat.is_eq(j, i), {==}, cut_app(T, t, i))

def pre_c(-T: Data, +j: Nat, +v: T, +t: List<&2, E.Item<T>>, +i: Nat, b: Bool, +eb: {Nat.is_eq(j, i) == b : Bool}, +ih: {NS.mem(i, NS.ids(T, pre(T, t, i))) == False{} : Bool}) -> {NS.mem(i, NS.ids(T, pre(T, Con{E.Item{j, v}, t}, i))) == False{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(j, i), True{}, eb) : {NS.mem(i, NS.ids(T, DS.pick(T, _, Nil{}, Con{E.Item{j, v}, pre(T, t, i)}))) == False{} : Bool}
      {==}
    case False{}:
      +ne = LK.ne_flip(j, i, eb)
      %Equal.sym(Bool, Nat.is_eq(j, i), False{}, eb) : {NS.mem(i, NS.ids(T, DS.pick(T, _, Nil{}, Con{E.Item{j, v}, pre(T, t, i)}))) == False{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(i, j), False{}, ne) : {Bool.or(_, NS.mem(i, NS.ids(T, pre(T, t, i)))) == False{} : Bool}
      ih

# i does not occur before the cut.
def pre_nm(-T: Data, +xs: List<&2, E.Item<T>>, +i: Nat) -> {NS.mem(i, NS.ids(T, pre(T, xs, i))) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{E.Item{+j, +v}, +t}:
      pre_c(T, j, v, t, i, Nat.is_eq(j, i), {==}, pre_nm(T, t, i))

def suf_c(-T: Data, +j: Nat, +v: T, +t: List<&2, E.Item<T>>, +i: Nat, b: Bool, +eb: {Nat.is_eq(j, i) == b : Bool}, +ih: {sufok(T, suf(T, t, i), i) == True{} : Bool}) -> {sufok(T, suf(T, Con{E.Item{j, v}, t}, i), i) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(j, i), True{}, eb) : {sufok(T, DS.pick(T, _, Con{E.Item{j, v}, t}, suf(T, t, i)), i) == True{} : Bool}
      eb
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(j, i), False{}, eb) : {sufok(T, DS.pick(T, _, Con{E.Item{j, v}, t}, suf(T, t, i)), i) == True{} : Bool}
      ih

# The cut starts at an item with id i (when it is not empty).
def suf_ok(-T: Data, +xs: List<&2, E.Item<T>>, +i: Nat) -> {sufok(T, suf(T, xs, i), i) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{E.Item{+j, +v}, +t}:
      suf_c(T, j, v, t, i, Nat.is_eq(j, i), {==}, suf_ok(T, t, i))

# ---- the specification's operations through the cut ----

def getv_c(-T: Data, +j: Nat, +v: T, +t: List<&2, E.Item<T>>, +i: Nat, b: Bool, +eb: {Nat.is_eq(j, i) == b : Bool}, +ih: {DS.getv(T, t, i) == gets(T, suf(T, t, i)) : Maybe<&2, T>}) -> {DS.getv(T, Con{E.Item{j, v}, t}, i) == gets(T, suf(T, Con{E.Item{j, v}, t}, i)) : Maybe<&2, T>}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(j, i), True{}, eb) : {DS.getv_at(T, _, v, DS.getv(T, t, i)) == gets(T, DS.pick(T, _, Con{E.Item{j, v}, t}, suf(T, t, i))) : Maybe<&2, T>}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(j, i), False{}, eb) : {DS.getv_at(T, _, v, DS.getv(T, t, i)) == gets(T, DS.pick(T, _, Con{E.Item{j, v}, t}, suf(T, t, i))) : Maybe<&2, T>}
      ih

def getv_cut(-T: Data, +xs: List<&2, E.Item<T>>, +i: Nat) -> {DS.getv(T, xs, i) == gets(T, suf(T, xs, i)) : Maybe<&2, T>}:
  match xs:
    case Nil{}:
      {==}
    case Con{E.Item{+j, +v}, +t}:
      getv_c(T, j, v, t, i, Nat.is_eq(j, i), {==}, getv_cut(T, t, i))

def ib_c(-T: Data, +j: Nat, +v: T, +t: List<&2, E.Item<T>>, +i: Nat, +it: E.Item<T>, b: Bool, +eb: {Nat.is_eq(j, i) == b : Bool}, +ih: {DS.ins_before(T, t, i, it) == SC.append(E.Item<T>, pre(T, t, i), ibs(T, suf(T, t, i), it)) : List<&2, E.Item<T>>}) -> {DS.ins_before(T, Con{E.Item{j, v}, t}, i, it) == SC.append(E.Item<T>, pre(T, Con{E.Item{j, v}, t}, i), ibs(T, suf(T, Con{E.Item{j, v}, t}, i), it)) : List<&2, E.Item<T>>}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(j, i), True{}, eb) : {DS.pick(T, _, Con{it, Con{E.Item{j, v}, t}}, Con{E.Item{j, v}, DS.ins_before(T, t, i, it)}) == SC.append(E.Item<T>, DS.pick(T, _, Nil{}, Con{E.Item{j, v}, pre(T, t, i)}), ibs(T, DS.pick(T, _, Con{E.Item{j, v}, t}, suf(T, t, i)), it)) : List<&2, E.Item<T>>}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(j, i), False{}, eb) : {DS.pick(T, _, Con{it, Con{E.Item{j, v}, t}}, Con{E.Item{j, v}, DS.ins_before(T, t, i, it)}) == SC.append(E.Item<T>, DS.pick(T, _, Nil{}, Con{E.Item{j, v}, pre(T, t, i)}), ibs(T, DS.pick(T, _, Con{E.Item{j, v}, t}, suf(T, t, i)), it)) : List<&2, E.Item<T>>}
      LL.cons_cong(E.Item<T>, E.Item{j, v}, DS.ins_before(T, t, i, it), SC.append(E.Item<T>, pre(T, t, i), ibs(T, suf(T, t, i), it)), ih)

def ib_cut(-T: Data, +xs: List<&2, E.Item<T>>, +i: Nat, +it: E.Item<T>) -> {DS.ins_before(T, xs, i, it) == SC.append(E.Item<T>, pre(T, xs, i), ibs(T, suf(T, xs, i), it)) : List<&2, E.Item<T>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{E.Item{+j, +v}, +t}:
      ib_c(T, j, v, t, i, it, Nat.is_eq(j, i), {==}, ib_cut(T, t, i, it))

def ia_c(-T: Data, +j: Nat, +v: T, +t: List<&2, E.Item<T>>, +i: Nat, +it: E.Item<T>, b: Bool, +eb: {Nat.is_eq(j, i) == b : Bool}, +ih: {DS.ins_after(T, t, i, it) == SC.append(E.Item<T>, pre(T, t, i), ias(T, suf(T, t, i), it)) : List<&2, E.Item<T>>}) -> {DS.ins_after(T, Con{E.Item{j, v}, t}, i, it) == SC.append(E.Item<T>, pre(T, Con{E.Item{j, v}, t}, i), ias(T, suf(T, Con{E.Item{j, v}, t}, i), it)) : List<&2, E.Item<T>>}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(j, i), True{}, eb) : {DS.pick(T, _, Con{E.Item{j, v}, Con{it, t}}, Con{E.Item{j, v}, DS.ins_after(T, t, i, it)}) == SC.append(E.Item<T>, DS.pick(T, _, Nil{}, Con{E.Item{j, v}, pre(T, t, i)}), ias(T, DS.pick(T, _, Con{E.Item{j, v}, t}, suf(T, t, i)), it)) : List<&2, E.Item<T>>}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(j, i), False{}, eb) : {DS.pick(T, _, Con{E.Item{j, v}, Con{it, t}}, Con{E.Item{j, v}, DS.ins_after(T, t, i, it)}) == SC.append(E.Item<T>, DS.pick(T, _, Nil{}, Con{E.Item{j, v}, pre(T, t, i)}), ias(T, DS.pick(T, _, Con{E.Item{j, v}, t}, suf(T, t, i)), it)) : List<&2, E.Item<T>>}
      LL.cons_cong(E.Item<T>, E.Item{j, v}, DS.ins_after(T, t, i, it), SC.append(E.Item<T>, pre(T, t, i), ias(T, suf(T, t, i), it)), ih)

def ia_cut(-T: Data, +xs: List<&2, E.Item<T>>, +i: Nat, +it: E.Item<T>) -> {DS.ins_after(T, xs, i, it) == SC.append(E.Item<T>, pre(T, xs, i), ias(T, suf(T, xs, i), it)) : List<&2, E.Item<T>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{E.Item{+j, +v}, +t}:
      ia_c(T, j, v, t, i, it, Nat.is_eq(j, i), {==}, ia_cut(T, t, i, it))

def del_c(-T: Data, +j: Nat, +v: T, +t: List<&2, E.Item<T>>, +i: Nat, b: Bool, +eb: {Nat.is_eq(j, i) == b : Bool}, +ih: {DS.del(T, t, i) == SC.append(E.Item<T>, pre(T, t, i), tl(T, suf(T, t, i))) : List<&2, E.Item<T>>}) -> {DS.del(T, Con{E.Item{j, v}, t}, i) == SC.append(E.Item<T>, pre(T, Con{E.Item{j, v}, t}, i), tl(T, suf(T, Con{E.Item{j, v}, t}, i))) : List<&2, E.Item<T>>}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(j, i), True{}, eb) : {DS.pick(T, _, t, Con{E.Item{j, v}, DS.del(T, t, i)}) == SC.append(E.Item<T>, DS.pick(T, _, Nil{}, Con{E.Item{j, v}, pre(T, t, i)}), tl(T, DS.pick(T, _, Con{E.Item{j, v}, t}, suf(T, t, i)))) : List<&2, E.Item<T>>}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(j, i), False{}, eb) : {DS.pick(T, _, t, Con{E.Item{j, v}, DS.del(T, t, i)}) == SC.append(E.Item<T>, DS.pick(T, _, Nil{}, Con{E.Item{j, v}, pre(T, t, i)}), tl(T, DS.pick(T, _, Con{E.Item{j, v}, t}, suf(T, t, i)))) : List<&2, E.Item<T>>}
      LL.cons_cong(E.Item<T>, E.Item{j, v}, DS.del(T, t, i), SC.append(E.Item<T>, pre(T, t, i), tl(T, suf(T, t, i))), ih)

def del_cut(-T: Data, +xs: List<&2, E.Item<T>>, +i: Nat) -> {DS.del(T, xs, i) == SC.append(E.Item<T>, pre(T, xs, i), tl(T, suf(T, xs, i))) : List<&2, E.Item<T>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{E.Item{+j, +v}, +t}:
      del_c(T, j, v, t, i, Nat.is_eq(j, i), {==}, del_cut(T, t, i))

def sv_c(-T: Data, +j: Nat, +v: T, +t: List<&2, E.Item<T>>, +i: Nat, +x: T, b: Bool, +eb: {Nat.is_eq(j, i) == b : Bool}, +ih: {DS.setv(T, t, i, x) == SC.append(E.Item<T>, pre(T, t, i), svs(T, suf(T, t, i), x)) : List<&2, E.Item<T>>}) -> {DS.setv(T, Con{E.Item{j, v}, t}, i, x) == SC.append(E.Item<T>, pre(T, Con{E.Item{j, v}, t}, i), svs(T, suf(T, Con{E.Item{j, v}, t}, i), x)) : List<&2, E.Item<T>>}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(j, i), True{}, eb) : {DS.pick(T, _, Con{E.Item{j, x}, t}, Con{E.Item{j, v}, DS.setv(T, t, i, x)}) == SC.append(E.Item<T>, DS.pick(T, _, Nil{}, Con{E.Item{j, v}, pre(T, t, i)}), svs(T, DS.pick(T, _, Con{E.Item{j, v}, t}, suf(T, t, i)), x)) : List<&2, E.Item<T>>}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(j, i), False{}, eb) : {DS.pick(T, _, Con{E.Item{j, x}, t}, Con{E.Item{j, v}, DS.setv(T, t, i, x)}) == SC.append(E.Item<T>, DS.pick(T, _, Nil{}, Con{E.Item{j, v}, pre(T, t, i)}), svs(T, DS.pick(T, _, Con{E.Item{j, v}, t}, suf(T, t, i)), x)) : List<&2, E.Item<T>>}
      LL.cons_cong(E.Item<T>, E.Item{j, v}, DS.setv(T, t, i, x), SC.append(E.Item<T>, pre(T, t, i), svs(T, suf(T, t, i), x)), ih)

def setv_cut(-T: Data, +xs: List<&2, E.Item<T>>, +i: Nat, +x: T) -> {DS.setv(T, xs, i, x) == SC.append(E.Item<T>, pre(T, xs, i), svs(T, suf(T, xs, i), x)) : List<&2, E.Item<T>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{E.Item{+j, +v}, +t}:
      sv_c(T, j, v, t, i, x, Nat.is_eq(j, i), {==}, setv_cut(T, t, i, x))

def first_fst(-T: Data, +xs: List<&2, E.Item<T>>) -> {DS.first_id(T, xs) == LK.fst(NS.ids(T, xs), None{}) : Maybe<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{E.Item{j, v}, t}:
      {==}

def nx_c(-T: Data, +j: Nat, +v: T, +t: List<&2, E.Item<T>>, +i: Nat, b: Bool, +eb: {Nat.is_eq(j, i) == b : Bool}, +ih: {DS.next_of(T, t, i) == nxs(T, suf(T, t, i)) : Maybe<&2, Nat>}) -> {DS.next_of(T, Con{E.Item{j, v}, t}, i) == nxs(T, suf(T, Con{E.Item{j, v}, t}, i)) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(j, i), True{}, eb) : {DS.pickm(_, DS.first_id(T, t), DS.next_of(T, t, i)) == nxs(T, DS.pick(T, _, Con{E.Item{j, v}, t}, suf(T, t, i))) : Maybe<&2, Nat>}
      first_fst(T, t)
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(j, i), False{}, eb) : {DS.pickm(_, DS.first_id(T, t), DS.next_of(T, t, i)) == nxs(T, DS.pick(T, _, Con{E.Item{j, v}, t}, suf(T, t, i))) : Maybe<&2, Nat>}
      ih

def next_cut(-T: Data, +xs: List<&2, E.Item<T>>, +i: Nat) -> {DS.next_of(T, xs, i) == nxs(T, suf(T, xs, i)) : Maybe<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{E.Item{+j, +v}, +t}:
      nx_c(T, j, v, t, i, Nat.is_eq(j, i), {==}, next_cut(T, t, i))

def pv_c(-T: Data, +j: Nat, +v: T, +t: List<&2, E.Item<T>>, +i: Nat, +p: Maybe<&2, Nat>, b: Bool, +eb: {Nat.is_eq(j, i) == b : Bool}, +ih: {DS.prev_of(T, t, i, Some{j}) == pvs(T, suf(T, t, i), LK.lst(NS.ids(T, pre(T, t, i)), Some{j})) : Maybe<&2, Nat>}) -> {DS.prev_of(T, Con{E.Item{j, v}, t}, i, p) == pvs(T, suf(T, Con{E.Item{j, v}, t}, i), LK.lst(NS.ids(T, pre(T, Con{E.Item{j, v}, t}, i)), p)) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(j, i), True{}, eb) : {DS.pickm(_, p, DS.prev_of(T, t, i, Some{j})) == pvs(T, DS.pick(T, _, Con{E.Item{j, v}, t}, suf(T, t, i)), LK.lst(NS.ids(T, DS.pick(T, _, Nil{}, Con{E.Item{j, v}, pre(T, t, i)})), p)) : Maybe<&2, Nat>}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(j, i), False{}, eb) : {DS.pickm(_, p, DS.prev_of(T, t, i, Some{j})) == pvs(T, DS.pick(T, _, Con{E.Item{j, v}, t}, suf(T, t, i)), LK.lst(NS.ids(T, DS.pick(T, _, Nil{}, Con{E.Item{j, v}, pre(T, t, i)})), p)) : Maybe<&2, Nat>}
      ih

def prev_cut(-T: Data, +xs: List<&2, E.Item<T>>, +i: Nat, +p: Maybe<&2, Nat>) -> {DS.prev_of(T, xs, i, p) == pvs(T, suf(T, xs, i), LK.lst(NS.ids(T, pre(T, xs, i)), p)) : Maybe<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{E.Item{+j, +v}, +t}:
      pv_c(T, j, v, t, i, p, Nat.is_eq(j, i), {==}, prev_cut(T, t, i, Some{j}))
