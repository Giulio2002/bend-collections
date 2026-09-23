import Base
import ../lib/logic.bend as L
import ../lib/array.bend as AR
import ../lib/list.bend as LL
import ../spec/common.bend as SC
import ../spec/doubly_linked_list.bend as S
import ../math/u32div.bend as UD
import ../../src/containers/doubly_linked_list.bend as D
import ../../src/containers/types/doubly_linked_list.bend as E
import ./state.bend as ST
import ./ok.bend as OK
import ./valid.bend as VD
import ./step.bend as SP

# THEOREM (traces): every trace run from a good shadow, whose specification
# states all have fewer than 2^cz issued ids, gives the specification's
# observations, and the new list is such a shadow.


# fewer than 2^cz ids issued
def room(-T: Data, m: S.DS<T>, +cz: Nat) -> Bool:
  match m:
    case S.DS{+tag, +order, +vals, +gens, +free}:
      Nat.is_lt(SC.length(Maybe<&2, T>, vals), SC.pow2(cz))

# room before every operation of ops
def fits(-T: Data, ops: List<&2, E.Op<T>>, +m: S.DS<T>, +cz: Nat) -> Bool:
  match ops:
    case Nil{}:
      True{}
    case Con{+op, rest}:
      Bool.and(room(T, m, cz), fits(T, rest, Pair.fst(S.DS<T>, E.Obs<T>, S.step(T, m, op)), cz))


def step_sh(~T: Data, +one: Nat, +h1: {one == 1n : Nat}, +cz: Nat, +hcz: {cz == 29n : Nat}, +sh: ST.Sh<T>, +hg: {ST.good(~T, sh) == True{} : Bool}, +hr: {room(T, ST.model(~T, sh), cz) == True{} : Bool}, +op: E.Op<T>) -> OK.POK(~T, E.Obs<T>, S.step(T, ST.model(~T, sh), op), D.step(~T, ST.real(~T, sh), op)):
  match sh:
    case ST.LS{+tag, +cap, +fresh, +free, +head, +tail, +depth, +vT, +pT, +nT, +gT, +sl, +fl}:
      +el = VD.len_vlf(~T, tag, cap, fresh, free, head, tail, depth, vT, pT, nT, gT, sl, fl, hg, 0, 0, 0)
      +hroom = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(cz)) == True{} : Bool}, SC.length(Maybe<&2, T>, SC.take(Maybe<&2, T>, AR.slots(Maybe<&2, T>, vT), UD.v(fresh))), UD.v(fresh), el, hr)
      SP.step_ok(~T, one, h1, cz, hcz, tag, cap, fresh, free, head, tail, depth, vT, pT, nT, gT, sl, fl, hg, hroom, op)

def RunOK(~T: Data, +ops: List<&2, E.Op<T>>, +sh: ST.Sh<T>, +acc: List<&2, E.Obs<T>>) -> Type:
  Sigma<&1, &1, ST.Sh<T>, sh2 => Sigma<&1, &1, List<&2, E.Obs<T>>, os => {D.run_acc(~T, ops, (ST.real(~T, sh), acc)) == (ST.real(~T, sh2), SC.append(E.Obs<T>, SC.reverse(E.Obs<T>, os), acc)) : D.DList<T> & List<&2, E.Obs<T>>} & ({S.run(T, ops, ST.model(~T, sh)) == (ST.model(~T, sh2), os) : S.DS<T> & List<&2, E.Obs<T>>} & {ST.good(~T, sh2) == True{} : Bool})>>


# after the rest
def run_c2(~T: Data, +op: E.Op<T>, +rest: List<&2, E.Op<T>>, +sh: ST.Sh<T>, +acc: List<&2, E.Obs<T>>, +sh1: ST.Sh<T>, +o: E.Obs<T>, +er: {D.step(~T, ST.real(~T, sh), op) == (ST.real(~T, sh1), o) : D.DList<T> & E.Obs<T>}, +es: {S.step(T, ST.model(~T, sh), op) == (ST.model(~T, sh1), o) : S.DS<T> & E.Obs<T>}, q: RunOK(~T, rest, sh1, Con{o, acc})) -> RunOK(~T, Con{op, rest}, sh, acc):
  match q:
    case Tuple{+sh2, Tuple{+os, Tuple{+er2, Tuple{+es2, hg2}}}}:
      +e1 = Equal.cong(D.DList<T> & E.Obs<T>, D.DList<T> & List<&2, E.Obs<T>>, r => D.run_acc(~T, rest, D.record(~T, acc, r)), D.step(~T, ST.real(~T, sh), op), (ST.real(~T, sh1), o), er)
      +e3 = Equal.cong(List<&2, E.Obs<T>>, D.DList<T> & List<&2, E.Obs<T>>, z => (ST.real(~T, sh2), z), SC.append(E.Obs<T>, SC.reverse(E.Obs<T>, os), Con{o, acc}), SC.append(E.Obs<T>, SC.reverse(E.Obs<T>, Con{o, os}), acc), Equal.sym(List<&2, E.Obs<T>>, SC.append(E.Obs<T>, SC.snoc(E.Obs<T>, SC.reverse(E.Obs<T>, os), o), acc), SC.append(E.Obs<T>, SC.reverse(E.Obs<T>, os), Con{o, acc}), LL.snoc_append_cons(E.Obs<T>, SC.reverse(E.Obs<T>, os), o, acc)))
      +erc = Equal.trans(D.DList<T> & List<&2, E.Obs<T>>, D.run_acc(~T, Con{op, rest}, (ST.real(~T, sh), acc)), D.run_acc(~T, rest, (ST.real(~T, sh1), Con{o, acc})), (ST.real(~T, sh2), SC.append(E.Obs<T>, SC.reverse(E.Obs<T>, Con{o, os}), acc)), e1, Equal.trans(D.DList<T> & List<&2, E.Obs<T>>, D.run_acc(~T, rest, (ST.real(~T, sh1), Con{o, acc})), (ST.real(~T, sh2), SC.append(E.Obs<T>, SC.reverse(E.Obs<T>, os), Con{o, acc})), (ST.real(~T, sh2), SC.append(E.Obs<T>, SC.reverse(E.Obs<T>, Con{o, os}), acc)), er2, e3))
      +s1 = Equal.cong(S.DS<T> & E.Obs<T>, S.DS<T> & List<&2, E.Obs<T>>, r => S.cons_obs(T, Pair.snd(S.DS<T>, E.Obs<T>, r), S.run(T, rest, Pair.fst(S.DS<T>, E.Obs<T>, r))), S.step(T, ST.model(~T, sh), op), (ST.model(~T, sh1), o), es)
      +s2 = Equal.cong(S.DS<T> & List<&2, E.Obs<T>>, S.DS<T> & List<&2, E.Obs<T>>, r => S.cons_obs(T, o, r), S.run(T, rest, ST.model(~T, sh1)), (ST.model(~T, sh2), os), es2)
      (sh2, (Con{o, os}, (erc, (Equal.trans(S.DS<T> & List<&2, E.Obs<T>>, S.run(T, Con{op, rest}, ST.model(~T, sh)), S.cons_obs(T, o, S.run(T, rest, ST.model(~T, sh1))), (ST.model(~T, sh2), Con{o, os}), s1, s2), hg2))))

# after the first operation
def run_c1(~T: Data, +op: E.Op<T>, +rest: List<&2, E.Op<T>>, +sh: ST.Sh<T>, +acc: List<&2, E.Obs<T>>, +cz: Nat, +hf: {fits(T, rest, Pair.fst(S.DS<T>, E.Obs<T>, S.step(T, ST.model(~T, sh), op)), cz) == True{} : Bool}, p: OK.POK(~T, E.Obs<T>, S.step(T, ST.model(~T, sh), op), D.step(~T, ST.real(~T, sh), op)), rec: @+sh1: ST.Sh<T> -> @+acc1: List<&2, E.Obs<T>> -> @+hg1: {ST.good(~T, sh1) == True{} : Bool} -> @+hf1: {fits(T, rest, ST.model(~T, sh1), cz) == True{} : Bool} -> RunOK(~T, rest, sh1, acc1)) -> RunOK(~T, Con{op, rest}, sh, acc):
  match p:
    case Tuple{+sh1, Tuple{+o, Tuple{+er, Tuple{+es, hg1}}}}:
      +hg1b = {hg1 : {ST.good(~T, sh1) == True{} : Bool}}
      +hf1 = L.subst(S.DS<T>, z => {fits(T, rest, z, cz) == True{} : Bool}, Pair.fst(S.DS<T>, E.Obs<T>, S.step(T, ST.model(~T, sh), op)), ST.model(~T, sh1), Equal.cong(S.DS<T> & E.Obs<T>, S.DS<T>, r => Pair.fst(S.DS<T>, E.Obs<T>, r), S.step(T, ST.model(~T, sh), op), (ST.model(~T, sh1), o), es), hf)
      run_c2(~T, op, rest, sh, acc, sh1, o, er, es, rec(sh1, Con{o, acc}, hg1b, hf1))

def run_ok(~T: Data, +one: Nat, +h1: {one == 1n : Nat}, +cz: Nat, +hcz: {cz == 29n : Nat}, +ops: List<&2, E.Op<T>>, +sh: ST.Sh<T>, +acc: List<&2, E.Obs<T>>, +hg: {ST.good(~T, sh) == True{} : Bool}, +hf: {fits(T, ops, ST.model(~T, sh), cz) == True{} : Bool}) -> RunOK(~T, ops, sh, acc):
  match ops:
    case Nil{}:
      (sh, (Nil{}, ({==}, ({==}, hg))))
    case Con{+op, +rest}:
      +hr = L.and_left(room(T, ST.model(~T, sh), cz), fits(T, rest, Pair.fst(S.DS<T>, E.Obs<T>, S.step(T, ST.model(~T, sh), op)), cz), hf)
      +hf2 = L.and_right(room(T, ST.model(~T, sh), cz), fits(T, rest, Pair.fst(S.DS<T>, E.Obs<T>, S.step(T, ST.model(~T, sh), op)), cz), hf)
      run_c1(~T, op, rest, sh, acc, cz, hf2, step_sh(~T, one, h1, cz, hcz, sh, hg, hr, op), sh1 => acc1 => hg1 => hf1 => run_ok(~T, one, h1, cz, hcz, rest, sh1, acc1, hg1, hf1))

def TraceOK(~T: Data, +ops: List<&2, E.Op<T>>, +sh: ST.Sh<T>) -> Type:
  Sigma<&1, &1, ST.Sh<T>, sh2 => Sigma<&1, &1, List<&2, E.Obs<T>>, os => {D.run(~T, ops, ST.real(~T, sh)) == (ST.real(~T, sh2), os) : D.DList<T> & List<&2, E.Obs<T>>} & ({S.run(T, ops, ST.model(~T, sh)) == (ST.model(~T, sh2), os) : S.DS<T> & List<&2, E.Obs<T>>} & {ST.good(~T, sh2) == True{} : Bool})>>

def fin_c(~T: Data, +ops: List<&2, E.Op<T>>, +sh: ST.Sh<T>, q: RunOK(~T, ops, sh, Nil{})) -> TraceOK(~T, ops, sh):
  match q:
    case Tuple{+sh2, Tuple{+os, Tuple{+er, Tuple{+es, hg2}}}}:
      +e1 = Equal.cong(D.DList<T> & List<&2, E.Obs<T>>, D.DList<T> & List<&2, E.Obs<T>>, r => D.finish(~T, r), D.run_acc(~T, ops, (ST.real(~T, sh), Nil{})), (ST.real(~T, sh2), SC.append(E.Obs<T>, SC.reverse(E.Obs<T>, os), Nil{})), er)
      +ev = Equal.trans(List<&2, E.Obs<T>>, List.reverse(&2, E.Obs<T>, SC.append(E.Obs<T>, SC.reverse(E.Obs<T>, os), Nil{})), SC.reverse(E.Obs<T>, SC.append(E.Obs<T>, SC.reverse(E.Obs<T>, os), Nil{})), os, LL.base_rev(E.Obs<T>, SC.append(E.Obs<T>, SC.reverse(E.Obs<T>, os), Nil{})), Equal.trans(List<&2, E.Obs<T>>, SC.reverse(E.Obs<T>, SC.append(E.Obs<T>, SC.reverse(E.Obs<T>, os), Nil{})), SC.reverse(E.Obs<T>, SC.reverse(E.Obs<T>, os)), os, Equal.cong(List<&2, E.Obs<T>>, List<&2, E.Obs<T>>, z => SC.reverse(E.Obs<T>, z), SC.append(E.Obs<T>, SC.reverse(E.Obs<T>, os), Nil{}), SC.reverse(E.Obs<T>, os), LL.append_nil(E.Obs<T>, SC.reverse(E.Obs<T>, os))), LL.spec_rev_rev(E.Obs<T>, os)))
      +e2 = Equal.cong(List<&2, E.Obs<T>>, D.DList<T> & List<&2, E.Obs<T>>, z => (ST.real(~T, sh2), z), List.reverse(&2, E.Obs<T>, SC.append(E.Obs<T>, SC.reverse(E.Obs<T>, os), Nil{})), os, ev)
      (sh2, (os, (Equal.trans(D.DList<T> & List<&2, E.Obs<T>>, D.run(~T, ops, ST.real(~T, sh)), D.finish(~T, (ST.real(~T, sh2), SC.append(E.Obs<T>, SC.reverse(E.Obs<T>, os), Nil{}))), (ST.real(~T, sh2), os), e1, e2), (es, hg2))))

# THEOREM (traces from a good shadow)
def trace_ok(~T: Data, +one: Nat, +h1: {one == 1n : Nat}, +cz: Nat, +hcz: {cz == 29n : Nat}, +ops: List<&2, E.Op<T>>, +sh: ST.Sh<T>, +hg: {ST.good(~T, sh) == True{} : Bool}, +hf: {fits(T, ops, ST.model(~T, sh), cz) == True{} : Bool}) -> TraceOK(~T, ops, sh):
  fin_c(~T, ops, sh, run_ok(~T, one, h1, cz, hcz, ops, sh, Nil{}, hg, hf))

# ---- the new list ----


def new_sh(-T: Data, +tag: U32) -> ST.Sh<T>:
  ST.LS{tag, 1, 0, 0, 0, 0, 0n, AR.TLeaf{None{}}, AR.TLeaf{0}, AR.TLeaf{0}, AR.TLeaf{0}, Nil{}, Nil{}}

# THEOREM (new): the new list is the real list of a good shadow whose model
# is the specification's empty list
def new_ok(~T: Data, +tag: U32) -> {ST.real(~T, ST.LS{tag, 1, 0, 0, 0, 0, 0n, AR.TLeaf{None{}}, AR.TLeaf{0}, AR.TLeaf{0}, AR.TLeaf{0}, Nil{}, Nil{}}) == D.new(~T, tag) : D.DList<T>} & ({ST.model(~T, ST.LS{tag, 1, 0, 0, 0, 0, 0n, AR.TLeaf{None{}}, AR.TLeaf{0}, AR.TLeaf{0}, AR.TLeaf{0}, Nil{}, Nil{}}) == S.empty(T, tag) : S.DS<T>} & {ST.good(~T, ST.LS{tag, 1, 0, 0, 0, 0, 0n, AR.TLeaf{None{}}, AR.TLeaf{0}, AR.TLeaf{0}, AR.TLeaf{0}, Nil{}, Nil{}}) == True{} : Bool}):
  ({==}, ({==}, {==}))

# THEOREM (observations): every trace on a new list whose specification
# states keep fewer than 2^cz issued ids observes what the specification does
def run_new(~T: Data, +one: Nat, +h1: {one == 1n : Nat}, +cz: Nat, +hcz: {cz == 29n : Nat}, +tag: U32, +ops: List<&2, E.Op<T>>, +hf: {fits(T, ops, S.empty(T, tag), cz) == True{} : Bool}) -> TraceOK(~T, ops, ST.LS{tag, 1, 0, 0, 0, 0, 0n, AR.TLeaf{None{}}, AR.TLeaf{0}, AR.TLeaf{0}, AR.TLeaf{0}, Nil{}, Nil{}}):
  trace_ok(~T, one, h1, cz, hcz, ops, ST.LS{tag, 1, 0, 0, 0, 0, 0n, AR.TLeaf{None{}}, AR.TLeaf{0}, AR.TLeaf{0}, AR.TLeaf{0}, Nil{}, Nil{}}, {==}, hf)
