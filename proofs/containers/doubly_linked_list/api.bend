import Base
import ../../lib/logic.bend as L
import ../../lib/array.bend as AR
import ../../lib/spec_common.bend as SC
import ./spec.bend as S
import ../../lib/u32div.bend as UD
import ../../../src/containers/doubly_linked_list.bend as D
import ../../../src/containers/types/doubly_linked_list.bend as E
import ./state.bend as ST
import ./ok.bend as OK
import ./valid.bend as VD
import ./step.bend as SP
import ./trace.bend as TR
import ./direct.bend as DR
import ../../../src/containers/internal/dlist_storage.bend as R

# The public list's API on a good shadow: every direct operation returns the
# projection of the specification's step, and the new state is good.


# the direct result r and the specification's step agree through P
def DOK(~T: Data, -Y: Data, -P: @r: D.DList<T> & E.Obs<T> -> D.DList<T> & Y, -x: D.DList<T> & Y, -spec: S.DS<T> & E.Obs<T>) -> Type:
  Sigma<&1, &1, ST.Sh<T>, sh2 => Sigma<&1, &1, E.Obs<T>, o => {x == P((ST.real(~T, sh2), o)) : D.DList<T> & Y} & ({spec == (ST.model(~T, sh2), o) : S.DS<T> & E.Obs<T>} & {ST.good(~T, sh2) == True{} : Bool})>>

def dok(~T: Data, -Y: Data, -P: @r: D.DList<T> & E.Obs<T> -> D.DList<T> & Y, -x: D.DList<T> & Y, -spec: S.DS<T> & E.Obs<T>, -r: D.DList<T> & E.Obs<T>, +dx: {x == P(r) : D.DList<T> & Y}, p: OK.POK(~T, E.Obs<T>, spec, r)) -> DOK(~T, Y, P, x, spec):
  match p:
    case Tuple{+sh2, Tuple{+o, Tuple{+er, Tuple{+es, hg2}}}}:
      (sh2, (o, (Equal.trans(D.DList<T> & Y, x, P(r), P((ST.real(~T, sh2), o)), dx, Equal.cong(D.DList<T> & E.Obs<T>, D.DList<T> & Y, z => P(z), r, (ST.real(~T, sh2), o), er)), (es, hg2))))


# ---- steps without allocation ----

def get_sh(~T: Data, +one: Nat, +h1: {one == 1n : Nat}, +sh: ST.Sh<T>, +hg: {ST.good(~T, sh) == True{} : Bool}, +h: E.Handle) -> OK.POK(~T, E.Obs<T>, S.step(T, ST.model(~T, sh), E.Get{h}), D.step(~T, ST.real(~T, sh), E.Get{h})):
  match sh:
    case ST.LS{+tag, +cap, +fresh, +free, +head, +tail, +depth, +vT, +pT, +nT, +gT, +sl, +fl}:
      SP.get_h(~T, one, h1, tag, cap, fresh, free, head, tail, depth, vT, pT, nT, gT, sl, fl, hg, h)

def set_sh(~T: Data, +one: Nat, +h1: {one == 1n : Nat}, +sh: ST.Sh<T>, +hg: {ST.good(~T, sh) == True{} : Bool}, +h: E.Handle, +x: T) -> OK.POK(~T, E.Obs<T>, S.step(T, ST.model(~T, sh), E.Set{h, x}), D.step(~T, ST.real(~T, sh), E.Set{h, x})):
  match sh:
    case ST.LS{+tag, +cap, +fresh, +free, +head, +tail, +depth, +vT, +pT, +nT, +gT, +sl, +fl}:
      SP.set_h(~T, one, h1, tag, cap, fresh, free, head, tail, depth, vT, pT, nT, gT, sl, fl, hg, h, x)

def next_sh(~T: Data, +one: Nat, +h1: {one == 1n : Nat}, +sh: ST.Sh<T>, +hg: {ST.good(~T, sh) == True{} : Bool}, +h: E.Handle) -> OK.POK(~T, E.Obs<T>, S.step(T, ST.model(~T, sh), E.Next{h}), D.step(~T, ST.real(~T, sh), E.Next{h})):
  match sh:
    case ST.LS{+tag, +cap, +fresh, +free, +head, +tail, +depth, +vT, +pT, +nT, +gT, +sl, +fl}:
      SP.next_h(~T, one, h1, tag, cap, fresh, free, head, tail, depth, vT, pT, nT, gT, sl, fl, hg, h)

def prev_sh(~T: Data, +one: Nat, +h1: {one == 1n : Nat}, +sh: ST.Sh<T>, +hg: {ST.good(~T, sh) == True{} : Bool}, +h: E.Handle) -> OK.POK(~T, E.Obs<T>, S.step(T, ST.model(~T, sh), E.Prev{h}), D.step(~T, ST.real(~T, sh), E.Prev{h})):
  match sh:
    case ST.LS{+tag, +cap, +fresh, +free, +head, +tail, +depth, +vT, +pT, +nT, +gT, +sl, +fl}:
      SP.prev_h(~T, one, h1, tag, cap, fresh, free, head, tail, depth, vT, pT, nT, gT, sl, fl, hg, h)

def remove_sh(~T: Data, +one: Nat, +h1: {one == 1n : Nat}, +sh: ST.Sh<T>, +hg: {ST.good(~T, sh) == True{} : Bool}, +h: E.Handle) -> OK.POK(~T, E.Obs<T>, S.step(T, ST.model(~T, sh), E.Remove{h}), D.step(~T, ST.real(~T, sh), E.Remove{h})):
  match sh:
    case ST.LS{+tag, +cap, +fresh, +free, +head, +tail, +depth, +vT, +pT, +nT, +gT, +sl, +fl}:
      SP.remove_h(~T, one, h1, tag, cap, fresh, free, head, tail, depth, vT, pT, nT, gT, sl, fl, hg, h)

# ---- the direct operations ----


def get_ok(~T: Data, +one: Nat, +h1: {one == 1n : Nat}, +sh: ST.Sh<T>, +hg: {ST.good(~T, sh) == True{} : Bool}, +h: E.Handle) -> DOK(~T, Result<&2, &2, E.Error, T>, r => D.project_value(~T, r), D.get(~T, ST.real(~T, sh), h), S.step(T, ST.model(~T, sh), E.Get{h})):
  dok(~T, Result<&2, &2, E.Error, T>, r => D.project_value(~T, r), D.get(~T, ST.real(~T, sh), h), S.step(T, ST.model(~T, sh), E.Get{h}), D.step(~T, ST.real(~T, sh), E.Get{h}), DR.get_step(~T, ST.real(~T, sh), h), get_sh(~T, one, h1, sh, hg, h))

def set_ok(~T: Data, +one: Nat, +h1: {one == 1n : Nat}, +sh: ST.Sh<T>, +hg: {ST.good(~T, sh) == True{} : Bool}, +h: E.Handle, +x: T) -> DOK(~T, Result<&2, &2, E.Error, Unit>, r => D.project_unit(~T, r), D.set(~T, ST.real(~T, sh), h, x), S.step(T, ST.model(~T, sh), E.Set{h, x})):
  dok(~T, Result<&2, &2, E.Error, Unit>, r => D.project_unit(~T, r), D.set(~T, ST.real(~T, sh), h, x), S.step(T, ST.model(~T, sh), E.Set{h, x}), D.step(~T, ST.real(~T, sh), E.Set{h, x}), DR.set_step(~T, ST.real(~T, sh), h, x), set_sh(~T, one, h1, sh, hg, h, x))

def remove_ok(~T: Data, +one: Nat, +h1: {one == 1n : Nat}, +sh: ST.Sh<T>, +hg: {ST.good(~T, sh) == True{} : Bool}, +h: E.Handle) -> DOK(~T, Result<&2, &2, E.Error, T>, r => D.project_value(~T, r), D.remove(~T, ST.real(~T, sh), h), S.step(T, ST.model(~T, sh), E.Remove{h})):
  dok(~T, Result<&2, &2, E.Error, T>, r => D.project_value(~T, r), D.remove(~T, ST.real(~T, sh), h), S.step(T, ST.model(~T, sh), E.Remove{h}), D.step(~T, ST.real(~T, sh), E.Remove{h}), DR.remove_step(~T, ST.real(~T, sh), h), remove_sh(~T, one, h1, sh, hg, h))

def next_ok(~T: Data, +one: Nat, +h1: {one == 1n : Nat}, +sh: ST.Sh<T>, +hg: {ST.good(~T, sh) == True{} : Bool}, +h: E.Handle) -> DOK(~T, Result<&2, &2, E.Error, Maybe<&2, E.Handle>>, r => D.project_neighbour(~T, r), D.next(~T, ST.real(~T, sh), h), S.step(T, ST.model(~T, sh), E.Next{h})):
  dok(~T, Result<&2, &2, E.Error, Maybe<&2, E.Handle>>, r => D.project_neighbour(~T, r), D.next(~T, ST.real(~T, sh), h), S.step(T, ST.model(~T, sh), E.Next{h}), D.step(~T, ST.real(~T, sh), E.Next{h}), DR.next_step(~T, ST.real(~T, sh), h), next_sh(~T, one, h1, sh, hg, h))

def prev_ok(~T: Data, +one: Nat, +h1: {one == 1n : Nat}, +sh: ST.Sh<T>, +hg: {ST.good(~T, sh) == True{} : Bool}, +h: E.Handle) -> DOK(~T, Result<&2, &2, E.Error, Maybe<&2, E.Handle>>, r => D.project_neighbour(~T, r), D.prev(~T, ST.real(~T, sh), h), S.step(T, ST.model(~T, sh), E.Prev{h})):
  dok(~T, Result<&2, &2, E.Error, Maybe<&2, E.Handle>>, r => D.project_neighbour(~T, r), D.prev(~T, ST.real(~T, sh), h), S.step(T, ST.model(~T, sh), E.Prev{h}), D.step(~T, ST.real(~T, sh), E.Prev{h}), DR.prev_step(~T, ST.real(~T, sh), h), prev_sh(~T, one, h1, sh, hg, h))

def before_ok(~T: Data, +one: Nat, +h1: {one == 1n : Nat}, +cz: Nat, +hcz: {cz == 29n : Nat}, +sh: ST.Sh<T>, +hg: {ST.good(~T, sh) == True{} : Bool}, +hr: {TR.room(T, ST.model(~T, sh), cz) == True{} : Bool}, +h: E.Handle, +x: T) -> DOK(~T, Result<&2, &2, E.Error, E.Handle>, r => D.project_insert(~T, r), D.insert_before(~T, ST.real(~T, sh), h, x), S.step(T, ST.model(~T, sh), E.InsertBefore{h, x})):
  dok(~T, Result<&2, &2, E.Error, E.Handle>, r => D.project_insert(~T, r), D.insert_before(~T, ST.real(~T, sh), h, x), S.step(T, ST.model(~T, sh), E.InsertBefore{h, x}), D.step(~T, ST.real(~T, sh), E.InsertBefore{h, x}), DR.before_step(~T, ST.real(~T, sh), h, x), TR.step_sh(~T, one, h1, cz, hcz, sh, hg, hr, E.InsertBefore{h, x}))

def after_ok(~T: Data, +one: Nat, +h1: {one == 1n : Nat}, +cz: Nat, +hcz: {cz == 29n : Nat}, +sh: ST.Sh<T>, +hg: {ST.good(~T, sh) == True{} : Bool}, +hr: {TR.room(T, ST.model(~T, sh), cz) == True{} : Bool}, +h: E.Handle, +x: T) -> DOK(~T, Result<&2, &2, E.Error, E.Handle>, r => D.project_insert(~T, r), D.insert_after(~T, ST.real(~T, sh), h, x), S.step(T, ST.model(~T, sh), E.InsertAfter{h, x})):
  dok(~T, Result<&2, &2, E.Error, E.Handle>, r => D.project_insert(~T, r), D.insert_after(~T, ST.real(~T, sh), h, x), S.step(T, ST.model(~T, sh), E.InsertAfter{h, x}), D.step(~T, ST.real(~T, sh), E.InsertAfter{h, x}), DR.after_step(~T, ST.real(~T, sh), h, x), TR.step_sh(~T, one, h1, cz, hcz, sh, hg, hr, E.InsertAfter{h, x}))

def front_ok(~T: Data, +one: Nat, +h1: {one == 1n : Nat}, +cz: Nat, +hcz: {cz == 29n : Nat}, +sh: ST.Sh<T>, +hg: {ST.good(~T, sh) == True{} : Bool}, +hr: {TR.room(T, ST.model(~T, sh), cz) == True{} : Bool}, +x: T) -> OK.POK(~T, E.Handle, S.push_front(T, ST.model(~T, sh), x), D.push_front(~T, ST.real(~T, sh), x)):
  match sh:
    case ST.LS{+tag, +cap, +fresh, +free, +head, +tail, +depth, +vT, +pT, +nT, +gT, +sl, +fl}:
      +el = VD.len_vlf(~T, tag, cap, fresh, free, head, tail, depth, vT, pT, nT, gT, sl, fl, hg, 0, 0, 0)
      +hroom = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(cz)) == True{} : Bool}, SC.length(Maybe<&2, T>, SC.take(Maybe<&2, T>, AR.slots(Maybe<&2, T>, vT), UD.v(fresh))), UD.v(fresh), el, hr)
      SP.front_h(~T, one, h1, cz, hcz, tag, cap, fresh, free, head, tail, depth, vT, pT, nT, gT, sl, fl, hg, hroom, x)

def back_ok(~T: Data, +one: Nat, +h1: {one == 1n : Nat}, +cz: Nat, +hcz: {cz == 29n : Nat}, +sh: ST.Sh<T>, +hg: {ST.good(~T, sh) == True{} : Bool}, +hr: {TR.room(T, ST.model(~T, sh), cz) == True{} : Bool}, +x: T) -> OK.POK(~T, E.Handle, S.push_back(T, ST.model(~T, sh), x), D.push_back(~T, ST.real(~T, sh), x)):
  match sh:
    case ST.LS{+tag, +cap, +fresh, +free, +head, +tail, +depth, +vT, +pT, +nT, +gT, +sl, +fl}:
      +el = VD.len_vlf(~T, tag, cap, fresh, free, head, tail, depth, vT, pT, nT, gT, sl, fl, hg, 0, 0, 0)
      +hroom = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(cz)) == True{} : Bool}, SC.length(Maybe<&2, T>, SC.take(Maybe<&2, T>, AR.slots(Maybe<&2, T>, vT), UD.v(fresh))), UD.v(fresh), el, hr)
      SP.back_h(~T, one, h1, cz, hcz, tag, cap, fresh, free, head, tail, depth, vT, pT, nT, gT, sl, fl, hg, hroom, x)

def length_ok(~T: Data, +sh: ST.Sh<T>) -> {D.length(~T, ST.real(~T, sh)) == (ST.real(~T, sh), S.len_of(T, ST.model(~T, sh))) : D.DList<T> & Nat}:
  match sh:
    case ST.LS{+tag, +cap, +fresh, +free, +head, +tail, +depth, +vT, +pT, +nT, +gT, +sl, +fl}:
      {==}

def to_list_ok(~T: Data, +one: Nat, +h1: {one == 1n : Nat}, +sh: ST.Sh<T>, +hg: {ST.good(~T, sh) == True{} : Bool}) -> {D.to_list(~T, ST.real(~T, sh)) == (ST.real(~T, sh), S.list_of(T, ST.model(~T, sh))) : D.DList<T> & List<&2, T>}:
  match sh:
    case ST.LS{+tag, +cap, +fresh, +free, +head, +tail, +depth, +vT, +pT, +nT, +gT, +sl, +fl}:
      +e1 = Equal.cong(R.DList<T> & List<&2, T>, D.DList<T> & List<&2, T>, r => D.to_list_direct_result(~T, tag, depth, cap, AR.thaw(U32, gT), r), R.to_list(~T, R.DL{tag, fresh, free, SC.length(Nat, sl), head, tail, depth, cap, AR.thaw(Maybe<&2, T>, vT), AR.thaw(U32, pT), AR.thaw(U32, nT)}), (R.DL{tag, fresh, free, SC.length(Nat, sl), head, tail, depth, cap, AR.thaw(Maybe<&2, T>, vT), AR.thaw(U32, pT), AR.thaw(U32, nT)}, S.values(T, AR.slots(Maybe<&2, T>, vT), sl)), SP.raw_list(~T, one, h1, tag, cap, fresh, free, head, tail, depth, vT, pT, nT, gT, sl, fl, hg))
      +e2 = Equal.cong(List<&2, T>, D.DList<T> & List<&2, T>, z => (ST.real(~T, ST.LS{tag, cap, fresh, free, head, tail, depth, vT, pT, nT, gT, sl, fl}), z), S.values(T, AR.slots(Maybe<&2, T>, vT), sl), S.list_of(T, ST.model(~T, ST.LS{tag, cap, fresh, free, head, tail, depth, vT, pT, nT, gT, sl, fl})), Equal.sym(List<&2, T>, S.list_of(T, ST.model(~T, ST.LS{tag, cap, fresh, free, head, tail, depth, vT, pT, nT, gT, sl, fl})), S.values(T, AR.slots(Maybe<&2, T>, vT), sl), SP.spec_list(~T, one, h1, tag, cap, fresh, free, head, tail, depth, vT, pT, nT, gT, sl, fl, hg)))
      Equal.trans(D.DList<T> & List<&2, T>, D.to_list(~T, ST.real(~T, ST.LS{tag, cap, fresh, free, head, tail, depth, vT, pT, nT, gT, sl, fl})), (ST.real(~T, ST.LS{tag, cap, fresh, free, head, tail, depth, vT, pT, nT, gT, sl, fl}), S.values(T, AR.slots(Maybe<&2, T>, vT), sl)), (ST.real(~T, ST.LS{tag, cap, fresh, free, head, tail, depth, vT, pT, nT, gT, sl, fl}), S.list_of(T, ST.model(~T, ST.LS{tag, cap, fresh, free, head, tail, depth, vT, pT, nT, gT, sl, fl}))), e1, e2)


# a refined trace observes what the specification does
def obs_eq(~T: Data, +ops: List<&2, E.Op<T>>, +sh: ST.Sh<T>, t: TR.TraceOK(~T, ops, sh)) -> {Pair.snd(D.DList<T>, List<&2, E.Obs<T>>, D.run(~T, ops, ST.real(~T, sh))) == Pair.snd(S.DS<T>, List<&2, E.Obs<T>>, S.run(T, ops, ST.model(~T, sh))) : List<&2, E.Obs<T>>}:
  match t:
    case Tuple{+sh2, Tuple{+os, Tuple{+er, Tuple{+es, hg2}}}}:
      Equal.trans(List<&2, E.Obs<T>>, Pair.snd(D.DList<T>, List<&2, E.Obs<T>>, D.run(~T, ops, ST.real(~T, sh))), os, Pair.snd(S.DS<T>, List<&2, E.Obs<T>>, S.run(T, ops, ST.model(~T, sh))), Equal.cong(D.DList<T> & List<&2, E.Obs<T>>, List<&2, E.Obs<T>>, r => Pair.snd(D.DList<T>, List<&2, E.Obs<T>>, r), D.run(~T, ops, ST.real(~T, sh)), (ST.real(~T, sh2), os), er), Equal.sym(List<&2, E.Obs<T>>, Pair.snd(S.DS<T>, List<&2, E.Obs<T>>, S.run(T, ops, ST.model(~T, sh))), os, Equal.cong(S.DS<T> & List<&2, E.Obs<T>>, List<&2, E.Obs<T>>, r => Pair.snd(S.DS<T>, List<&2, E.Obs<T>>, r), S.run(T, ops, ST.model(~T, sh)), (ST.model(~T, sh2), os), es)))
