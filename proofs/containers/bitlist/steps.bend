import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/list.bend as LL
import ../../../spec/lib/common.bend as SC
import ../../lib/arith.bend as AT
import ../../../src/containers/bitset.bend as B
import ../../../src/containers/bitlist.bend as BLI
import ../../../src/containers/types/bitlist.bend as E
import ../../../src/containers/dynamic_array.bend as D
import ../../../src/containers/types/dynamic_array.bend as DE
import ../../../spec/containers/dynamic_array.bend as DS
import ../dynamic_array/state.bend as DAS
import ../dynamic_array/steps.bend as DSP
import ../dynamic_array/trace.bend as DTR
import ../bitset/lists.bend as BL
import ../bitset/listx.bend as LX
import ../bitset/model.bend as MD
import ../bitset/walk.bend as WK
import ../bitset/state.bend as ST
import ../bitset/steps.bend as BSS
import ../../../spec/containers/bitlist.bend as S
import ./da.bend as DI
import ./bits.bend as BT
import ./state.bend as SS
import ./loops.bend as LP

# Every public bitlist operation, errors included, lands on the bitlist of
# another good shadow whose model and answer are the specification step
# (the SPARK-style "effect on the whole model" statement: S.step is the
# postcondition, the shared StepOK shape carries the frame conditions).
# (source: proofs/containers/bitlist/steps.src)


def StepOK(sh: SS.Sh, op: E.Op) -> Type:
  Sigma<&1, &1, SS.Sh, sh_2 => Sigma<&1, &1, E.Obs, o_2 => {BLI.step(SS.real(sh), op) == (SS.real(sh_2), o_2) : BLI.Bitlist & E.Obs} & ({SS.good(sh_2) == True{} : Bool} & {(SS.model(sh_2), o_2) == S.step(SS.model(sh), op) : S.Model & E.Obs})>>

# ---- index facts ----

def len_flat(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}) -> {SC.length(Bool, ST.flat(DI.ws(w))) == Nat.mul(SC.length(U32, DI.ws(w)), 32n) : Nat}:
  ST.length_flat(DI.ws(w))

def n_le_flat(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}) -> {Nat.is_le(n, SC.length(Bool, ST.flat(DI.ws(w)))) == True{} : Bool}:
  ST.inv_le(n, ST.flat(DI.ws(w)), SS.g_inv(l, n, w, g))

def wq(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}, +i: Nat, +hi: {Nat.is_lt(i, SC.length(Bool, ST.flat(DI.ws(w)))) == True{} : Bool}) -> {Nat.is_lt(B.wordix(i), SC.length(U32, DI.ws(w))) == True{} : Bool}:
  ST.wordix_lt(i, SC.length(U32, DI.ws(w)), L.subst(Nat, z => {Nat.is_lt(i, z) == True{} : Bool}, SC.length(Bool, ST.flat(DI.ws(w))), Nat.mul(SC.length(U32, DI.ws(w)), 32n), len_flat(l, n, w, g, gw), hi))

def in_flat(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}, +i: Nat, +hi: {Nat.is_lt(i, n) == True{} : Bool}) -> {Nat.is_lt(i, SC.length(Bool, ST.flat(DI.ws(w)))) == True{} : Bool}:
  N.lt_le_trans(i, n, SC.length(Bool, ST.flat(DI.ws(w))), hi, n_le_flat(l, n, w, g, gw))

# ---- length and limit ----

def length_ok(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}) -> StepOK(SS.BSh{l, n, w}, E.Length{}):
  (SS.BSh{l, n, w}, (E.ONat{n}, ({==}, (g,
    %Equal.sym(Nat, SC.length(Bool, SC.take(Bool, ST.flat(DI.ws(w)), n)), n, ST.length_abs(n, ST.flat(DI.ws(w)), SS.g_inv(l, n, w, g))) : {(S.M{l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n)}, E.ONat{n}) == (S.M{l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n)}, E.ONat{_}) : S.Model & E.Obs}
    {==}))))

def limit_ok(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}) -> StepOK(SS.BSh{l, n, w}, E.Limit{}):
  (SS.BSh{l, n, w}, (E.OLimit{l}, ({==}, (g, {==}))))

# ---- get ----


def get_real(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}, +i: Nat, +hi: {Nat.is_lt(i, n) == True{} : Bool}) -> {BLI.get_word(i, l, n, D.get(U32, DAS.real(U32, w), B.wordix(i))) == (SS.real(SS.BSh{l, n, DI.gsh(w, gw, B.wordix(i))}), Done{B.word_get(WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i))}) : BLI.Bitlist & Result<&2, &2, E.Error, Bool>}:
  %Equal.sym(D.DynArray<&2, U32> & Result<&2, &2, DE.Error, U32>, D.get(U32, DAS.real(U32, w), B.wordix(i)), (DAS.real(U32, DI.gsh(w, gw, B.wordix(i))), DI.unitem(DTR.so_obs(U32, w, DE.Get{B.wordix(i)}, DSP.step_ok(U32, w, DE.Get{B.wordix(i)}, gw)))), DI.get_eq(w, gw, B.wordix(i))) : {BLI.get_word(i, l, n, _) == (SS.real(SS.BSh{l, n, DI.gsh(w, gw, B.wordix(i))}), Done{B.word_get(WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i))}) : BLI.Bitlist & Result<&2, &2, E.Error, Bool>}
  %Equal.sym(Result<&2, &2, DE.Error, U32>, DI.unitem(DTR.so_obs(U32, w, DE.Get{B.wordix(i)}, DSP.step_ok(U32, w, DE.Get{B.wordix(i)}, gw))), DS.item_result(U32, SC.nth(U32, DI.ws(w), B.wordix(i))), DI.get_val(w, gw, B.wordix(i))) : {BLI.get_word(i, l, n, (DAS.real(U32, DI.gsh(w, gw, B.wordix(i))), _)) == (SS.real(SS.BSh{l, n, DI.gsh(w, gw, B.wordix(i))}), Done{B.word_get(WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i))}) : BLI.Bitlist & Result<&2, &2, E.Error, Bool>}
  %Equal.sym(Maybe<&2, U32>, SC.nth(U32, DI.ws(w), B.wordix(i)), Some{WK.nthw(DI.ws(w), B.wordix(i))}, WK.nthw_nth(DI.ws(w), B.wordix(i), wq(l, n, w, g, gw, i, in_flat(l, n, w, g, gw, i, hi)))) : {BLI.get_word(i, l, n, (DAS.real(U32, DI.gsh(w, gw, B.wordix(i))), DS.item_result(U32, _))) == (SS.real(SS.BSh{l, n, DI.gsh(w, gw, B.wordix(i))}), Done{B.word_get(WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i))}) : BLI.Bitlist & Result<&2, &2, E.Error, Bool>}
  {==}

def get_model(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}, +i: Nat) -> {SS.model(SS.BSh{l, n, DI.gsh(w, gw, B.wordix(i))}) == S.M{l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n)} : S.Model}:
  SS.model_of(l, n, DI.gsh(w, gw, B.wordix(i)), DI.ws(w), DI.lim(w), DI.get_ws(w, gw, B.wordix(i)), DI.get_lim(w, gw, B.wordix(i)))

def get_good(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}, +i: Nat) -> {SS.good(SS.BSh{l, n, DI.gsh(w, gw, B.wordix(i))}) == True{} : Bool}:
  SS.same_good(l, n, w, DI.gsh(w, gw, B.wordix(i)), DI.get_good(w, gw, B.wordix(i)), DI.get_ws(w, gw, B.wordix(i)), g)

def get_bit(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}, +i: Nat, +hi: {Nat.is_lt(i, n) == True{} : Bool}) -> {Some{B.word_get(WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i))} == SC.nth(Bool, SC.take(Bool, ST.flat(DI.ws(w)), n), i) : Maybe<&2, Bool>}:
  %WK.get_index(DI.ws(w), i) : {Some{_} == SC.nth(Bool, SC.take(Bool, ST.flat(DI.ws(w)), n), i) : Maybe<&2, Bool>}
  BSS.nth_in(n, DI.ws(w), i, hi, SS.g_inv(l, n, w, g))

def get_case(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}, +i: Nat, b: Bool, +eb: {Nat.is_lt(i, n) == b : Bool}) -> StepOK(SS.BSh{l, n, w}, E.Get{i}):
  match b:
    case True{}:
      (SS.BSh{l, n, DI.gsh(w, gw, B.wordix(i))}, (E.OBit{Done{B.word_get(WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i))}},
        (%Equal.sym(Bool, Nat.is_lt(i, n), True{}, eb) : {BLI.obs_bit(BLI.get_if(_, l, n, DAS.real(U32, w), i)) == (SS.real(SS.BSh{l, n, DI.gsh(w, gw, B.wordix(i))}), E.OBit{Done{B.word_get(WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i))}}) : BLI.Bitlist & E.Obs}
         %Equal.sym(BLI.Bitlist & Result<&2, &2, E.Error, Bool>, BLI.get_word(i, l, n, D.get(U32, DAS.real(U32, w), B.wordix(i))), (SS.real(SS.BSh{l, n, DI.gsh(w, gw, B.wordix(i))}), Done{B.word_get(WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i))}), get_real(l, n, w, g, gw, i, eb)) : {BLI.obs_bit(_) == (SS.real(SS.BSh{l, n, DI.gsh(w, gw, B.wordix(i))}), E.OBit{Done{B.word_get(WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i))}}) : BLI.Bitlist & E.Obs}
         {==},
        (get_good(l, n, w, g, gw, i),
         %Equal.sym(S.Model, SS.model(SS.BSh{l, n, DI.gsh(w, gw, B.wordix(i))}), S.M{l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n)}, get_model(l, n, w, g, gw, i)) : {(_, E.OBit{Done{B.word_get(WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i))}}) == (S.M{l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n)}, E.OBit{S.bit(SC.nth(Bool, SC.take(Bool, ST.flat(DI.ws(w)), n), i))}) : S.Model & E.Obs}
         %Equal.sym(Maybe<&2, Bool>, SC.nth(Bool, SC.take(Bool, ST.flat(DI.ws(w)), n), i), Some{B.word_get(WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i))}, Equal.sym(Maybe<&2, Bool>, Some{B.word_get(WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i))}, SC.nth(Bool, SC.take(Bool, ST.flat(DI.ws(w)), n), i), get_bit(l, n, w, g, gw, i, eb))) : {(S.M{l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n)}, E.OBit{Done{B.word_get(WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i))}}) == (S.M{l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n)}, E.OBit{S.bit(_)}) : S.Model & E.Obs}
         {==}))))
    case False{}:
      (SS.BSh{l, n, w}, (E.OBit{Fail{E.IndexOutOfRange{}}},
        (%Equal.sym(Bool, Nat.is_lt(i, n), False{}, eb) : {BLI.obs_bit(BLI.get_if(_, l, n, DAS.real(U32, w), i)) == (SS.real(SS.BSh{l, n, w}), E.OBit{Fail{E.IndexOutOfRange{}}}) : BLI.Bitlist & E.Obs}
         {==},
        (g,
         %Equal.sym(Maybe<&2, Bool>, SC.nth(Bool, SC.take(Bool, ST.flat(DI.ws(w)), n), i), None{}, Equal.sym(Maybe<&2, Bool>, None{}, SC.nth(Bool, SC.take(Bool, ST.flat(DI.ws(w)), n), i), BSS.nth_out(n, DI.ws(w), i, eb, SS.g_inv(l, n, w, g)))) : {(S.M{l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n)}, E.OBit{Fail{E.IndexOutOfRange{}}}) == (S.M{l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n)}, E.OBit{S.bit(_)}) : S.Model & E.Obs}
         {==}))))

# ---- assign (and so set / unset) ----


def q_in2(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}, +i: Nat, +hi: {Nat.is_lt(i, n) == True{} : Bool}) -> {Nat.is_lt(B.wordix(i), SC.length(U32, DI.ws(DI.gsh(w, gw, B.wordix(i))))) == True{} : Bool}:
  L.subst(List<&2, U32>, z => {Nat.is_lt(B.wordix(i), SC.length(U32, z)) == True{} : Bool}, DI.ws(w), DI.ws(DI.gsh(w, gw, B.wordix(i))), Equal.sym(List<&2, U32>, DI.ws(DI.gsh(w, gw, B.wordix(i))), DI.ws(w), DI.get_ws(w, gw, B.wordix(i))), wq(l, n, w, g, gw, i, in_flat(l, n, w, g, gw, i, hi)))

def ws2(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}, +i: Nat, +v: Bool, +hi: {Nat.is_lt(i, n) == True{} : Bool}) -> {DI.ws(DI.ssh(DI.gsh(w, gw, B.wordix(i)), DI.get_good(w, gw, B.wordix(i)), B.wordix(i), B.word_put(v, WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i)))) == MD.put_walk(DI.ws(w), i, v) : List<&2, U32>}:
  %Equal.sym(List<&2, U32>, DI.ws(DI.ssh(DI.gsh(w, gw, B.wordix(i)), DI.get_good(w, gw, B.wordix(i)), B.wordix(i), B.word_put(v, WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i)))), SC.update(U32, DI.ws(DI.gsh(w, gw, B.wordix(i))), B.wordix(i), B.word_put(v, WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i))), DI.set_ws(DI.gsh(w, gw, B.wordix(i)), DI.get_good(w, gw, B.wordix(i)), B.wordix(i), B.word_put(v, WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i)), q_in2(l, n, w, g, gw, i, hi))) : {_ == MD.put_walk(DI.ws(w), i, v) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, DI.ws(DI.gsh(w, gw, B.wordix(i))), DI.ws(w), DI.get_ws(w, gw, B.wordix(i))) : {SC.update(U32, _, B.wordix(i), B.word_put(v, WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i))) == MD.put_walk(DI.ws(w), i, v) : List<&2, U32>}
  Equal.sym(List<&2, U32>, MD.put_walk(DI.ws(w), i, v), SC.update(U32, DI.ws(w), B.wordix(i), B.word_put(v, WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i))), WK.put_index(DI.ws(w), i, v))

def lim2(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}, +i: Nat, +v: Bool, +hi: {Nat.is_lt(i, n) == True{} : Bool}) -> {DI.lim(DI.ssh(DI.gsh(w, gw, B.wordix(i)), DI.get_good(w, gw, B.wordix(i)), B.wordix(i), B.word_put(v, WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i)))) == DI.lim(w) : Nat}:
  Equal.trans(Nat, DI.lim(DI.ssh(DI.gsh(w, gw, B.wordix(i)), DI.get_good(w, gw, B.wordix(i)), B.wordix(i), B.word_put(v, WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i)))), DI.lim(DI.gsh(w, gw, B.wordix(i))), DI.lim(w), DI.set_lim(DI.gsh(w, gw, B.wordix(i)), DI.get_good(w, gw, B.wordix(i)), B.wordix(i), B.word_put(v, WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i)), q_in2(l, n, w, g, gw, i, hi)), DI.get_lim(w, gw, B.wordix(i)))

def assign_real(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}, +i: Nat, +v: Bool, +hi: {Nat.is_lt(i, n) == True{} : Bool}) -> {BLI.assign_word(i, v, l, n, D.get(U32, DAS.real(U32, w), B.wordix(i))) == (SS.real(SS.BSh{l, n, DI.ssh(DI.gsh(w, gw, B.wordix(i)), DI.get_good(w, gw, B.wordix(i)), B.wordix(i), B.word_put(v, WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i)))}), Done{Unit{}}) : BLI.Bitlist & Result<&2, &2, E.Error, Unit>}:
  %Equal.sym(D.DynArray<&2, U32> & Result<&2, &2, DE.Error, U32>, D.get(U32, DAS.real(U32, w), B.wordix(i)), (DAS.real(U32, DI.gsh(w, gw, B.wordix(i))), DI.unitem(DTR.so_obs(U32, w, DE.Get{B.wordix(i)}, DSP.step_ok(U32, w, DE.Get{B.wordix(i)}, gw)))), DI.get_eq(w, gw, B.wordix(i))) : {BLI.assign_word(i, v, l, n, _) == (SS.real(SS.BSh{l, n, DI.ssh(DI.gsh(w, gw, B.wordix(i)), DI.get_good(w, gw, B.wordix(i)), B.wordix(i), B.word_put(v, WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i)))}), Done{Unit{}}) : BLI.Bitlist & Result<&2, &2, E.Error, Unit>}
  %Equal.sym(Result<&2, &2, DE.Error, U32>, DI.unitem(DTR.so_obs(U32, w, DE.Get{B.wordix(i)}, DSP.step_ok(U32, w, DE.Get{B.wordix(i)}, gw))), DS.item_result(U32, SC.nth(U32, DI.ws(w), B.wordix(i))), DI.get_val(w, gw, B.wordix(i))) : {BLI.assign_word(i, v, l, n, (DAS.real(U32, DI.gsh(w, gw, B.wordix(i))), _)) == (SS.real(SS.BSh{l, n, DI.ssh(DI.gsh(w, gw, B.wordix(i)), DI.get_good(w, gw, B.wordix(i)), B.wordix(i), B.word_put(v, WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i)))}), Done{Unit{}}) : BLI.Bitlist & Result<&2, &2, E.Error, Unit>}
  %Equal.sym(Maybe<&2, U32>, SC.nth(U32, DI.ws(w), B.wordix(i)), Some{WK.nthw(DI.ws(w), B.wordix(i))}, WK.nthw_nth(DI.ws(w), B.wordix(i), wq(l, n, w, g, gw, i, in_flat(l, n, w, g, gw, i, hi)))) : {BLI.assign_word(i, v, l, n, (DAS.real(U32, DI.gsh(w, gw, B.wordix(i))), DS.item_result(U32, _))) == (SS.real(SS.BSh{l, n, DI.ssh(DI.gsh(w, gw, B.wordix(i)), DI.get_good(w, gw, B.wordix(i)), B.wordix(i), B.word_put(v, WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i)))}), Done{Unit{}}) : BLI.Bitlist & Result<&2, &2, E.Error, Unit>}
  %Equal.sym(D.DynArray<&2, U32> & Result<&2, &2, DE.Error, Unit>, D.set(U32, DAS.real(U32, DI.gsh(w, gw, B.wordix(i))), B.wordix(i), B.word_put(v, WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i))), (DAS.real(U32, DI.ssh(DI.gsh(w, gw, B.wordix(i)), DI.get_good(w, gw, B.wordix(i)), B.wordix(i), B.word_put(v, WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i)))), DI.ununit(DTR.so_obs(U32, DI.gsh(w, gw, B.wordix(i)), DE.Set{B.wordix(i), B.word_put(v, WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i))}, DSP.step_ok(U32, DI.gsh(w, gw, B.wordix(i)), DE.Set{B.wordix(i), B.word_put(v, WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i))}, DI.get_good(w, gw, B.wordix(i)))))), DI.set_eq(DI.gsh(w, gw, B.wordix(i)), DI.get_good(w, gw, B.wordix(i)), B.wordix(i), B.word_put(v, WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i)))) : {BLI.assign_set(l, n, _) == (SS.real(SS.BSh{l, n, DI.ssh(DI.gsh(w, gw, B.wordix(i)), DI.get_good(w, gw, B.wordix(i)), B.wordix(i), B.word_put(v, WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i)))}), Done{Unit{}}) : BLI.Bitlist & Result<&2, &2, E.Error, Unit>}
  %Equal.sym(Result<&2, &2, DE.Error, Unit>, DI.ununit(DTR.so_obs(U32, DI.gsh(w, gw, B.wordix(i)), DE.Set{B.wordix(i), B.word_put(v, WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i))}, DSP.step_ok(U32, DI.gsh(w, gw, B.wordix(i)), DE.Set{B.wordix(i), B.word_put(v, WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i))}, DI.get_good(w, gw, B.wordix(i))))), Done{Unit{}}, DI.set_val(DI.gsh(w, gw, B.wordix(i)), DI.get_good(w, gw, B.wordix(i)), B.wordix(i), B.word_put(v, WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i)), q_in2(l, n, w, g, gw, i, hi))) : {BLI.assign_set(l, n, (DAS.real(U32, DI.ssh(DI.gsh(w, gw, B.wordix(i)), DI.get_good(w, gw, B.wordix(i)), B.wordix(i), B.word_put(v, WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i)))), _)) == (SS.real(SS.BSh{l, n, DI.ssh(DI.gsh(w, gw, B.wordix(i)), DI.get_good(w, gw, B.wordix(i)), B.wordix(i), B.word_put(v, WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i)))}), Done{Unit{}}) : BLI.Bitlist & Result<&2, &2, E.Error, Unit>}
  {==}

def assign_model(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}, +i: Nat, +v: Bool, +hi: {Nat.is_lt(i, n) == True{} : Bool}) -> {SS.model(SS.BSh{l, n, DI.ssh(DI.gsh(w, gw, B.wordix(i)), DI.get_good(w, gw, B.wordix(i)), B.wordix(i), B.word_put(v, WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i)))}) == S.M{l, DI.lim(w), SC.update(Bool, SC.take(Bool, ST.flat(DI.ws(w)), n), i, v)} : S.Model}:
  %Equal.sym(S.Model, SS.model(SS.BSh{l, n, DI.ssh(DI.gsh(w, gw, B.wordix(i)), DI.get_good(w, gw, B.wordix(i)), B.wordix(i), B.word_put(v, WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i)))}), S.M{l, DI.lim(w), SC.take(Bool, ST.flat(MD.put_walk(DI.ws(w), i, v)), n)}, SS.model_of(l, n, DI.ssh(DI.gsh(w, gw, B.wordix(i)), DI.get_good(w, gw, B.wordix(i)), B.wordix(i), B.word_put(v, WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i))), MD.put_walk(DI.ws(w), i, v), DI.lim(w), ws2(l, n, w, g, gw, i, v, hi), lim2(l, n, w, g, gw, i, v, hi))) : {_ == S.M{l, DI.lim(w), SC.update(Bool, SC.take(Bool, ST.flat(DI.ws(w)), n), i, v)} : S.Model}
  %Equal.sym(List<&2, Bool>, SC.take(Bool, ST.flat(MD.put_walk(DI.ws(w), i, v)), n), SC.update(Bool, SC.take(Bool, ST.flat(DI.ws(w)), n), i, v), ST.put_abs(n, DI.ws(w), i, v)) : {S.M{l, DI.lim(w), _} == S.M{l, DI.lim(w), SC.update(Bool, SC.take(Bool, ST.flat(DI.ws(w)), n), i, v)} : S.Model}
  {==}

def assign_good(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}, +i: Nat, +v: Bool, +hi: {Nat.is_lt(i, n) == True{} : Bool}) -> {SS.good(SS.BSh{l, n, DI.ssh(DI.gsh(w, gw, B.wordix(i)), DI.get_good(w, gw, B.wordix(i)), B.wordix(i), B.word_put(v, WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i)))}) == True{} : Bool}:
  SS.good_of(l, n, DI.ssh(DI.gsh(w, gw, B.wordix(i)), DI.get_good(w, gw, B.wordix(i)), B.wordix(i), B.word_put(v, WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i))), MD.put_walk(DI.ws(w), i, v), DI.set_good(DI.gsh(w, gw, B.wordix(i)), DI.get_good(w, gw, B.wordix(i)), B.wordix(i), B.word_put(v, WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i))), ws2(l, n, w, g, gw, i, v, hi), ST.put_inv(n, DI.ws(w), i, v, hi, SS.g_inv(l, n, w, g)))

def assign_case(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}, +i: Nat, +v: Bool, b: Bool, +eb: {Nat.is_lt(i, n) == b : Bool}) -> StepOK(SS.BSh{l, n, w}, E.Assign{i, v}):
  match b:
    case True{}:
      (SS.BSh{l, n, DI.ssh(DI.gsh(w, gw, B.wordix(i)), DI.get_good(w, gw, B.wordix(i)), B.wordix(i), B.word_put(v, WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i)))}, (E.OUnit{Done{Unit{}}},
        (%Equal.sym(Bool, Nat.is_lt(i, n), True{}, eb) : {BLI.obs_unit(BLI.assign_if(_, l, n, DAS.real(U32, w), i, v)) == (SS.real(SS.BSh{l, n, DI.ssh(DI.gsh(w, gw, B.wordix(i)), DI.get_good(w, gw, B.wordix(i)), B.wordix(i), B.word_put(v, WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i)))}), E.OUnit{Done{Unit{}}}) : BLI.Bitlist & E.Obs}
         %Equal.sym(BLI.Bitlist & Result<&2, &2, E.Error, Unit>, BLI.assign_word(i, v, l, n, D.get(U32, DAS.real(U32, w), B.wordix(i))), (SS.real(SS.BSh{l, n, DI.ssh(DI.gsh(w, gw, B.wordix(i)), DI.get_good(w, gw, B.wordix(i)), B.wordix(i), B.word_put(v, WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i)))}), Done{Unit{}}), assign_real(l, n, w, g, gw, i, v, eb)) : {BLI.obs_unit(_) == (SS.real(SS.BSh{l, n, DI.ssh(DI.gsh(w, gw, B.wordix(i)), DI.get_good(w, gw, B.wordix(i)), B.wordix(i), B.word_put(v, WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i)))}), E.OUnit{Done{Unit{}}}) : BLI.Bitlist & E.Obs}
         {==},
        (assign_good(l, n, w, g, gw, i, v, eb),
         %Equal.sym(S.Model, SS.model(SS.BSh{l, n, DI.ssh(DI.gsh(w, gw, B.wordix(i)), DI.get_good(w, gw, B.wordix(i)), B.wordix(i), B.word_put(v, WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i)))}), S.M{l, DI.lim(w), SC.update(Bool, SC.take(Bool, ST.flat(DI.ws(w)), n), i, v)}, assign_model(l, n, w, g, gw, i, v, eb)) : {(_, E.OUnit{Done{Unit{}}}) == S.assign_at(SC.nth(Bool, SC.take(Bool, ST.flat(DI.ws(w)), n), i), l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n), i, v) : S.Model & E.Obs}
         %Equal.sym(Maybe<&2, Bool>, SC.nth(Bool, SC.take(Bool, ST.flat(DI.ws(w)), n), i), Some{B.word_get(WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i))}, Equal.sym(Maybe<&2, Bool>, Some{B.word_get(WK.nthw(DI.ws(w), B.wordix(i)), B.bitix(i))}, SC.nth(Bool, SC.take(Bool, ST.flat(DI.ws(w)), n), i), get_bit(l, n, w, g, gw, i, eb))) : {(S.M{l, DI.lim(w), SC.update(Bool, SC.take(Bool, ST.flat(DI.ws(w)), n), i, v)}, E.OUnit{Done{Unit{}}}) == S.assign_at(_, l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n), i, v) : S.Model & E.Obs}
         {==}))))
    case False{}:
      (SS.BSh{l, n, w}, (E.OUnit{Fail{E.IndexOutOfRange{}}},
        (%Equal.sym(Bool, Nat.is_lt(i, n), False{}, eb) : {BLI.obs_unit(BLI.assign_if(_, l, n, DAS.real(U32, w), i, v)) == (SS.real(SS.BSh{l, n, w}), E.OUnit{Fail{E.IndexOutOfRange{}}}) : BLI.Bitlist & E.Obs}
         {==},
        (g,
         %Equal.sym(Maybe<&2, Bool>, SC.nth(Bool, SC.take(Bool, ST.flat(DI.ws(w)), n), i), None{}, Equal.sym(Maybe<&2, Bool>, None{}, SC.nth(Bool, SC.take(Bool, ST.flat(DI.ws(w)), n), i), BSS.nth_out(n, DI.ws(w), i, eb, SS.g_inv(l, n, w, g)))) : {(S.M{l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n)}, E.OUnit{Fail{E.IndexOutOfRange{}}}) == S.assign_at(_, l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n), i, v) : S.Model & E.Obs}
         {==}))))

# ---- push ----


def sp_push_t(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +v: Bool, +n: Nat, +hlen: {SC.length(Bool, xs) == n : Nat}, +hl: {S.below(l, n) == True{} : Bool}, +hn: {Nat.is_lt(n, Nat.mul(SC.pow2(c), 32n)) == True{} : Bool}) -> {S.step_parts(l, c, xs, E.Push{v}) == (S.M{l, c, SC.snoc(Bool, xs, v)}, E.OUnit{Done{Unit{}}}) : S.Model & E.Obs}:
  %Equal.sym(Nat, SC.length(Bool, xs), n, hlen) : {S.push_if(Bool.and(S.below(l, _), Nat.is_lt(_, Nat.mul(SC.pow2(c), 32n))), l, c, xs, v) == (S.M{l, c, SC.snoc(Bool, xs, v)}, E.OUnit{Done{Unit{}}}) : S.Model & E.Obs}
  %Equal.sym(Bool, S.below(l, n), True{}, hl) : {S.push_if(Bool.and(_, Nat.is_lt(n, Nat.mul(SC.pow2(c), 32n))), l, c, xs, v) == (S.M{l, c, SC.snoc(Bool, xs, v)}, E.OUnit{Done{Unit{}}}) : S.Model & E.Obs}
  %Equal.sym(Bool, Nat.is_lt(n, Nat.mul(SC.pow2(c), 32n)), True{}, hn) : {S.push_if(Bool.and(True{}, _), l, c, xs, v) == (S.M{l, c, SC.snoc(Bool, xs, v)}, E.OUnit{Done{Unit{}}}) : S.Model & E.Obs}
  {==}

def sp_push_fl(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +v: Bool, +n: Nat, +hlen: {SC.length(Bool, xs) == n : Nat}, +hl: {S.below(l, n) == False{} : Bool}) -> {S.step_parts(l, c, xs, E.Push{v}) == (S.M{l, c, xs}, E.OUnit{Fail{E.Full{}}}) : S.Model & E.Obs}:
  %Equal.sym(Nat, SC.length(Bool, xs), n, hlen) : {S.push_if(Bool.and(S.below(l, _), Nat.is_lt(_, Nat.mul(SC.pow2(c), 32n))), l, c, xs, v) == (S.M{l, c, xs}, E.OUnit{Fail{E.Full{}}}) : S.Model & E.Obs}
  %Equal.sym(Bool, S.below(l, n), False{}, hl) : {S.push_if(Bool.and(_, Nat.is_lt(n, Nat.mul(SC.pow2(c), 32n))), l, c, xs, v) == (S.M{l, c, xs}, E.OUnit{Fail{E.Full{}}}) : S.Model & E.Obs}
  {==}

def sp_push_fc(+l: Maybe<&2, Nat>, +c: Nat, +xs: List<&2, Bool>, +v: Bool, +n: Nat, +hlen: {SC.length(Bool, xs) == n : Nat}, +hl: {S.below(l, n) == True{} : Bool}, +hn: {Nat.is_lt(n, Nat.mul(SC.pow2(c), 32n)) == False{} : Bool}) -> {S.step_parts(l, c, xs, E.Push{v}) == (S.M{l, c, xs}, E.OUnit{Fail{E.Full{}}}) : S.Model & E.Obs}:
  %Equal.sym(Nat, SC.length(Bool, xs), n, hlen) : {S.push_if(Bool.and(S.below(l, _), Nat.is_lt(_, Nat.mul(SC.pow2(c), 32n))), l, c, xs, v) == (S.M{l, c, xs}, E.OUnit{Fail{E.Full{}}}) : S.Model & E.Obs}
  %Equal.sym(Bool, S.below(l, n), True{}, hl) : {S.push_if(Bool.and(_, Nat.is_lt(n, Nat.mul(SC.pow2(c), 32n))), l, c, xs, v) == (S.M{l, c, xs}, E.OUnit{Fail{E.Full{}}}) : S.Model & E.Obs}
  %Equal.sym(Bool, Nat.is_lt(n, Nat.mul(SC.pow2(c), 32n)), False{}, hn) : {S.push_if(Bool.and(True{}, _), l, c, xs, v) == (S.M{l, c, xs}, E.OUnit{Fail{E.Full{}}}) : S.Model & E.Obs}
  {==}


# the length read of the word array
def push_len(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}, +v: Bool) -> {BLI.push_room(l, n, v, D.length(U32, DAS.real(U32, w))) == BLI.push_where(Nat.is_lt(n, Nat.mul(SC.length(U32, DI.ws(w)), 32n)), l, n, DAS.real(U32, DI.lsh(w, gw)), v) : BLI.Bitlist & Result<&2, &2, E.Error, Unit>}:
  %Equal.sym(D.DynArray<&2, U32> & Nat, D.length(U32, DAS.real(U32, w)), (DAS.real(U32, DI.lsh(w, gw)), DI.unnat(DTR.so_obs(U32, w, DE.Length{}, DSP.step_ok(U32, w, DE.Length{}, gw)))), DI.len_eq(w, gw)) : {BLI.push_room(l, n, v, _) == BLI.push_where(Nat.is_lt(n, Nat.mul(SC.length(U32, DI.ws(w)), 32n)), l, n, DAS.real(U32, DI.lsh(w, gw)), v) : BLI.Bitlist & Result<&2, &2, E.Error, Unit>}
  %Equal.sym(Nat, DI.unnat(DTR.so_obs(U32, w, DE.Length{}, DSP.step_ok(U32, w, DE.Length{}, gw))), SC.length(U32, DI.ws(w)), DI.len_val(w, gw)) : {BLI.push_room(l, n, v, (DAS.real(U32, DI.lsh(w, gw)), _)) == BLI.push_where(Nat.is_lt(n, Nat.mul(SC.length(U32, DI.ws(w)), 32n)), l, n, DAS.real(U32, DI.lsh(w, gw)), v) : BLI.Bitlist & Result<&2, &2, E.Error, Unit>}
  {==}

def room_in(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}, +d: {Nat.is_lt(n, Nat.mul(SC.length(U32, DI.ws(w)), 32n)) == True{} : Bool}) -> {Nat.is_lt(n, Nat.mul(SC.pow2(DI.lim(w)), 32n)) == True{} : Bool}:
  N.lt_le_trans(n, Nat.mul(SC.length(U32, DI.ws(w)), 32n), Nat.mul(SC.pow2(DI.lim(w)), 32n), d, AT.mul_le(SC.length(U32, DI.ws(w)), SC.pow2(DI.lim(w)), 32n, DI.wcap(w, gw)))

def in_f(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}, +d: {Nat.is_lt(n, Nat.mul(SC.length(U32, DI.ws(w)), 32n)) == True{} : Bool}) -> {Nat.is_lt(n, SC.length(Bool, ST.flat(DI.ws(w)))) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(n, z) == True{} : Bool}, Nat.mul(SC.length(U32, DI.ws(w)), 32n), SC.length(Bool, ST.flat(DI.ws(w))), Equal.sym(Nat, SC.length(Bool, ST.flat(DI.ws(w))), Nat.mul(SC.length(U32, DI.ws(w)), 32n), len_flat(l, n, w, g, gw)), d)

def g_inc(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}, +d: {Nat.is_lt(n, Nat.mul(SC.length(U32, DI.ws(w)), 32n)) == True{} : Bool}) -> {SS.good(SS.BSh{l, 1n+n, DI.lsh(w, gw)}) == True{} : Bool}:
  SS.good_of(l, 1n+n, DI.lsh(w, gw), DI.ws(w), DI.len_good(w, gw), DI.len_ws(w, gw), BT.invf_succ(n, ST.flat(DI.ws(w)), in_f(l, n, w, g, gw, d), SS.g_inv(l, n, w, g)))

def m_inc(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}) -> {SS.model(SS.BSh{l, 1n+n, DI.lsh(w, gw)}) == S.M{l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), 1n+n)} : S.Model}:
  SS.model_of(l, 1n+n, DI.lsh(w, gw), DI.ws(w), DI.lim(w), DI.len_ws(w, gw), DI.len_lim(w, gw))


# the zero bit below the new length: the stored bits spell the list plus it
def take_inc(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}, +d: {Nat.is_lt(n, Nat.mul(SC.length(U32, DI.ws(w)), 32n)) == True{} : Bool}) -> {SC.take(Bool, ST.flat(DI.ws(w)), 1n+n) == SC.snoc(Bool, SC.take(Bool, ST.flat(DI.ws(w)), n), False{}) : List<&2, Bool>}:
  BT.push_zero(n, ST.flat(DI.ws(w)), in_f(l, n, w, g, gw, d), SS.g_inv(l, n, w, g))

def set_last(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}, +d: {Nat.is_lt(n, Nat.mul(SC.length(U32, DI.ws(w)), 32n)) == True{} : Bool}) -> {S.M{l, DI.lim(DI.lsh(w, gw)), SC.update(Bool, SC.take(Bool, ST.flat(DI.ws(DI.lsh(w, gw))), 1n+n), n, True{})} == S.M{l, DI.lim(w), SC.snoc(Bool, SC.take(Bool, ST.flat(DI.ws(w)), n), True{})} : S.Model}:
  %Equal.sym(List<&2, U32>, DI.ws(DI.lsh(w, gw)), DI.ws(w), DI.len_ws(w, gw)) : {S.M{l, DI.lim(DI.lsh(w, gw)), SC.update(Bool, SC.take(Bool, ST.flat(_), 1n+n), n, True{})} == S.M{l, DI.lim(w), SC.snoc(Bool, SC.take(Bool, ST.flat(DI.ws(w)), n), True{})} : S.Model}
  %Equal.sym(Nat, DI.lim(DI.lsh(w, gw)), DI.lim(w), DI.len_lim(w, gw)) : {S.M{l, _, SC.update(Bool, SC.take(Bool, ST.flat(DI.ws(w)), 1n+n), n, True{})} == S.M{l, DI.lim(w), SC.snoc(Bool, SC.take(Bool, ST.flat(DI.ws(w)), n), True{})} : S.Model}
  %Equal.sym(List<&2, Bool>, SC.take(Bool, ST.flat(DI.ws(w)), 1n+n), SC.snoc(Bool, SC.take(Bool, ST.flat(DI.ws(w)), n), False{}), take_inc(l, n, w, g, gw, d)) : {S.M{l, DI.lim(w), SC.update(Bool, _, n, True{})} == S.M{l, DI.lim(w), SC.snoc(Bool, SC.take(Bool, ST.flat(DI.ws(w)), n), True{})} : S.Model}
  %Equal.sym(Nat, n, SC.length(Bool, SC.take(Bool, ST.flat(DI.ws(w)), n)), Equal.sym(Nat, SC.length(Bool, SC.take(Bool, ST.flat(DI.ws(w)), n)), n, ST.length_abs(n, ST.flat(DI.ws(w)), SS.g_inv(l, n, w, g)))) : {S.M{l, DI.lim(w), SC.update(Bool, SC.snoc(Bool, SC.take(Bool, ST.flat(DI.ws(w)), n), False{}), _, True{})} == S.M{l, DI.lim(w), SC.snoc(Bool, SC.take(Bool, ST.flat(DI.ws(w)), n), True{})} : S.Model}
  %Equal.sym(List<&2, Bool>, SC.update(Bool, SC.snoc(Bool, SC.take(Bool, ST.flat(DI.ws(w)), n), False{}), SC.length(Bool, SC.take(Bool, ST.flat(DI.ws(w)), n)), True{}), SC.snoc(Bool, SC.take(Bool, ST.flat(DI.ws(w)), n), True{}), BT.upd_snoc_end(SC.take(Bool, ST.flat(DI.ws(w)), n), False{}, True{})) : {S.M{l, DI.lim(w), _} == S.M{l, DI.lim(w), SC.snoc(Bool, SC.take(Bool, ST.flat(DI.ws(w)), n), True{})} : S.Model}
  {==}

def push_in_v(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}, +v: Bool, +d: {Nat.is_lt(n, Nat.mul(SC.length(U32, DI.ws(w)), 32n)) == True{} : Bool}, +hb: {BLI.below(l, n) == True{} : Bool}, +hs: {S.step_parts(l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n), E.Push{v}) == (S.M{l, DI.lim(w), SC.snoc(Bool, SC.take(Bool, ST.flat(DI.ws(w)), n), v)}, E.OUnit{Done{Unit{}}}) : S.Model & E.Obs}) -> StepOK(SS.BSh{l, n, w}, E.Push{v}):
  match v:
    case False{}:
      (SS.BSh{l, 1n+n, DI.lsh(w, gw)}, (E.OUnit{Done{Unit{}}},
        (%Equal.sym(Bool, BLI.below(l, n), True{}, hb) : {BLI.obs_unit(BLI.push_if(_, l, n, DAS.real(U32, w), False{})) == (SS.real(SS.BSh{l, 1n+n, DI.lsh(w, gw)}), E.OUnit{Done{Unit{}}}) : BLI.Bitlist & E.Obs}
         %Equal.sym(BLI.Bitlist & Result<&2, &2, E.Error, Unit>, BLI.push_room(l, n, False{}, D.length(U32, DAS.real(U32, w))), BLI.push_where(Nat.is_lt(n, Nat.mul(SC.length(U32, DI.ws(w)), 32n)), l, n, DAS.real(U32, DI.lsh(w, gw)), False{}), push_len(l, n, w, g, gw, False{})) : {BLI.obs_unit(_) == (SS.real(SS.BSh{l, 1n+n, DI.lsh(w, gw)}), E.OUnit{Done{Unit{}}}) : BLI.Bitlist & E.Obs}
         %Equal.sym(Bool, Nat.is_lt(n, Nat.mul(SC.length(U32, DI.ws(w)), 32n)), True{}, d) : {BLI.obs_unit(BLI.push_where(_, l, n, DAS.real(U32, DI.lsh(w, gw)), False{})) == (SS.real(SS.BSh{l, 1n+n, DI.lsh(w, gw)}), E.OUnit{Done{Unit{}}}) : BLI.Bitlist & E.Obs}
         {==},
        (g_inc(l, n, w, g, gw, d),
         %Equal.sym(S.Model, SS.model(SS.BSh{l, 1n+n, DI.lsh(w, gw)}), S.M{l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), 1n+n)}, m_inc(l, n, w, g, gw)) : {(_, E.OUnit{Done{Unit{}}}) == S.step_parts(l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n), E.Push{False{}}) : S.Model & E.Obs}
         %Equal.sym(List<&2, Bool>, SC.take(Bool, ST.flat(DI.ws(w)), 1n+n), SC.snoc(Bool, SC.take(Bool, ST.flat(DI.ws(w)), n), False{}), take_inc(l, n, w, g, gw, d)) : {(S.M{l, DI.lim(w), _}, E.OUnit{Done{Unit{}}}) == S.step_parts(l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n), E.Push{False{}}) : S.Model & E.Obs}
         Equal.sym(S.Model & E.Obs, S.step_parts(l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n), E.Push{False{}}), (S.M{l, DI.lim(w), SC.snoc(Bool, SC.take(Bool, ST.flat(DI.ws(w)), n), False{})}, E.OUnit{Done{Unit{}}}), hs)))))
    case True{}:
      (SS.BSh{l, 1n+n, DI.ssh(DI.gsh(DI.lsh(w, gw), DI.len_good(w, gw), B.wordix(n)), DI.get_good(DI.lsh(w, gw), DI.len_good(w, gw), B.wordix(n)), B.wordix(n), B.word_put(True{}, WK.nthw(DI.ws(DI.lsh(w, gw)), B.wordix(n)), B.bitix(n)))}, (E.OUnit{Done{Unit{}}},
        (%Equal.sym(Bool, BLI.below(l, n), True{}, hb) : {BLI.obs_unit(BLI.push_if(_, l, n, DAS.real(U32, w), True{})) == (SS.real(SS.BSh{l, 1n+n, DI.ssh(DI.gsh(DI.lsh(w, gw), DI.len_good(w, gw), B.wordix(n)), DI.get_good(DI.lsh(w, gw), DI.len_good(w, gw), B.wordix(n)), B.wordix(n), B.word_put(True{}, WK.nthw(DI.ws(DI.lsh(w, gw)), B.wordix(n)), B.bitix(n)))}), E.OUnit{Done{Unit{}}}) : BLI.Bitlist & E.Obs}
         %Equal.sym(BLI.Bitlist & Result<&2, &2, E.Error, Unit>, BLI.push_room(l, n, True{}, D.length(U32, DAS.real(U32, w))), BLI.push_where(Nat.is_lt(n, Nat.mul(SC.length(U32, DI.ws(w)), 32n)), l, n, DAS.real(U32, DI.lsh(w, gw)), True{}), push_len(l, n, w, g, gw, True{})) : {BLI.obs_unit(_) == (SS.real(SS.BSh{l, 1n+n, DI.ssh(DI.gsh(DI.lsh(w, gw), DI.len_good(w, gw), B.wordix(n)), DI.get_good(DI.lsh(w, gw), DI.len_good(w, gw), B.wordix(n)), B.wordix(n), B.word_put(True{}, WK.nthw(DI.ws(DI.lsh(w, gw)), B.wordix(n)), B.bitix(n)))}), E.OUnit{Done{Unit{}}}) : BLI.Bitlist & E.Obs}
         %Equal.sym(Bool, Nat.is_lt(n, Nat.mul(SC.length(U32, DI.ws(w)), 32n)), True{}, d) : {BLI.obs_unit(BLI.push_where(_, l, n, DAS.real(U32, DI.lsh(w, gw)), True{})) == (SS.real(SS.BSh{l, 1n+n, DI.ssh(DI.gsh(DI.lsh(w, gw), DI.len_good(w, gw), B.wordix(n)), DI.get_good(DI.lsh(w, gw), DI.len_good(w, gw), B.wordix(n)), B.wordix(n), B.word_put(True{}, WK.nthw(DI.ws(DI.lsh(w, gw)), B.wordix(n)), B.bitix(n)))}), E.OUnit{Done{Unit{}}}) : BLI.Bitlist & E.Obs}
         %Equal.sym(BLI.Bitlist & Result<&2, &2, E.Error, Unit>, BLI.assign_word(n, True{}, l, 1n+n, D.get(U32, DAS.real(U32, DI.lsh(w, gw)), B.wordix(n))), (SS.real(SS.BSh{l, 1n+n, DI.ssh(DI.gsh(DI.lsh(w, gw), DI.len_good(w, gw), B.wordix(n)), DI.get_good(DI.lsh(w, gw), DI.len_good(w, gw), B.wordix(n)), B.wordix(n), B.word_put(True{}, WK.nthw(DI.ws(DI.lsh(w, gw)), B.wordix(n)), B.bitix(n)))}), Done{Unit{}}), assign_real(l, 1n+n, DI.lsh(w, gw), g_inc(l, n, w, g, gw, d), DI.len_good(w, gw), n, True{}, N.lt_succ(n))) : {BLI.obs_unit(_) == (SS.real(SS.BSh{l, 1n+n, DI.ssh(DI.gsh(DI.lsh(w, gw), DI.len_good(w, gw), B.wordix(n)), DI.get_good(DI.lsh(w, gw), DI.len_good(w, gw), B.wordix(n)), B.wordix(n), B.word_put(True{}, WK.nthw(DI.ws(DI.lsh(w, gw)), B.wordix(n)), B.bitix(n)))}), E.OUnit{Done{Unit{}}}) : BLI.Bitlist & E.Obs}
         {==},
        (assign_good(l, 1n+n, DI.lsh(w, gw), g_inc(l, n, w, g, gw, d), DI.len_good(w, gw), n, True{}, N.lt_succ(n)),
         %Equal.sym(S.Model, SS.model(SS.BSh{l, 1n+n, DI.ssh(DI.gsh(DI.lsh(w, gw), DI.len_good(w, gw), B.wordix(n)), DI.get_good(DI.lsh(w, gw), DI.len_good(w, gw), B.wordix(n)), B.wordix(n), B.word_put(True{}, WK.nthw(DI.ws(DI.lsh(w, gw)), B.wordix(n)), B.bitix(n)))}), S.M{l, DI.lim(DI.lsh(w, gw)), SC.update(Bool, SC.take(Bool, ST.flat(DI.ws(DI.lsh(w, gw))), 1n+n), n, True{})}, assign_model(l, 1n+n, DI.lsh(w, gw), g_inc(l, n, w, g, gw, d), DI.len_good(w, gw), n, True{}, N.lt_succ(n))) : {(_, E.OUnit{Done{Unit{}}}) == S.step_parts(l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n), E.Push{True{}}) : S.Model & E.Obs}
         %Equal.sym(S.Model, S.M{l, DI.lim(DI.lsh(w, gw)), SC.update(Bool, SC.take(Bool, ST.flat(DI.ws(DI.lsh(w, gw))), 1n+n), n, True{})}, S.M{l, DI.lim(w), SC.snoc(Bool, SC.take(Bool, ST.flat(DI.ws(w)), n), True{})}, set_last(l, n, w, g, gw, d)) : {(_, E.OUnit{Done{Unit{}}}) == S.step_parts(l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n), E.Push{True{}}) : S.Model & E.Obs}
         Equal.sym(S.Model & E.Obs, S.step_parts(l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n), E.Push{True{}}), (S.M{l, DI.lim(w), SC.snoc(Bool, SC.take(Bool, ST.flat(DI.ws(w)), n), True{})}, E.OUnit{Done{Unit{}}}), hs)))))

def push_in_case(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}, +v: Bool, +d: {Nat.is_lt(n, Nat.mul(SC.length(U32, DI.ws(w)), 32n)) == True{} : Bool}, +hb: {BLI.below(l, n) == True{} : Bool}) -> StepOK(SS.BSh{l, n, w}, E.Push{v}):
  +hs = sp_push_t(l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n), v, n, ST.length_abs(n, ST.flat(DI.ws(w)), SS.g_inv(l, n, w, g)), Equal.trans(Bool, S.below(l, n), BLI.below(l, n), True{}, Equal.sym(Bool, BLI.below(l, n), S.below(l, n), BT.below_eq(l, n)), hb), room_in(l, n, w, g, gw, d))
  push_in_v(l, n, w, g, gw, v, d, hb, hs)

# ---- push into a new word (every stored bit in use) ----


def n_eq(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}, +d: {Nat.is_lt(n, Nat.mul(SC.length(U32, DI.ws(w)), 32n)) == False{} : Bool}) -> {n == SC.length(Bool, ST.flat(DI.ws(w))) : Nat}:
  N.le_antisym(n, SC.length(Bool, ST.flat(DI.ws(w))), n_le_flat(l, n, w, g, gw), L.subst(Nat, z => {Nat.is_le(z, n) == True{} : Bool}, Nat.mul(SC.length(U32, DI.ws(w)), 32n), SC.length(Bool, ST.flat(DI.ws(w))), Equal.sym(Nat, SC.length(Bool, ST.flat(DI.ws(w))), Nat.mul(SC.length(U32, DI.ws(w)), 32n), len_flat(l, n, w, g, gw)), N.not_lt_le(n, Nat.mul(SC.length(U32, DI.ws(w)), 32n), d)))

def n_eq32(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}, +d: {Nat.is_lt(n, Nat.mul(SC.length(U32, DI.ws(w)), 32n)) == False{} : Bool}) -> {n == Nat.mul(SC.length(U32, DI.ws(w)), 32n) : Nat}:
  Equal.trans(Nat, n, SC.length(Bool, ST.flat(DI.ws(w))), Nat.mul(SC.length(U32, DI.ws(w)), 32n), n_eq(l, n, w, g, gw, d), len_flat(l, n, w, g, gw))

def room_lsh(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}, r: Bool, +er: {Nat.is_lt(SC.length(U32, DI.ws(w)), SC.pow2(DI.lim(w))) == r : Bool}) -> {Nat.is_lt(SC.length(U32, DI.ws(DI.lsh(w, gw))), SC.pow2(DI.lim(DI.lsh(w, gw)))) == r : Bool}:
  %Equal.sym(List<&2, U32>, DI.ws(DI.lsh(w, gw)), DI.ws(w), DI.len_ws(w, gw)) : {Nat.is_lt(SC.length(U32, _), SC.pow2(DI.lim(DI.lsh(w, gw)))) == r : Bool}
  %Equal.sym(Nat, DI.lim(DI.lsh(w, gw)), DI.lim(w), DI.len_lim(w, gw)) : {Nat.is_lt(SC.length(U32, DI.ws(w)), SC.pow2(_)) == r : Bool}
  er

def ws_new(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}, +v: Bool, +hr: {Nat.is_lt(SC.length(U32, DI.ws(w)), SC.pow2(DI.lim(w))) == True{} : Bool}) -> {DI.ws(DI.psh(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n))) == SC.snoc(U32, DI.ws(w), B.word_put(v, 0, 0n)) : List<&2, U32>}:
  %Equal.sym(List<&2, U32>, DI.ws(DI.psh(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n))), SC.snoc(U32, DI.ws(DI.lsh(w, gw)), B.word_put(v, 0, 0n)), DI.push_ws(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n), room_lsh(l, n, w, g, gw, True{}, hr))) : {_ == SC.snoc(U32, DI.ws(w), B.word_put(v, 0, 0n)) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, DI.ws(DI.lsh(w, gw)), DI.ws(w), DI.len_ws(w, gw)) : {SC.snoc(U32, _, B.word_put(v, 0, 0n)) == SC.snoc(U32, DI.ws(w), B.word_put(v, 0, 0n)) : List<&2, U32>}
  {==}

def lim_new(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}, +v: Bool, +hr: {Nat.is_lt(SC.length(U32, DI.ws(w)), SC.pow2(DI.lim(w))) == True{} : Bool}) -> {DI.lim(DI.psh(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n))) == DI.lim(w) : Nat}:
  Equal.trans(Nat, DI.lim(DI.psh(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n))), DI.lim(DI.lsh(w, gw)), DI.lim(w), DI.push_lim(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n), room_lsh(l, n, w, g, gw, True{}, hr)), DI.len_lim(w, gw))

def ws_full(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}, +v: Bool, +hr: {Nat.is_lt(SC.length(U32, DI.ws(w)), SC.pow2(DI.lim(w))) == False{} : Bool}) -> {DI.ws(DI.psh(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n))) == DI.ws(w) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, DI.ws(DI.psh(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n))), DI.ws(DI.lsh(w, gw)), DI.ws(w), DI.full_ws(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n), room_lsh(l, n, w, g, gw, False{}, hr)), DI.len_ws(w, gw))

def lim_full(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}, +v: Bool, +hr: {Nat.is_lt(SC.length(U32, DI.ws(w)), SC.pow2(DI.lim(w))) == False{} : Bool}) -> {DI.lim(DI.psh(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n))) == DI.lim(w) : Nat}:
  Equal.trans(Nat, DI.lim(DI.psh(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n))), DI.lim(DI.lsh(w, gw)), DI.lim(w), DI.full_lim(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n), room_lsh(l, n, w, g, gw, False{}, hr)), DI.len_lim(w, gw))

def nlt_mul32(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == False{} : Bool}) -> {Nat.is_lt(Nat.mul(a, 32n), Nat.mul(b, 32n)) == False{} : Bool}:
  N.le_not_lt(Nat.mul(a, 32n), Nat.mul(b, 32n), AT.mul_le(b, a, 32n, N.not_lt_le(a, b, h)))

def new_real(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}, +v: Bool, r: Bool, +er: {Nat.is_lt(SC.length(U32, DI.ws(w)), SC.pow2(DI.lim(w))) == r : Bool}) -> {BLI.push_new(l, n, D.push(U32, DAS.real(U32, DI.lsh(w, gw)), B.word_put(v, 0, 0n))) == BLI.push_new(l, n, (DAS.real(U32, DI.psh(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n))), DI.ununit(DTR.so_obs(U32, DI.lsh(w, gw), DE.Push{B.word_put(v, 0, 0n)}, DSP.step_ok(U32, DI.lsh(w, gw), DE.Push{B.word_put(v, 0, 0n)}, DI.len_good(w, gw)))))) : BLI.Bitlist & Result<&2, &2, E.Error, Unit>}:
  %Equal.sym(D.DynArray<&2, U32> & Result<&2, &2, DE.Error, Unit>, D.push(U32, DAS.real(U32, DI.lsh(w, gw)), B.word_put(v, 0, 0n)), (DAS.real(U32, DI.psh(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n))), DI.ununit(DTR.so_obs(U32, DI.lsh(w, gw), DE.Push{B.word_put(v, 0, 0n)}, DSP.step_ok(U32, DI.lsh(w, gw), DE.Push{B.word_put(v, 0, 0n)}, DI.len_good(w, gw))))), DI.push_eq(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n))) : {BLI.push_new(l, n, _) == BLI.push_new(l, n, (DAS.real(U32, DI.psh(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n))), DI.ununit(DTR.so_obs(U32, DI.lsh(w, gw), DE.Push{B.word_put(v, 0, 0n)}, DSP.step_ok(U32, DI.lsh(w, gw), DE.Push{B.word_put(v, 0, 0n)}, DI.len_good(w, gw)))))) : BLI.Bitlist & Result<&2, &2, E.Error, Unit>}
  {==}

def push_new_case(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}, +v: Bool, +d: {Nat.is_lt(n, Nat.mul(SC.length(U32, DI.ws(w)), 32n)) == False{} : Bool}, +hb: {BLI.below(l, n) == True{} : Bool}, r: Bool, +er: {Nat.is_lt(SC.length(U32, DI.ws(w)), SC.pow2(DI.lim(w))) == r : Bool}) -> StepOK(SS.BSh{l, n, w}, E.Push{v}):
  match r:
    case True{}:
      +hn = L.subst(Nat, z => {Nat.is_lt(z, Nat.mul(SC.pow2(DI.lim(w)), 32n)) == True{} : Bool}, Nat.mul(SC.length(U32, DI.ws(w)), 32n), n, Equal.sym(Nat, n, Nat.mul(SC.length(U32, DI.ws(w)), 32n), n_eq32(l, n, w, g, gw, d)), BT.lt_mul32(SC.length(U32, DI.ws(w)), SC.pow2(DI.lim(w)), er))
      +hs = sp_push_t(l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n), v, n, ST.length_abs(n, ST.flat(DI.ws(w)), SS.g_inv(l, n, w, g)), Equal.trans(Bool, S.below(l, n), BLI.below(l, n), True{}, Equal.sym(Bool, BLI.below(l, n), S.below(l, n), BT.below_eq(l, n)), hb), hn)
      +gi = L.subst(Nat, z => {ST.invf(1n+z, ST.flat(SC.snoc(U32, DI.ws(w), B.word_put(v, 0, 0n)))) == True{} : Bool}, SC.length(Bool, ST.flat(DI.ws(w))), n, Equal.sym(Nat, n, SC.length(Bool, ST.flat(DI.ws(w))), n_eq(l, n, w, g, gw, d)), BT.push_new_inv(DI.ws(w), v))
      +ma = L.subst(Nat, z => {SC.take(Bool, ST.flat(SC.snoc(U32, DI.ws(w), B.word_put(v, 0, 0n))), 1n+z) == SC.snoc(Bool, SC.take(Bool, ST.flat(DI.ws(w)), z), v) : List<&2, Bool>}, SC.length(Bool, ST.flat(DI.ws(w))), n, Equal.sym(Nat, n, SC.length(Bool, ST.flat(DI.ws(w))), n_eq(l, n, w, g, gw, d)), BT.push_new_abs(DI.ws(w), v))
      (SS.BSh{l, 1n+n, DI.psh(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n))}, (E.OUnit{Done{Unit{}}},
        (%Equal.sym(Bool, BLI.below(l, n), True{}, hb) : {BLI.obs_unit(BLI.push_if(_, l, n, DAS.real(U32, w), v)) == (SS.real(SS.BSh{l, 1n+n, DI.psh(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n))}), E.OUnit{Done{Unit{}}}) : BLI.Bitlist & E.Obs}
         %Equal.sym(BLI.Bitlist & Result<&2, &2, E.Error, Unit>, BLI.push_room(l, n, v, D.length(U32, DAS.real(U32, w))), BLI.push_where(Nat.is_lt(n, Nat.mul(SC.length(U32, DI.ws(w)), 32n)), l, n, DAS.real(U32, DI.lsh(w, gw)), v), push_len(l, n, w, g, gw, v)) : {BLI.obs_unit(_) == (SS.real(SS.BSh{l, 1n+n, DI.psh(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n))}), E.OUnit{Done{Unit{}}}) : BLI.Bitlist & E.Obs}
         %Equal.sym(Bool, Nat.is_lt(n, Nat.mul(SC.length(U32, DI.ws(w)), 32n)), False{}, d) : {BLI.obs_unit(BLI.push_where(_, l, n, DAS.real(U32, DI.lsh(w, gw)), v)) == (SS.real(SS.BSh{l, 1n+n, DI.psh(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n))}), E.OUnit{Done{Unit{}}}) : BLI.Bitlist & E.Obs}
         %Equal.sym(BLI.Bitlist & Result<&2, &2, E.Error, Unit>, BLI.push_new(l, n, D.push(U32, DAS.real(U32, DI.lsh(w, gw)), B.word_put(v, 0, 0n))), BLI.push_new(l, n, (DAS.real(U32, DI.psh(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n))), DI.ununit(DTR.so_obs(U32, DI.lsh(w, gw), DE.Push{B.word_put(v, 0, 0n)}, DSP.step_ok(U32, DI.lsh(w, gw), DE.Push{B.word_put(v, 0, 0n)}, DI.len_good(w, gw)))))), new_real(l, n, w, g, gw, v, True{}, er)) : {BLI.obs_unit(_) == (SS.real(SS.BSh{l, 1n+n, DI.psh(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n))}), E.OUnit{Done{Unit{}}}) : BLI.Bitlist & E.Obs}
         %Equal.sym(Result<&2, &2, DE.Error, Unit>, DI.ununit(DTR.so_obs(U32, DI.lsh(w, gw), DE.Push{B.word_put(v, 0, 0n)}, DSP.step_ok(U32, DI.lsh(w, gw), DE.Push{B.word_put(v, 0, 0n)}, DI.len_good(w, gw)))), Done{Unit{}}, DI.push_val(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n), room_lsh(l, n, w, g, gw, True{}, er))) : {BLI.obs_unit(BLI.push_new(l, n, (DAS.real(U32, DI.psh(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n))), _))) == (SS.real(SS.BSh{l, 1n+n, DI.psh(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n))}), E.OUnit{Done{Unit{}}}) : BLI.Bitlist & E.Obs}
         {==},
        (SS.good_of(l, 1n+n, DI.psh(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n)), SC.snoc(U32, DI.ws(w), B.word_put(v, 0, 0n)), DI.push_good(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n)), ws_new(l, n, w, g, gw, v, er), gi),
         %Equal.sym(S.Model, SS.model(SS.BSh{l, 1n+n, DI.psh(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n))}), S.M{l, DI.lim(w), SC.take(Bool, ST.flat(SC.snoc(U32, DI.ws(w), B.word_put(v, 0, 0n))), 1n+n)}, SS.model_of(l, 1n+n, DI.psh(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n)), SC.snoc(U32, DI.ws(w), B.word_put(v, 0, 0n)), DI.lim(w), ws_new(l, n, w, g, gw, v, er), lim_new(l, n, w, g, gw, v, er))) : {(_, E.OUnit{Done{Unit{}}}) == S.step_parts(l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n), E.Push{v}) : S.Model & E.Obs}
         %Equal.sym(List<&2, Bool>, SC.take(Bool, ST.flat(SC.snoc(U32, DI.ws(w), B.word_put(v, 0, 0n))), 1n+n), SC.snoc(Bool, SC.take(Bool, ST.flat(DI.ws(w)), n), v), ma) : {(S.M{l, DI.lim(w), _}, E.OUnit{Done{Unit{}}}) == S.step_parts(l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n), E.Push{v}) : S.Model & E.Obs}
         Equal.sym(S.Model & E.Obs, S.step_parts(l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n), E.Push{v}), (S.M{l, DI.lim(w), SC.snoc(Bool, SC.take(Bool, ST.flat(DI.ws(w)), n), v)}, E.OUnit{Done{Unit{}}}), hs)))))
    case False{}:
      +hn = L.subst(Nat, z => {Nat.is_lt(z, Nat.mul(SC.pow2(DI.lim(w)), 32n)) == False{} : Bool}, Nat.mul(SC.length(U32, DI.ws(w)), 32n), n, Equal.sym(Nat, n, Nat.mul(SC.length(U32, DI.ws(w)), 32n), n_eq32(l, n, w, g, gw, d)), nlt_mul32(SC.length(U32, DI.ws(w)), SC.pow2(DI.lim(w)), er))
      +hs = sp_push_fc(l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n), v, n, ST.length_abs(n, ST.flat(DI.ws(w)), SS.g_inv(l, n, w, g)), Equal.trans(Bool, S.below(l, n), BLI.below(l, n), True{}, Equal.sym(Bool, BLI.below(l, n), S.below(l, n), BT.below_eq(l, n)), hb), hn)
      (SS.BSh{l, n, DI.psh(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n))}, (E.OUnit{Fail{E.Full{}}},
        (%Equal.sym(Bool, BLI.below(l, n), True{}, hb) : {BLI.obs_unit(BLI.push_if(_, l, n, DAS.real(U32, w), v)) == (SS.real(SS.BSh{l, n, DI.psh(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n))}), E.OUnit{Fail{E.Full{}}}) : BLI.Bitlist & E.Obs}
         %Equal.sym(BLI.Bitlist & Result<&2, &2, E.Error, Unit>, BLI.push_room(l, n, v, D.length(U32, DAS.real(U32, w))), BLI.push_where(Nat.is_lt(n, Nat.mul(SC.length(U32, DI.ws(w)), 32n)), l, n, DAS.real(U32, DI.lsh(w, gw)), v), push_len(l, n, w, g, gw, v)) : {BLI.obs_unit(_) == (SS.real(SS.BSh{l, n, DI.psh(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n))}), E.OUnit{Fail{E.Full{}}}) : BLI.Bitlist & E.Obs}
         %Equal.sym(Bool, Nat.is_lt(n, Nat.mul(SC.length(U32, DI.ws(w)), 32n)), False{}, d) : {BLI.obs_unit(BLI.push_where(_, l, n, DAS.real(U32, DI.lsh(w, gw)), v)) == (SS.real(SS.BSh{l, n, DI.psh(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n))}), E.OUnit{Fail{E.Full{}}}) : BLI.Bitlist & E.Obs}
         %Equal.sym(BLI.Bitlist & Result<&2, &2, E.Error, Unit>, BLI.push_new(l, n, D.push(U32, DAS.real(U32, DI.lsh(w, gw)), B.word_put(v, 0, 0n))), BLI.push_new(l, n, (DAS.real(U32, DI.psh(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n))), DI.ununit(DTR.so_obs(U32, DI.lsh(w, gw), DE.Push{B.word_put(v, 0, 0n)}, DSP.step_ok(U32, DI.lsh(w, gw), DE.Push{B.word_put(v, 0, 0n)}, DI.len_good(w, gw)))))), new_real(l, n, w, g, gw, v, False{}, er)) : {BLI.obs_unit(_) == (SS.real(SS.BSh{l, n, DI.psh(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n))}), E.OUnit{Fail{E.Full{}}}) : BLI.Bitlist & E.Obs}
         %Equal.sym(Result<&2, &2, DE.Error, Unit>, DI.ununit(DTR.so_obs(U32, DI.lsh(w, gw), DE.Push{B.word_put(v, 0, 0n)}, DSP.step_ok(U32, DI.lsh(w, gw), DE.Push{B.word_put(v, 0, 0n)}, DI.len_good(w, gw)))), Fail{DE.CapacityExceeded{}}, DI.full_val(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n), room_lsh(l, n, w, g, gw, False{}, er))) : {BLI.obs_unit(BLI.push_new(l, n, (DAS.real(U32, DI.psh(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n))), _))) == (SS.real(SS.BSh{l, n, DI.psh(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n))}), E.OUnit{Fail{E.Full{}}}) : BLI.Bitlist & E.Obs}
         {==},
        (SS.good_of(l, n, DI.psh(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n)), DI.ws(w), DI.push_good(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n)), ws_full(l, n, w, g, gw, v, er), SS.g_inv(l, n, w, g)),
         %Equal.sym(S.Model, SS.model(SS.BSh{l, n, DI.psh(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n))}), S.M{l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n)}, SS.model_of(l, n, DI.psh(DI.lsh(w, gw), DI.len_good(w, gw), B.word_put(v, 0, 0n)), DI.ws(w), DI.lim(w), ws_full(l, n, w, g, gw, v, er), lim_full(l, n, w, g, gw, v, er))) : {(_, E.OUnit{Fail{E.Full{}}}) == S.step_parts(l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n), E.Push{v}) : S.Model & E.Obs}
         Equal.sym(S.Model & E.Obs, S.step_parts(l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n), E.Push{v}), (S.M{l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n)}, E.OUnit{Fail{E.Full{}}}), hs)))))

def push_room_case(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}, +v: Bool, +hb: {BLI.below(l, n) == True{} : Bool}, d: Bool, +ed: {Nat.is_lt(n, Nat.mul(SC.length(U32, DI.ws(w)), 32n)) == d : Bool}) -> StepOK(SS.BSh{l, n, w}, E.Push{v}):
  match d:
    case True{}:
      push_in_case(l, n, w, g, gw, v, ed, hb)
    case False{}:
      push_new_case(l, n, w, g, gw, v, ed, hb, Nat.is_lt(SC.length(U32, DI.ws(w)), SC.pow2(DI.lim(w))), {==})

def push_case(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}, +v: Bool, c: Bool, +ec: {BLI.below(l, n) == c : Bool}) -> StepOK(SS.BSh{l, n, w}, E.Push{v}):
  match c:
    case True{}:
      push_room_case(l, n, w, g, gw, v, ec, Nat.is_lt(n, Nat.mul(SC.length(U32, DI.ws(w)), 32n)), {==})
    case False{}:
      +hs = sp_push_fl(l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n), v, n, ST.length_abs(n, ST.flat(DI.ws(w)), SS.g_inv(l, n, w, g)), Equal.trans(Bool, S.below(l, n), BLI.below(l, n), False{}, Equal.sym(Bool, BLI.below(l, n), S.below(l, n), BT.below_eq(l, n)), ec))
      (SS.BSh{l, n, w}, (E.OUnit{Fail{E.Full{}}},
        (%Equal.sym(Bool, BLI.below(l, n), False{}, ec) : {BLI.obs_unit(BLI.push_if(_, l, n, DAS.real(U32, w), v)) == (SS.real(SS.BSh{l, n, w}), E.OUnit{Fail{E.Full{}}}) : BLI.Bitlist & E.Obs}
         {==},
        (g, Equal.sym(S.Model & E.Obs, S.step_parts(l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n), E.Push{v}), (S.M{l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n)}, E.OUnit{Fail{E.Full{}}}), hs)))))

# ---- pop ----


def pop_read(+l: Maybe<&2, Nat>, +m: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, 1n+m, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}) -> {BLI.pop_at(l, 1n+m, DAS.real(U32, w)) == BLI.pop_bit(l, m, DAS.real(U32, DI.gsh(w, gw, B.wordix(m))), WK.nthw(DI.ws(w), B.wordix(m)), B.word_get(WK.nthw(DI.ws(w), B.wordix(m)), B.bitix(m))) : BLI.Bitlist & Result<&2, &2, E.Error, Bool>}:
  %Equal.sym(D.DynArray<&2, U32> & Result<&2, &2, DE.Error, U32>, D.get(U32, DAS.real(U32, w), B.wordix(m)), (DAS.real(U32, DI.gsh(w, gw, B.wordix(m))), DI.unitem(DTR.so_obs(U32, w, DE.Get{B.wordix(m)}, DSP.step_ok(U32, w, DE.Get{B.wordix(m)}, gw)))), DI.get_eq(w, gw, B.wordix(m))) : {BLI.pop_word(l, m, _) == BLI.pop_bit(l, m, DAS.real(U32, DI.gsh(w, gw, B.wordix(m))), WK.nthw(DI.ws(w), B.wordix(m)), B.word_get(WK.nthw(DI.ws(w), B.wordix(m)), B.bitix(m))) : BLI.Bitlist & Result<&2, &2, E.Error, Bool>}
  %Equal.sym(Result<&2, &2, DE.Error, U32>, DI.unitem(DTR.so_obs(U32, w, DE.Get{B.wordix(m)}, DSP.step_ok(U32, w, DE.Get{B.wordix(m)}, gw))), DS.item_result(U32, SC.nth(U32, DI.ws(w), B.wordix(m))), DI.get_val(w, gw, B.wordix(m))) : {BLI.pop_word(l, m, (DAS.real(U32, DI.gsh(w, gw, B.wordix(m))), _)) == BLI.pop_bit(l, m, DAS.real(U32, DI.gsh(w, gw, B.wordix(m))), WK.nthw(DI.ws(w), B.wordix(m)), B.word_get(WK.nthw(DI.ws(w), B.wordix(m)), B.bitix(m))) : BLI.Bitlist & Result<&2, &2, E.Error, Bool>}
  %Equal.sym(Maybe<&2, U32>, SC.nth(U32, DI.ws(w), B.wordix(m)), Some{WK.nthw(DI.ws(w), B.wordix(m))}, WK.nthw_nth(DI.ws(w), B.wordix(m), wq(l, 1n+m, w, g, gw, m, in_flat(l, 1n+m, w, g, gw, m, N.lt_succ(m))))) : {BLI.pop_word(l, m, (DAS.real(U32, DI.gsh(w, gw, B.wordix(m))), DS.item_result(U32, _))) == BLI.pop_bit(l, m, DAS.real(U32, DI.gsh(w, gw, B.wordix(m))), WK.nthw(DI.ws(w), B.wordix(m)), B.word_get(WK.nthw(DI.ws(w), B.wordix(m)), B.bitix(m))) : BLI.Bitlist & Result<&2, &2, E.Error, Bool>}
  {==}

# the last stored bit of the list is bit m of F
def last_nth(+l: Maybe<&2, Nat>, +m: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, 1n+m, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}) -> {SC.nth(Bool, ST.flat(DI.ws(w)), m) == Some{B.word_get(WK.nthw(DI.ws(w), B.wordix(m)), B.bitix(m))} : Maybe<&2, Bool>}:
  Equal.trans(Maybe<&2, Bool>, SC.nth(Bool, ST.flat(DI.ws(w)), m), SC.nth(Bool, SC.take(Bool, ST.flat(DI.ws(w)), 1n+m), m), Some{B.word_get(WK.nthw(DI.ws(w), B.wordix(m)), B.bitix(m))},
    Equal.sym(Maybe<&2, Bool>, SC.nth(Bool, SC.take(Bool, ST.flat(DI.ws(w)), 1n+m), m), SC.nth(Bool, ST.flat(DI.ws(w)), m), BL.nth_take(ST.flat(DI.ws(w)), 1n+m, m, N.lt_succ(m))),
    Equal.sym(Maybe<&2, Bool>, Some{B.word_get(WK.nthw(DI.ws(w), B.wordix(m)), B.bitix(m))}, SC.nth(Bool, SC.take(Bool, ST.flat(DI.ws(w)), 1n+m), m), get_bit(l, 1n+m, w, g, gw, m, N.lt_succ(m))))

def last_is(+l: Maybe<&2, Nat>, +m: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, 1n+m, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}, b: Bool, +eb: {B.word_get(WK.nthw(DI.ws(w), B.wordix(m)), B.bitix(m)) == b : Bool}) -> {SC.nth(Bool, ST.flat(DI.ws(w)), m) == Some{b} : Maybe<&2, Bool>}:
  L.subst(Bool, z => {SC.nth(Bool, ST.flat(DI.ws(w)), m) == Some{z} : Maybe<&2, Bool>}, B.word_get(WK.nthw(DI.ws(w), B.wordix(m)), B.bitix(m)), b, eb, last_nth(l, m, w, g, gw))

def pop_bit_case(+l: Maybe<&2, Nat>, +m: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, 1n+m, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}, b: Bool, +eb: {B.word_get(WK.nthw(DI.ws(w), B.wordix(m)), B.bitix(m)) == b : Bool}) -> StepOK(SS.BSh{l, 1n+m, w}, E.Pop{}):
  match b:
    case False{}:
      +hz = last_is(l, m, w, g, gw, False{}, eb)
      (SS.BSh{l, m, DI.gsh(w, gw, B.wordix(m))}, (E.OBit{Done{False{}}},
        (%Equal.sym(BLI.Bitlist & Result<&2, &2, E.Error, Bool>, BLI.pop_at(l, 1n+m, DAS.real(U32, w)), BLI.pop_bit(l, m, DAS.real(U32, DI.gsh(w, gw, B.wordix(m))), WK.nthw(DI.ws(w), B.wordix(m)), B.word_get(WK.nthw(DI.ws(w), B.wordix(m)), B.bitix(m))), pop_read(l, m, w, g, gw)) : {BLI.obs_bit(_) == (SS.real(SS.BSh{l, m, DI.gsh(w, gw, B.wordix(m))}), E.OBit{Done{False{}}}) : BLI.Bitlist & E.Obs}
         %Equal.sym(Bool, B.word_get(WK.nthw(DI.ws(w), B.wordix(m)), B.bitix(m)), False{}, eb) : {BLI.obs_bit(BLI.pop_bit(l, m, DAS.real(U32, DI.gsh(w, gw, B.wordix(m))), WK.nthw(DI.ws(w), B.wordix(m)), _)) == (SS.real(SS.BSh{l, m, DI.gsh(w, gw, B.wordix(m))}), E.OBit{Done{False{}}}) : BLI.Bitlist & E.Obs}
         {==},
        (SS.good_of(l, m, DI.gsh(w, gw, B.wordix(m)), DI.ws(w), DI.get_good(w, gw, B.wordix(m)), DI.get_ws(w, gw, B.wordix(m)), BT.pop_keep_inv(m, ST.flat(DI.ws(w)), SS.g_inv(l, 1n+m, w, g), hz)),
         %Equal.sym(S.Model, SS.model(SS.BSh{l, m, DI.gsh(w, gw, B.wordix(m))}), S.M{l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), m)}, SS.model_of(l, m, DI.gsh(w, gw, B.wordix(m)), DI.ws(w), DI.lim(w), DI.get_ws(w, gw, B.wordix(m)), DI.get_lim(w, gw, B.wordix(m)))) : {(_, E.OBit{Done{False{}}}) == S.pop(l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), 1n+m)) : S.Model & E.Obs}
         %Equal.sym(List<&2, Bool>, SC.take(Bool, ST.flat(DI.ws(w)), 1n+m), SC.snoc(Bool, SC.take(Bool, ST.flat(DI.ws(w)), m), False{}), LX.take_succ(Bool, ST.flat(DI.ws(w)), m, False{}, hz)) : {(S.M{l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), m)}, E.OBit{Done{False{}}}) == S.pop(l, DI.lim(w), _) : S.Model & E.Obs}
         Equal.sym(S.Model & E.Obs, S.pop(l, DI.lim(w), SC.snoc(Bool, SC.take(Bool, ST.flat(DI.ws(w)), m), False{})), (S.M{l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), m)}, E.OBit{Done{False{}}}), BT.pop_spec(l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), m), False{}))))))
    case True{}:
      +ho = last_is(l, m, w, g, gw, True{}, eb)
      +hq = q_in2(l, 1n+m, w, g, gw, m, N.lt_succ(m))
      +ew = Equal.trans(List<&2, U32>, DI.ws(DI.ssh(DI.gsh(w, gw, B.wordix(m)), DI.get_good(w, gw, B.wordix(m)), B.wordix(m), B.word_put(False{}, WK.nthw(DI.ws(w), B.wordix(m)), B.bitix(m)))), MD.put_walk(DI.ws(w), m, False{}), MD.put_walk(DI.ws(w), m, False{}), ws2(l, 1n+m, w, g, gw, m, False{}, N.lt_succ(m)), {==})
      +gi = L.subst(List<&2, Bool>, z => {ST.invf(m, z) == True{} : Bool}, SC.update(Bool, ST.flat(DI.ws(w)), m, False{}), ST.flat(MD.put_walk(DI.ws(w), m, False{})), Equal.sym(List<&2, Bool>, ST.flat(MD.put_walk(DI.ws(w), m, False{})), SC.update(Bool, ST.flat(DI.ws(w)), m, False{}), ST.put_walk(DI.ws(w), m, False{})), BT.pop_clear_inv(m, ST.flat(DI.ws(w)), SS.g_inv(l, 1n+m, w, g)))
      (SS.BSh{l, m, DI.ssh(DI.gsh(w, gw, B.wordix(m)), DI.get_good(w, gw, B.wordix(m)), B.wordix(m), B.word_put(False{}, WK.nthw(DI.ws(w), B.wordix(m)), B.bitix(m)))}, (E.OBit{Done{True{}}},
        (%Equal.sym(BLI.Bitlist & Result<&2, &2, E.Error, Bool>, BLI.pop_at(l, 1n+m, DAS.real(U32, w)), BLI.pop_bit(l, m, DAS.real(U32, DI.gsh(w, gw, B.wordix(m))), WK.nthw(DI.ws(w), B.wordix(m)), B.word_get(WK.nthw(DI.ws(w), B.wordix(m)), B.bitix(m))), pop_read(l, m, w, g, gw)) : {BLI.obs_bit(_) == (SS.real(SS.BSh{l, m, DI.ssh(DI.gsh(w, gw, B.wordix(m)), DI.get_good(w, gw, B.wordix(m)), B.wordix(m), B.word_put(False{}, WK.nthw(DI.ws(w), B.wordix(m)), B.bitix(m)))}), E.OBit{Done{True{}}}) : BLI.Bitlist & E.Obs}
         %Equal.sym(Bool, B.word_get(WK.nthw(DI.ws(w), B.wordix(m)), B.bitix(m)), True{}, eb) : {BLI.obs_bit(BLI.pop_bit(l, m, DAS.real(U32, DI.gsh(w, gw, B.wordix(m))), WK.nthw(DI.ws(w), B.wordix(m)), _)) == (SS.real(SS.BSh{l, m, DI.ssh(DI.gsh(w, gw, B.wordix(m)), DI.get_good(w, gw, B.wordix(m)), B.wordix(m), B.word_put(False{}, WK.nthw(DI.ws(w), B.wordix(m)), B.bitix(m)))}), E.OBit{Done{True{}}}) : BLI.Bitlist & E.Obs}
         %Equal.sym(D.DynArray<&2, U32> & Result<&2, &2, DE.Error, Unit>, D.set(U32, DAS.real(U32, DI.gsh(w, gw, B.wordix(m))), B.wordix(m), B.word_put(False{}, WK.nthw(DI.ws(w), B.wordix(m)), B.bitix(m))), (DAS.real(U32, DI.ssh(DI.gsh(w, gw, B.wordix(m)), DI.get_good(w, gw, B.wordix(m)), B.wordix(m), B.word_put(False{}, WK.nthw(DI.ws(w), B.wordix(m)), B.bitix(m)))), DI.ununit(DTR.so_obs(U32, DI.gsh(w, gw, B.wordix(m)), DE.Set{B.wordix(m), B.word_put(False{}, WK.nthw(DI.ws(w), B.wordix(m)), B.bitix(m))}, DSP.step_ok(U32, DI.gsh(w, gw, B.wordix(m)), DE.Set{B.wordix(m), B.word_put(False{}, WK.nthw(DI.ws(w), B.wordix(m)), B.bitix(m))}, DI.get_good(w, gw, B.wordix(m)))))), DI.set_eq(DI.gsh(w, gw, B.wordix(m)), DI.get_good(w, gw, B.wordix(m)), B.wordix(m), B.word_put(False{}, WK.nthw(DI.ws(w), B.wordix(m)), B.bitix(m)))) : {BLI.obs_bit(BLI.pop_set(l, m, _)) == (SS.real(SS.BSh{l, m, DI.ssh(DI.gsh(w, gw, B.wordix(m)), DI.get_good(w, gw, B.wordix(m)), B.wordix(m), B.word_put(False{}, WK.nthw(DI.ws(w), B.wordix(m)), B.bitix(m)))}), E.OBit{Done{True{}}}) : BLI.Bitlist & E.Obs}
         %Equal.sym(Result<&2, &2, DE.Error, Unit>, DI.ununit(DTR.so_obs(U32, DI.gsh(w, gw, B.wordix(m)), DE.Set{B.wordix(m), B.word_put(False{}, WK.nthw(DI.ws(w), B.wordix(m)), B.bitix(m))}, DSP.step_ok(U32, DI.gsh(w, gw, B.wordix(m)), DE.Set{B.wordix(m), B.word_put(False{}, WK.nthw(DI.ws(w), B.wordix(m)), B.bitix(m))}, DI.get_good(w, gw, B.wordix(m))))), Done{Unit{}}, DI.set_val(DI.gsh(w, gw, B.wordix(m)), DI.get_good(w, gw, B.wordix(m)), B.wordix(m), B.word_put(False{}, WK.nthw(DI.ws(w), B.wordix(m)), B.bitix(m)), hq)) : {BLI.obs_bit(BLI.pop_set(l, m, (DAS.real(U32, DI.ssh(DI.gsh(w, gw, B.wordix(m)), DI.get_good(w, gw, B.wordix(m)), B.wordix(m), B.word_put(False{}, WK.nthw(DI.ws(w), B.wordix(m)), B.bitix(m)))), _))) == (SS.real(SS.BSh{l, m, DI.ssh(DI.gsh(w, gw, B.wordix(m)), DI.get_good(w, gw, B.wordix(m)), B.wordix(m), B.word_put(False{}, WK.nthw(DI.ws(w), B.wordix(m)), B.bitix(m)))}), E.OBit{Done{True{}}}) : BLI.Bitlist & E.Obs}
         {==},
        (SS.good_of(l, m, DI.ssh(DI.gsh(w, gw, B.wordix(m)), DI.get_good(w, gw, B.wordix(m)), B.wordix(m), B.word_put(False{}, WK.nthw(DI.ws(w), B.wordix(m)), B.bitix(m))), MD.put_walk(DI.ws(w), m, False{}), DI.set_good(DI.gsh(w, gw, B.wordix(m)), DI.get_good(w, gw, B.wordix(m)), B.wordix(m), B.word_put(False{}, WK.nthw(DI.ws(w), B.wordix(m)), B.bitix(m))), ew, gi),
         %Equal.sym(S.Model, SS.model(SS.BSh{l, m, DI.ssh(DI.gsh(w, gw, B.wordix(m)), DI.get_good(w, gw, B.wordix(m)), B.wordix(m), B.word_put(False{}, WK.nthw(DI.ws(w), B.wordix(m)), B.bitix(m)))}), S.M{l, DI.lim(w), SC.take(Bool, ST.flat(MD.put_walk(DI.ws(w), m, False{})), m)}, SS.model_of(l, m, DI.ssh(DI.gsh(w, gw, B.wordix(m)), DI.get_good(w, gw, B.wordix(m)), B.wordix(m), B.word_put(False{}, WK.nthw(DI.ws(w), B.wordix(m)), B.bitix(m))), MD.put_walk(DI.ws(w), m, False{}), DI.lim(w), ew, lim2(l, 1n+m, w, g, gw, m, False{}, N.lt_succ(m)))) : {(_, E.OBit{Done{True{}}}) == S.pop(l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), 1n+m)) : S.Model & E.Obs}
         %Equal.sym(List<&2, Bool>, ST.flat(MD.put_walk(DI.ws(w), m, False{})), SC.update(Bool, ST.flat(DI.ws(w)), m, False{}), ST.put_walk(DI.ws(w), m, False{})) : {(S.M{l, DI.lim(w), SC.take(Bool, _, m)}, E.OBit{Done{True{}}}) == S.pop(l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), 1n+m)) : S.Model & E.Obs}
         %Equal.sym(List<&2, Bool>, SC.take(Bool, SC.update(Bool, ST.flat(DI.ws(w)), m, False{}), m), SC.take(Bool, ST.flat(DI.ws(w)), m), LX.take_update(Bool, ST.flat(DI.ws(w)), m, False{})) : {(S.M{l, DI.lim(w), _}, E.OBit{Done{True{}}}) == S.pop(l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), 1n+m)) : S.Model & E.Obs}
         %Equal.sym(List<&2, Bool>, SC.take(Bool, ST.flat(DI.ws(w)), 1n+m), SC.snoc(Bool, SC.take(Bool, ST.flat(DI.ws(w)), m), True{}), LX.take_succ(Bool, ST.flat(DI.ws(w)), m, True{}, ho)) : {(S.M{l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), m)}, E.OBit{Done{True{}}}) == S.pop(l, DI.lim(w), _) : S.Model & E.Obs}
         Equal.sym(S.Model & E.Obs, S.pop(l, DI.lim(w), SC.snoc(Bool, SC.take(Bool, ST.flat(DI.ws(w)), m), True{})), (S.M{l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), m)}, E.OBit{Done{True{}}}), BT.pop_spec(l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), m), True{}))))))

def pop_case(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}) -> StepOK(SS.BSh{l, n, w}, E.Pop{}):
  match n:
    case 0n:
      (SS.BSh{l, 0n, w}, (E.OBit{Fail{E.Empty{}}}, ({==}, (g,
        %Equal.sym(List<&2, Bool>, SC.take(Bool, ST.flat(DI.ws(w)), 0n), Nil{}, LL.sc_take_zero(Bool, ST.flat(DI.ws(w)))) : {(S.M{l, DI.lim(w), _}, E.OBit{Fail{E.Empty{}}}) == S.pop(l, DI.lim(w), _) : S.Model & E.Obs}
        {==}))))
    case 1n+ +m:
      pop_bit_case(l, m, w, g, gw, B.word_get(WK.nthw(DI.ws(w), B.wordix(m)), B.bitix(m)), {==})

# ---- clear ----


def clear_ok(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}) -> StepOK(SS.BSh{l, n, w}, E.Clear{}):
  (SS.BSh{l, 0n, DI.csh(w, gw)}, (E.OUnit{Done{Unit{}}},
    (%Equal.sym(D.DynArray<&2, U32>, D.clear(U32, DAS.real(U32, w)), DAS.real(U32, DI.csh(w, gw)), DI.clear_eq(w, gw)) : {(BLI.BL{l, 0n, _}, E.OUnit{Done{Unit{}}}) == (SS.real(SS.BSh{l, 0n, DI.csh(w, gw)}), E.OUnit{Done{Unit{}}}) : BLI.Bitlist & E.Obs}
     {==},
    (SS.good_of(l, 0n, DI.csh(w, gw), Nil{}, DI.clear_good(w, gw), DI.clear_ws(w, gw), {==}),
     %Equal.sym(S.Model, SS.model(SS.BSh{l, 0n, DI.csh(w, gw)}), S.M{l, DI.lim(w), SC.take(Bool, ST.flat(Nil{}), 0n)}, SS.model_of(l, 0n, DI.csh(w, gw), Nil{}, DI.lim(w), DI.clear_ws(w, gw), DI.clear_lim(w, gw))) : {(_, E.OUnit{Done{Unit{}}}) == (S.M{l, DI.lim(w), Nil{}}, E.OUnit{Done{Unit{}}}) : S.Model & E.Obs}
     {==}))))

# ---- count ----


def cw_all(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}) -> {MD.count_words(SC.take(U32, SC.drop(U32, DI.ws(w), 0n), SC.length(U32, DI.ws(w)))) == S.count(SC.take(Bool, ST.flat(DI.ws(w)), n)) : Nat}:
  %Equal.sym(List<&2, U32>, SC.drop(U32, DI.ws(w), 0n), DI.ws(w), LX.drop_zero(U32, DI.ws(w))) : {MD.count_words(SC.take(U32, _, SC.length(U32, DI.ws(w)))) == S.count(SC.take(Bool, ST.flat(DI.ws(w)), n)) : Nat}
  %Equal.sym(List<&2, U32>, SC.take(U32, DI.ws(w), SC.length(U32, DI.ws(w))), DI.ws(w), LX.take_all(U32, DI.ws(w))) : {MD.count_words(_) == S.count(SC.take(Bool, ST.flat(DI.ws(w)), n)) : Nat}
  %Equal.sym(Nat, MD.count_words(DI.ws(w)), S.count(ST.flat(DI.ws(w))), ST.count_words(DI.ws(w))) : {_ == S.count(SC.take(Bool, ST.flat(DI.ws(w)), n)) : Nat}
  BSS.count_abs(n, ST.flat(DI.ws(w)), SS.g_inv(l, n, w, g))

def count_read(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}) -> {BLI.count_len(l, n, D.length(U32, DAS.real(U32, w))) == BLI.count_fin(l, n, BLI.count_go(SC.length(U32, DI.ws(w)), (DAS.real(U32, DI.lsh(w, gw)), 0n), 0n)) : BLI.Bitlist & Nat}:
  %Equal.sym(D.DynArray<&2, U32> & Nat, D.length(U32, DAS.real(U32, w)), (DAS.real(U32, DI.lsh(w, gw)), DI.unnat(DTR.so_obs(U32, w, DE.Length{}, DSP.step_ok(U32, w, DE.Length{}, gw)))), DI.len_eq(w, gw)) : {BLI.count_len(l, n, _) == BLI.count_fin(l, n, BLI.count_go(SC.length(U32, DI.ws(w)), (DAS.real(U32, DI.lsh(w, gw)), 0n), 0n)) : BLI.Bitlist & Nat}
  %Equal.sym(Nat, DI.unnat(DTR.so_obs(U32, w, DE.Length{}, DSP.step_ok(U32, w, DE.Length{}, gw))), SC.length(U32, DI.ws(w)), DI.len_val(w, gw)) : {BLI.count_len(l, n, (DAS.real(U32, DI.lsh(w, gw)), _)) == BLI.count_fin(l, n, BLI.count_go(SC.length(U32, DI.ws(w)), (DAS.real(U32, DI.lsh(w, gw)), 0n), 0n)) : BLI.Bitlist & Nat}
  {==}

def count_done2(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}, +s2: DAS.Shadow<U32>, e2: {BLI.count_go(SC.length(U32, DI.ws(w)), (DAS.real(U32, DI.lsh(w, gw)), 0n), 0n) == (DAS.real(U32, s2), Nat.add(0n, MD.count_words(SC.take(U32, SC.drop(U32, DI.ws(w), 0n), SC.length(U32, DI.ws(w)))))) : D.DynArray<&2, U32> & Nat}, +g2: {DAS.good(U32, s2) == True{} : Bool}, +wx: {DI.ws(s2) == DI.ws(w) : List<&2, U32>}, +f2: {DI.lim(s2) == DI.lim(w) : Nat}) -> StepOK(SS.BSh{l, n, w}, E.Count{}):
  (SS.BSh{l, n, s2}, (E.ONat{MD.count_words(SC.take(U32, SC.drop(U32, DI.ws(w), 0n), SC.length(U32, DI.ws(w))))},
    (%Equal.sym(BLI.Bitlist & Nat, BLI.count_len(l, n, D.length(U32, DAS.real(U32, w))), BLI.count_fin(l, n, BLI.count_go(SC.length(U32, DI.ws(w)), (DAS.real(U32, DI.lsh(w, gw)), 0n), 0n)), count_read(l, n, w, g, gw)) : {BLI.obs_nat(_) == (SS.real(SS.BSh{l, n, s2}), E.ONat{MD.count_words(SC.take(U32, SC.drop(U32, DI.ws(w), 0n), SC.length(U32, DI.ws(w))))}) : BLI.Bitlist & E.Obs}
     %Equal.sym(D.DynArray<&2, U32> & Nat, BLI.count_go(SC.length(U32, DI.ws(w)), (DAS.real(U32, DI.lsh(w, gw)), 0n), 0n), (DAS.real(U32, s2), MD.count_words(SC.take(U32, SC.drop(U32, DI.ws(w), 0n), SC.length(U32, DI.ws(w))))), e2) : {BLI.obs_nat(BLI.count_fin(l, n, _)) == (SS.real(SS.BSh{l, n, s2}), E.ONat{MD.count_words(SC.take(U32, SC.drop(U32, DI.ws(w), 0n), SC.length(U32, DI.ws(w))))}) : BLI.Bitlist & E.Obs}
     {==},
    (SS.good_of(l, n, s2, DI.ws(w), g2, wx, SS.g_inv(l, n, w, g)),
     %Equal.sym(S.Model, SS.model(SS.BSh{l, n, s2}), S.M{l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n)}, SS.model_of(l, n, s2, DI.ws(w), DI.lim(w), wx, f2)) : {(_, E.ONat{MD.count_words(SC.take(U32, SC.drop(U32, DI.ws(w), 0n), SC.length(U32, DI.ws(w))))}) == (S.M{l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n)}, E.ONat{S.count(SC.take(Bool, ST.flat(DI.ws(w)), n))}) : S.Model & E.Obs}
     %Equal.sym(Nat, MD.count_words(SC.take(U32, SC.drop(U32, DI.ws(w), 0n), SC.length(U32, DI.ws(w)))), S.count(SC.take(Bool, ST.flat(DI.ws(w)), n)), cw_all(l, n, w, g, gw)) : {(S.M{l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n)}, E.ONat{_}) == (S.M{l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n)}, E.ONat{S.count(SC.take(Bool, ST.flat(DI.ws(w)), n))}) : S.Model & E.Obs}
     {==}))))

def count_done(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}, ih: LP.CountOK(SC.length(U32, DI.ws(w)), DI.lsh(w, gw), 0n, 0n, DI.ws(w), DI.lim(w))) -> StepOK(SS.BSh{l, n, w}, E.Count{}):
  match ih:
    case Tuple{s2, Tuple{e2, Tuple{g2, Tuple{w2, f2}}}}:
      count_done2(l, n, w, g, gw, s2, e2, g2, w2, f2)

def count_ok(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}) -> StepOK(SS.BSh{l, n, w}, E.Count{}):
  count_done(l, n, w, g, gw, LP.count_loop(SC.length(U32, DI.ws(w)), DI.lsh(w, gw), DI.len_good(w, gw), DI.ws(w), DI.lim(w), DI.len_ws(w, gw), DI.len_lim(w, gw), 0n, 0n))

# ---- to_list ----


def tk0(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}) -> {SC.take(Bool, ST.flat(SC.drop(U32, DI.ws(w), 0n)), Nat.sub(n, 0n)) == SC.take(Bool, ST.flat(DI.ws(w)), n) : List<&2, Bool>}:
  %Equal.sym(List<&2, U32>, SC.drop(U32, DI.ws(w), 0n), DI.ws(w), LX.drop_zero(U32, DI.ws(w))) : {SC.take(Bool, ST.flat(_), Nat.sub(n, 0n)) == SC.take(Bool, ST.flat(DI.ws(w)), n) : List<&2, Bool>}
  %Equal.sym(Nat, Nat.sub(n, 0n), n, N.sub_zero(n)) : {SC.take(Bool, ST.flat(DI.ws(w)), _) == SC.take(Bool, ST.flat(DI.ws(w)), n) : List<&2, Bool>}
  {==}

def tkk(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}) -> {Nil{} == SC.take(Bool, ST.flat(SC.drop(U32, DI.ws(w), SC.length(U32, DI.ws(w)))), Nat.sub(n, Nat.mul(SC.length(U32, DI.ws(w)), 32n))) : List<&2, Bool>}:
  %Equal.sym(List<&2, U32>, SC.drop(U32, DI.ws(w), SC.length(U32, DI.ws(w))), Nil{}, LX.drop_all(U32, DI.ws(w))) : {Nil{} == SC.take(Bool, ST.flat(_), Nat.sub(n, Nat.mul(SC.length(U32, DI.ws(w)), 32n))) : List<&2, Bool>}
  {==}

def list_read(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}) -> {BLI.to_list_len(l, n, D.length(U32, DAS.real(U32, w))) == BLI.to_list_fin(l, n, BLI.bits_go(SC.length(U32, DI.ws(w)), (DAS.real(U32, DI.lsh(w, gw)), SC.take(Bool, ST.flat(SC.drop(U32, DI.ws(w), SC.length(U32, DI.ws(w)))), Nat.sub(n, Nat.mul(SC.length(U32, DI.ws(w)), 32n)))), n)) : BLI.Bitlist & List<&2, Bool>}:
  %Equal.sym(D.DynArray<&2, U32> & Nat, D.length(U32, DAS.real(U32, w)), (DAS.real(U32, DI.lsh(w, gw)), DI.unnat(DTR.so_obs(U32, w, DE.Length{}, DSP.step_ok(U32, w, DE.Length{}, gw)))), DI.len_eq(w, gw)) : {BLI.to_list_len(l, n, _) == BLI.to_list_fin(l, n, BLI.bits_go(SC.length(U32, DI.ws(w)), (DAS.real(U32, DI.lsh(w, gw)), SC.take(Bool, ST.flat(SC.drop(U32, DI.ws(w), SC.length(U32, DI.ws(w)))), Nat.sub(n, Nat.mul(SC.length(U32, DI.ws(w)), 32n)))), n)) : BLI.Bitlist & List<&2, Bool>}
  %Equal.sym(Nat, DI.unnat(DTR.so_obs(U32, w, DE.Length{}, DSP.step_ok(U32, w, DE.Length{}, gw))), SC.length(U32, DI.ws(w)), DI.len_val(w, gw)) : {BLI.to_list_len(l, n, (DAS.real(U32, DI.lsh(w, gw)), _)) == BLI.to_list_fin(l, n, BLI.bits_go(SC.length(U32, DI.ws(w)), (DAS.real(U32, DI.lsh(w, gw)), SC.take(Bool, ST.flat(SC.drop(U32, DI.ws(w), SC.length(U32, DI.ws(w)))), Nat.sub(n, Nat.mul(SC.length(U32, DI.ws(w)), 32n)))), n)) : BLI.Bitlist & List<&2, Bool>}
  %Equal.sym(List<&2, Bool>, Nil{}, SC.take(Bool, ST.flat(SC.drop(U32, DI.ws(w), SC.length(U32, DI.ws(w)))), Nat.sub(n, Nat.mul(SC.length(U32, DI.ws(w)), 32n))), tkk(l, n, w, g, gw)) : {BLI.to_list_fin(l, n, BLI.bits_go(SC.length(U32, DI.ws(w)), (DAS.real(U32, DI.lsh(w, gw)), _), n)) == BLI.to_list_fin(l, n, BLI.bits_go(SC.length(U32, DI.ws(w)), (DAS.real(U32, DI.lsh(w, gw)), SC.take(Bool, ST.flat(SC.drop(U32, DI.ws(w), SC.length(U32, DI.ws(w)))), Nat.sub(n, Nat.mul(SC.length(U32, DI.ws(w)), 32n)))), n)) : BLI.Bitlist & List<&2, Bool>}
  {==}

def list_done2(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}, +s2: DAS.Shadow<U32>, e2: {BLI.bits_go(SC.length(U32, DI.ws(w)), (DAS.real(U32, DI.lsh(w, gw)), SC.take(Bool, ST.flat(SC.drop(U32, DI.ws(w), SC.length(U32, DI.ws(w)))), Nat.sub(n, Nat.mul(SC.length(U32, DI.ws(w)), 32n)))), n) == (DAS.real(U32, s2), SC.take(Bool, ST.flat(SC.drop(U32, DI.ws(w), 0n)), Nat.sub(n, 0n))) : D.DynArray<&2, U32> & List<&2, Bool>}, +g2: {DAS.good(U32, s2) == True{} : Bool}, +wx: {DI.ws(s2) == DI.ws(w) : List<&2, U32>}, +f2: {DI.lim(s2) == DI.lim(w) : Nat}) -> StepOK(SS.BSh{l, n, w}, E.ToList{}):
  (SS.BSh{l, n, s2}, (E.OBits{SC.take(Bool, ST.flat(SC.drop(U32, DI.ws(w), 0n)), Nat.sub(n, 0n))},
    (%Equal.sym(BLI.Bitlist & List<&2, Bool>, BLI.to_list_len(l, n, D.length(U32, DAS.real(U32, w))), BLI.to_list_fin(l, n, BLI.bits_go(SC.length(U32, DI.ws(w)), (DAS.real(U32, DI.lsh(w, gw)), SC.take(Bool, ST.flat(SC.drop(U32, DI.ws(w), SC.length(U32, DI.ws(w)))), Nat.sub(n, Nat.mul(SC.length(U32, DI.ws(w)), 32n)))), n)), list_read(l, n, w, g, gw)) : {BLI.obs_bits(_) == (SS.real(SS.BSh{l, n, s2}), E.OBits{SC.take(Bool, ST.flat(SC.drop(U32, DI.ws(w), 0n)), Nat.sub(n, 0n))}) : BLI.Bitlist & E.Obs}
     %Equal.sym(D.DynArray<&2, U32> & List<&2, Bool>, BLI.bits_go(SC.length(U32, DI.ws(w)), (DAS.real(U32, DI.lsh(w, gw)), SC.take(Bool, ST.flat(SC.drop(U32, DI.ws(w), SC.length(U32, DI.ws(w)))), Nat.sub(n, Nat.mul(SC.length(U32, DI.ws(w)), 32n)))), n), (DAS.real(U32, s2), SC.take(Bool, ST.flat(SC.drop(U32, DI.ws(w), 0n)), Nat.sub(n, 0n))), e2) : {BLI.obs_bits(BLI.to_list_fin(l, n, _)) == (SS.real(SS.BSh{l, n, s2}), E.OBits{SC.take(Bool, ST.flat(SC.drop(U32, DI.ws(w), 0n)), Nat.sub(n, 0n))}) : BLI.Bitlist & E.Obs}
     {==},
    (SS.good_of(l, n, s2, DI.ws(w), g2, wx, SS.g_inv(l, n, w, g)),
     %Equal.sym(S.Model, SS.model(SS.BSh{l, n, s2}), S.M{l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n)}, SS.model_of(l, n, s2, DI.ws(w), DI.lim(w), wx, f2)) : {(_, E.OBits{SC.take(Bool, ST.flat(SC.drop(U32, DI.ws(w), 0n)), Nat.sub(n, 0n))}) == (S.M{l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n)}, E.OBits{SC.take(Bool, ST.flat(DI.ws(w)), n)}) : S.Model & E.Obs}
     %Equal.sym(List<&2, Bool>, SC.take(Bool, ST.flat(SC.drop(U32, DI.ws(w), 0n)), Nat.sub(n, 0n)), SC.take(Bool, ST.flat(DI.ws(w)), n), tk0(l, n, w, g, gw)) : {(S.M{l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n)}, E.OBits{_}) == (S.M{l, DI.lim(w), SC.take(Bool, ST.flat(DI.ws(w)), n)}, E.OBits{SC.take(Bool, ST.flat(DI.ws(w)), n)}) : S.Model & E.Obs}
     {==}))))

def list_done(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}, ih: LP.BitsOK(SC.length(U32, DI.ws(w)), DI.lsh(w, gw), n, DI.ws(w), DI.lim(w))) -> StepOK(SS.BSh{l, n, w}, E.ToList{}):
  match ih:
    case Tuple{s2, Tuple{e2, Tuple{g2, Tuple{w2, f2}}}}:
      list_done2(l, n, w, g, gw, s2, e2, g2, w2, f2)

def tolist_ok(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}) -> StepOK(SS.BSh{l, n, w}, E.ToList{}):
  list_done(l, n, w, g, gw, LP.bits_loop(SC.length(U32, DI.ws(w)), DI.lsh(w, gw), DI.len_good(w, gw), DI.ws(w), DI.lim(w), DI.len_ws(w, gw), DI.len_lim(w, gw), n, N.le_refl(SC.length(U32, DI.ws(w)))))

# ---- every operation ----

def step_at(+l: Maybe<&2, Nat>, +n: Nat, +w: DAS.Shadow<U32>, +g: {SS.good(SS.BSh{l, n, w}) == True{} : Bool}, +gw: {DAS.good(U32, w) == True{} : Bool}, +op: E.Op) -> StepOK(SS.BSh{l, n, w}, op):
  match op:
    case E.Length{}:
      length_ok(l, n, w, g, gw)
    case E.Limit{}:
      limit_ok(l, n, w, g, gw)
    case E.Get{+i}:
      get_case(l, n, w, g, gw, i, Nat.is_lt(i, n), {==})
    case E.Assign{+i, +v}:
      assign_case(l, n, w, g, gw, i, v, Nat.is_lt(i, n), {==})
    case E.Push{+v}:
      push_case(l, n, w, g, gw, v, BLI.below(l, n), {==})
    case E.Pop{}:
      pop_case(l, n, w, g, gw)
    case E.Clear{}:
      clear_ok(l, n, w, g, gw)
    case E.Count{}:
      count_ok(l, n, w, g, gw)
    case E.ToList{}:
      tolist_ok(l, n, w, g, gw)

def step_ok(+sh: SS.Sh, +op: E.Op, +g: {SS.good(sh) == True{} : Bool}) -> StepOK(sh, op):
  match sh:
    case SS.BSh{+l, +n, +w}:
      step_at(l, n, w, g, SS.g_w(l, n, w, g), op)
