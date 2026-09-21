import Base
import ../../src/pow2.bend as P2
import ../lib/pow2t.bend as PT
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/array.bend as A
import ../../spec/common.bend as SC
import ../../spec/bitset.bend as S
import ../../src/bitset.bend as B
import ../../types/bitset.bend as E
import ./lists.bend as BL
import ./model.bend as MD
import ./walk.bend as WK
import ./arr.bend as AR
import ./loops.bend as LP
import ./zip.bend as ZP
import ./depth.bend as DP
import ./state.bend as ST

# Every public operation (errors included) refines the spec step and keeps the
# representation invariant; from_bools builds exactly the requested bit
# sequence.
#
# Base.Array is linear, so a step is stated as: the real operation on the
# array of a good shadow produces the array of another good shadow, whose
# model and observation are the spec step of the first shadow's model.

def StepOK(sh: ST.Sh, op: E.Op) -> Type:
  Sigma<&1, &1, ST.Sh, sh2 => Sigma<&1, &1, E.Obs, o => {B.step(ST.real(sh), op) == (ST.real(sh2), o) : B.Bitset & E.Obs} & ({ST.good(sh2) == True{} : Bool} & {(ST.model(sh2), o) == S.step(ST.model(sh), op) : List<&2, Bool> & E.Obs})>>

# ---- shared index facts ----

def n_le_cap(+n: Nat, +d: Nat, +t: A.Tree<B.Wd>, +g: {ST.rep(n, d, t) == True{} : Bool}) -> {Nat.is_le(n, Nat.mul(SC.pow2(d), 32n)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(n, z) == True{} : Bool}, SC.length(Bool, ST.flat(AR.ws(t))), Nat.mul(SC.pow2(d), 32n),
    ST.flat_len(d, t, ST.rep_perfect(n, d, t, g)), ST.inv_le(n, ST.flat(AR.ws(t)), ST.rep_invf(n, d, t, g)))

def wix(+n: Nat, +d: Nat, +t: A.Tree<B.Wd>, +i: Nat, +g: {ST.rep(n, d, t) == True{} : Bool}, +hi: {Nat.is_lt(i, n) == True{} : Bool}) -> {Nat.is_lt(B.wordix(i), SC.pow2(d)) == True{} : Bool}:
  ST.wordix_lt(i, SC.pow2(d), N.lt_le_trans(i, n, Nat.mul(SC.pow2(d), 32n), hi, n_le_cap(n, d, t, g)))

# ---- length ----

def length_ok(+n: Nat, +d: Nat, +t: A.Tree<B.Wd>, +g: {ST.rep(n, d, t) == True{} : Bool}) -> StepOK(ST.Sh{n, d, t}, E.Length{}):
  (ST.Sh{n, d, t}, (E.ONat{n}, ({==}, (g,
    %Equal.sym(Nat, SC.length(Bool, ST.abs(n, t)), n, ST.length_abs(n, ST.flat(AR.ws(t)), ST.rep_invf(n, d, t, g))) : {(ST.abs(n, t), E.ONat{n}) == (ST.abs(n, t), E.ONat{_}) : List<&2, Bool> & E.Obs}
    {==}))))

# ---- get ----

def nth_in(+n: Nat, +ws: List<&2, U32>, +i: Nat, +h: {Nat.is_lt(i, n) == True{} : Bool}, +g: {ST.invf(n, ST.flat(ws)) == True{} : Bool}) -> {Some{MD.get_walk(ws, i)} == SC.nth(Bool, SC.take(Bool, ST.flat(ws), n), i) : Maybe<&2, Bool>}:
  Equal.trans(Maybe<&2, Bool>, Some{MD.get_walk(ws, i)}, SC.nth(Bool, ST.flat(ws), i), SC.nth(Bool, SC.take(Bool, ST.flat(ws), n), i),
    ST.get_walk(ws, i, N.lt_le_trans(i, n, SC.length(Bool, ST.flat(ws)), h, ST.inv_le(n, ST.flat(ws), g))),
    Equal.sym(Maybe<&2, Bool>, SC.nth(Bool, SC.take(Bool, ST.flat(ws), n), i), SC.nth(Bool, ST.flat(ws), i), BL.nth_take(ST.flat(ws), n, i, h)))

def nth_out(+n: Nat, +ws: List<&2, U32>, +i: Nat, +h: {Nat.is_lt(i, n) == False{} : Bool}, +g: {ST.invf(n, ST.flat(ws)) == True{} : Bool}) -> {None{} == SC.nth(Bool, SC.take(Bool, ST.flat(ws), n), i) : Maybe<&2, Bool>}:
  Equal.sym(Maybe<&2, Bool>, SC.nth(Bool, SC.take(Bool, ST.flat(ws), n), i), None{},
    LL.nth_none(Bool, SC.take(Bool, ST.flat(ws), n), i, L.subst(Nat, k => {Nat.is_le(k, i) == True{} : Bool}, n, SC.length(Bool, SC.take(Bool, ST.flat(ws), n)), Equal.sym(Nat, SC.length(Bool, SC.take(Bool, ST.flat(ws), n)), n, ST.length_abs(n, ST.flat(ws), g)), N.not_lt_le(i, n, h))))

def get_case(+n: Nat, +d: Nat, +t: A.Tree<B.Wd>, +i: Nat, b: Bool, +eb: {Nat.is_lt(i, n) == b : Bool}, +g: {ST.rep(n, d, t) == True{} : Bool}) -> StepOK(ST.Sh{n, d, t}, E.Get{i}):
  match b:
    case True{}:
      (ST.Sh{n, d, t}, (E.OBit{Done{MD.get_walk(AR.ws(t), i)}}, (
        %Equal.sym(Bool, Nat.is_lt(i, n), True{}, eb) : {B.obs_bit(B.get_if(_, n, d, A.thaw(B.Wd, t), i)) == (ST.real(ST.Sh{n, d, t}), E.OBit{Done{MD.get_walk(AR.ws(t), i)}}) : B.Bitset & E.Obs}
        %Equal.sym(Array<B.Wd> & U32, B.read(A.thaw(B.Wd, t), d, B.wordix(i)), (A.thaw(B.Wd, t), WK.nthw(AR.ws(t), B.wordix(i))), AR.read_ok(d, t, B.wordix(i), ST.rep_lt(n, d, t, g), wix(n, d, t, i, g, eb), ST.rep_perfect(n, d, t, g))) : {B.obs_bit(B.get_read(_, n, d, B.bitix(i))) == (ST.real(ST.Sh{n, d, t}), E.OBit{Done{MD.get_walk(AR.ws(t), i)}}) : B.Bitset & E.Obs}
        %WK.get_index(AR.ws(t), i) : {(B.BS{n, d, A.thaw(B.Wd, t)}, E.OBit{Done{_}}) == (ST.real(ST.Sh{n, d, t}), E.OBit{Done{MD.get_walk(AR.ws(t), i)}}) : B.Bitset & E.Obs}
        {==},
        (g,
         %nth_in(n, AR.ws(t), i, eb, ST.rep_invf(n, d, t, g)) : {(ST.abs(n, t), E.OBit{Done{MD.get_walk(AR.ws(t), i)}}) == (ST.abs(n, t), E.OBit{S.bit(_)}) : List<&2, Bool> & E.Obs}
         {==}))))
    case False{}:
      (ST.Sh{n, d, t}, (E.OBit{Fail{E.IndexOutOfRange{}}}, (
        %Equal.sym(Bool, Nat.is_lt(i, n), False{}, eb) : {B.obs_bit(B.get_if(_, n, d, A.thaw(B.Wd, t), i)) == (ST.real(ST.Sh{n, d, t}), E.OBit{Fail{E.IndexOutOfRange{}}}) : B.Bitset & E.Obs}
        {==},
        (g,
         %nth_out(n, AR.ws(t), i, eb, ST.rep_invf(n, d, t, g)) : {(ST.abs(n, t), E.OBit{Fail{E.IndexOutOfRange{}}}) == (ST.abs(n, t), E.OBit{S.bit(_)}) : List<&2, Bool> & E.Obs}
         {==}))))

# ---- set / clear ----

def upd_tree(+d: Nat, +t: A.Tree<B.Wd>, +i: Nat, +v: Bool) -> A.Tree<B.Wd>:
  A.upd(B.Wd, d, t, B.wordix(i), B.W{B.word_put(v, WK.nthw(AR.ws(t), B.wordix(i)), B.bitix(i))})

def upd_ws(+n: Nat, +d: Nat, +t: A.Tree<B.Wd>, +i: Nat, +v: Bool, +g: {ST.rep(n, d, t) == True{} : Bool}, +hi: {Nat.is_lt(i, n) == True{} : Bool}) -> {AR.ws(upd_tree(d, t, i, v)) == MD.put_walk(AR.ws(t), i, v) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, AR.ws(upd_tree(d, t, i, v)), SC.update(U32, AR.ws(t), B.wordix(i), B.word_put(v, WK.nthw(AR.ws(t), B.wordix(i)), B.bitix(i))), MD.put_walk(AR.ws(t), i, v),
    AR.ws_upd(d, t, B.wordix(i), B.word_put(v, WK.nthw(AR.ws(t), B.wordix(i)), B.bitix(i)), wix(n, d, t, i, g, hi), ST.rep_perfect(n, d, t, g)),
    Equal.sym(List<&2, U32>, MD.put_walk(AR.ws(t), i, v), SC.update(U32, AR.ws(t), B.wordix(i), B.word_put(v, WK.nthw(AR.ws(t), B.wordix(i)), B.bitix(i))), WK.put_index(AR.ws(t), i, v)))

def upd_rep(+n: Nat, +d: Nat, +t: A.Tree<B.Wd>, +i: Nat, +v: Bool, +g: {ST.rep(n, d, t) == True{} : Bool}, +hi: {Nat.is_lt(i, n) == True{} : Bool}) -> {ST.rep(n, d, upd_tree(d, t, i, v)) == True{} : Bool}:
  ST.rep_mk(n, d, upd_tree(d, t, i, v),
    ST.rep_depth(n, d, t, g),
    AR.upd_perfect(d, t, B.wordix(i), B.word_put(v, WK.nthw(AR.ws(t), B.wordix(i)), B.bitix(i)), ST.rep_perfect(n, d, t, g)),
    L.subst(List<&2, U32>, z => {ST.invf(n, ST.flat(z)) == True{} : Bool}, MD.put_walk(AR.ws(t), i, v), AR.ws(upd_tree(d, t, i, v)),
      Equal.sym(List<&2, U32>, AR.ws(upd_tree(d, t, i, v)), MD.put_walk(AR.ws(t), i, v), upd_ws(n, d, t, i, v, g, hi)),
      ST.put_inv(n, AR.ws(t), i, v, hi, ST.rep_invf(n, d, t, g))))

def upd_abs(+n: Nat, +d: Nat, +t: A.Tree<B.Wd>, +i: Nat, +v: Bool, +g: {ST.rep(n, d, t) == True{} : Bool}, +hi: {Nat.is_lt(i, n) == True{} : Bool}) -> {ST.abs(n, upd_tree(d, t, i, v)) == SC.update(Bool, ST.abs(n, t), i, v) : List<&2, Bool>}:
  L.subst(List<&2, U32>, z => {SC.take(Bool, ST.flat(z), n) == SC.update(Bool, ST.abs(n, t), i, v) : List<&2, Bool>}, MD.put_walk(AR.ws(t), i, v), AR.ws(upd_tree(d, t, i, v)),
    Equal.sym(List<&2, U32>, AR.ws(upd_tree(d, t, i, v)), MD.put_walk(AR.ws(t), i, v), upd_ws(n, d, t, i, v, g, hi)),
    ST.put_abs(n, AR.ws(t), i, v))

def AssignOK(+n: Nat, +d: Nat, +t: A.Tree<B.Wd>, +i: Nat, +v: Bool, b: Bool) -> Type:
  Sigma<&1, &1, ST.Sh, sh2 => Sigma<&1, &1, Result<&2, &2, E.Error, Unit>, x => {B.assign_if(b, n, d, A.thaw(B.Wd, t), i, v) == (ST.real(sh2), x) : B.Bitset & Result<&2, &2, E.Error, Unit>} & ({ST.good(sh2) == True{} : Bool} & {(ST.model(sh2), E.OUnit{x}) == S.assign(ST.abs(n, t), i, v) : List<&2, Bool> & E.Obs})>>

def assign_case(+n: Nat, +d: Nat, +t: A.Tree<B.Wd>, +i: Nat, +v: Bool, b: Bool, +eb: {Nat.is_lt(i, n) == b : Bool}, +g: {ST.rep(n, d, t) == True{} : Bool}) -> AssignOK(n, d, t, i, v, b):
  match b:
    case True{}:
      (ST.Sh{n, d, upd_tree(d, t, i, v)}, (Done{Unit{}}, (
        %Equal.sym(Array<B.Wd> & U32, B.read(A.thaw(B.Wd, t), d, B.wordix(i)), (A.thaw(B.Wd, t), WK.nthw(AR.ws(t), B.wordix(i))), AR.read_ok(d, t, B.wordix(i), ST.rep_lt(n, d, t, g), wix(n, d, t, i, g, eb), ST.rep_perfect(n, d, t, g))) : {B.assign_read(_, n, d, B.wordix(i), B.bitix(i), v) == (ST.real(ST.Sh{n, d, upd_tree(d, t, i, v)}), Done{Unit{}}) : B.Bitset & Result<&2, &2, E.Error, Unit>}
        %Equal.sym(Array<B.Wd>, B.write(A.thaw(B.Wd, t), d, B.wordix(i), B.word_put(v, WK.nthw(AR.ws(t), B.wordix(i)), B.bitix(i))), A.thaw(B.Wd, upd_tree(d, t, i, v)), AR.write_ok(d, t, B.wordix(i), B.word_put(v, WK.nthw(AR.ws(t), B.wordix(i)), B.bitix(i)), ST.rep_lt(n, d, t, g), wix(n, d, t, i, g, eb), ST.rep_perfect(n, d, t, g))) : {(B.BS{n, d, _}, Done{Unit{}}) == (ST.real(ST.Sh{n, d, upd_tree(d, t, i, v)}), Done{Unit{}}) : B.Bitset & Result<&2, &2, E.Error, Unit>}
        {==},
        (upd_rep(n, d, t, i, v, g, eb),
         %nth_in(n, AR.ws(t), i, eb, ST.rep_invf(n, d, t, g)) : {(ST.abs(n, upd_tree(d, t, i, v)), E.OUnit{Done{Unit{}}}) == S.assign_at(_, ST.abs(n, t), i, v) : List<&2, Bool> & E.Obs}
         %Equal.sym(List<&2, Bool>, ST.abs(n, upd_tree(d, t, i, v)), SC.update(Bool, ST.abs(n, t), i, v), upd_abs(n, d, t, i, v, g, eb)) : {(_, E.OUnit{Done{Unit{}}}) == S.assign_at(Some{MD.get_walk(AR.ws(t), i)}, ST.abs(n, t), i, v) : List<&2, Bool> & E.Obs}
         {==}))))
    case False{}:
      (ST.Sh{n, d, t}, (Fail{E.IndexOutOfRange{}}, ({==},
        (g,
         %nth_out(n, AR.ws(t), i, eb, ST.rep_invf(n, d, t, g)) : {(ST.abs(n, t), E.OUnit{Fail{E.IndexOutOfRange{}}}) == S.assign_at(_, ST.abs(n, t), i, v) : List<&2, Bool> & E.Obs}
         {==}))))

# ---- count and enumeration see only the logical bits ----

def count_abs(+n: Nat, +xs: List<&2, Bool>, +g: {ST.invf(n, xs) == True{} : Bool}) -> {S.count(xs) == S.count(SC.take(Bool, xs, n)) : Nat}:
  Equal.trans(Nat, S.count(xs), S.count(SC.append(Bool, SC.take(Bool, xs, n), SC.drop(Bool, xs, n))), S.count(SC.take(Bool, xs, n)),
    Equal.cong(List<&2, Bool>, Nat, z => S.count(z), xs, SC.append(Bool, SC.take(Bool, xs, n), SC.drop(Bool, xs, n)), ST.split(n, xs)),
    %Equal.sym(Nat, S.count(SC.append(Bool, SC.take(Bool, xs, n), SC.drop(Bool, xs, n))), Nat.add(S.count(SC.take(Bool, xs, n)), S.count(SC.drop(Bool, xs, n))), BL.count_append(SC.take(Bool, xs, n), SC.drop(Bool, xs, n))) : {_ == S.count(SC.take(Bool, xs, n)) : Nat}
    %Equal.sym(Nat, S.count(SC.drop(Bool, xs, n)), 0n, BL.count_allf(SC.drop(Bool, xs, n), ST.inv_tail(n, xs, g))) : {Nat.add(S.count(SC.take(Bool, xs, n)), _) == S.count(SC.take(Bool, xs, n)) : Nat}
    N.add_zero(S.count(SC.take(Bool, xs, n))))

def members_abs(+n: Nat, +xs: List<&2, Bool>, +g: {ST.invf(n, xs) == True{} : Bool}) -> {S.members(xs, 0n) == S.members(SC.take(Bool, xs, n), 0n) : List<&2, Nat>}:
  Equal.trans(List<&2, Nat>, S.members(xs, 0n), S.members(SC.append(Bool, SC.take(Bool, xs, n), SC.drop(Bool, xs, n)), 0n), S.members(SC.take(Bool, xs, n), 0n),
    Equal.cong(List<&2, Bool>, List<&2, Nat>, z => S.members(z, 0n), xs, SC.append(Bool, SC.take(Bool, xs, n), SC.drop(Bool, xs, n)), ST.split(n, xs)),
    %Equal.sym(List<&2, Nat>, S.members(SC.append(Bool, SC.take(Bool, xs, n), SC.drop(Bool, xs, n)), 0n), SC.append(Nat, S.members(SC.take(Bool, xs, n), 0n), S.members(SC.drop(Bool, xs, n), Nat.add(SC.length(Bool, SC.take(Bool, xs, n)), 0n))), BL.members_append(SC.take(Bool, xs, n), SC.drop(Bool, xs, n), 0n)) : {_ == S.members(SC.take(Bool, xs, n), 0n) : List<&2, Nat>}
    %Equal.sym(List<&2, Nat>, S.members(SC.drop(Bool, xs, n), Nat.add(SC.length(Bool, SC.take(Bool, xs, n)), 0n)), Nil{}, BL.members_allf(SC.drop(Bool, xs, n), Nat.add(SC.length(Bool, SC.take(Bool, xs, n)), 0n), ST.inv_tail(n, xs, g))) : {SC.append(Nat, S.members(SC.take(Bool, xs, n), 0n), _) == S.members(SC.take(Bool, xs, n), 0n) : List<&2, Nat>}
    LL.append_nil(Nat, S.members(SC.take(Bool, xs, n), 0n)))

def count_ok(+n: Nat, +d: Nat, +t: A.Tree<B.Wd>, +g: {ST.rep(n, d, t) == True{} : Bool}) -> StepOK(ST.Sh{n, d, t}, E.Count{}):
  (ST.Sh{n, d, t}, (E.ONat{MD.count_words(AR.ws(t))}, (
    %Equal.sym(Nat, P2.pow2t(d), SC.pow2(d), PT.same(d)) : {B.obs_nat(B.count_fin(B.count_go(_, (A.thaw(B.Wd, t), 0n), d, 0n), n, d)) == (ST.real(ST.Sh{n, d, t}), E.ONat{MD.count_words(AR.ws(t))}) : B.Bitset & E.Obs}
    %Equal.sym(Array<B.Wd> & Nat, B.count_go(SC.pow2(d), (A.thaw(B.Wd, t), 0n), d, 0n), (A.thaw(B.Wd, t), MD.count_words(AR.ws(t))), LP.count_ok(d, t, ST.rep_lt(n, d, t, g), ST.rep_perfect(n, d, t, g))) : {B.obs_nat(B.count_fin(_, n, d)) == (ST.real(ST.Sh{n, d, t}), E.ONat{MD.count_words(AR.ws(t))}) : B.Bitset & E.Obs}
    {==},
    (g,
     %Equal.sym(Nat, MD.count_words(AR.ws(t)), S.count(ST.flat(AR.ws(t))), ST.count_words(AR.ws(t))) : {(ST.abs(n, t), E.ONat{_}) == (ST.abs(n, t), E.ONat{S.count(ST.abs(n, t))}) : List<&2, Bool> & E.Obs}
     %Equal.sym(Nat, S.count(ST.flat(AR.ws(t))), S.count(ST.abs(n, t)), count_abs(n, ST.flat(AR.ws(t)), ST.rep_invf(n, d, t, g))) : {(ST.abs(n, t), E.ONat{_}) == (ST.abs(n, t), E.ONat{S.count(ST.abs(n, t))}) : List<&2, Bool> & E.Obs}
     {==}))))

def tolist_ok(+n: Nat, +d: Nat, +t: A.Tree<B.Wd>, +g: {ST.rep(n, d, t) == True{} : Bool}) -> StepOK(ST.Sh{n, d, t}, E.ToList{}):
  (ST.Sh{n, d, t}, (E.OList{MD.members_words(AR.ws(t), 0n)}, (
    %Equal.sym(Nat, P2.pow2t(d), SC.pow2(d), PT.same(d)) : {B.obs_list(B.members_fin(B.members_go(_, (A.thaw(B.Wd, t), Nil{}), d), n, d)) == (ST.real(ST.Sh{n, d, t}), E.OList{MD.members_words(AR.ws(t), 0n)}) : B.Bitset & E.Obs}
    %Equal.sym(Array<B.Wd> & List<&2, Nat>, B.members_go(SC.pow2(d), (A.thaw(B.Wd, t), Nil{}), d), (A.thaw(B.Wd, t), MD.members_words(AR.ws(t), 0n)), LP.to_list_ok(d, t, ST.rep_lt(n, d, t, g), ST.rep_perfect(n, d, t, g))) : {B.obs_list(B.members_fin(_, n, d)) == (ST.real(ST.Sh{n, d, t}), E.OList{MD.members_words(AR.ws(t), 0n)}) : B.Bitset & E.Obs}
    {==},
    (g,
     %Equal.sym(List<&2, Nat>, MD.members_words(AR.ws(t), 0n), S.members(ST.flat(AR.ws(t)), 0n), ST.members_words(AR.ws(t), 0n)) : {(ST.abs(n, t), E.OList{_}) == (ST.abs(n, t), E.OList{S.members(ST.abs(n, t), 0n)}) : List<&2, Bool> & E.Obs}
     %Equal.sym(List<&2, Nat>, S.members(ST.flat(AR.ws(t)), 0n), S.members(ST.abs(n, t), 0n), members_abs(n, ST.flat(AR.ws(t)), ST.rep_invf(n, d, t, g))) : {(ST.abs(n, t), E.OList{_}) == (ST.abs(n, t), E.OList{S.members(ST.abs(n, t), 0n)}) : List<&2, Bool> & E.Obs}
     {==}))))

# ---- from_bools builds the requested sequence ----

def ao_sh(-n: Nat, -d: Nat, -t: A.Tree<B.Wd>, -i: Nat, -v: Bool, -b: Bool, r: AssignOK(n, d, t, i, v, b)) -> ST.Sh:
  match r:
    case Tuple{sh2, x}:
      sh2

def ao_res(-n: Nat, -d: Nat, -t: A.Tree<B.Wd>, -i: Nat, -v: Bool, -b: Bool, r: AssignOK(n, d, t, i, v, b)) -> Result<&2, &2, E.Error, Unit>:
  match r:
    case Tuple{sh2, Tuple{x, y}}:
      x

def ao_eq(-n: Nat, -d: Nat, -t: A.Tree<B.Wd>, -i: Nat, -v: Bool, -b: Bool, r: AssignOK(n, d, t, i, v, b)) -> {B.assign_if(b, n, d, A.thaw(B.Wd, t), i, v) == (ST.real(ao_sh(n, d, t, i, v, b, r)), ao_res(n, d, t, i, v, b, r)) : B.Bitset & Result<&2, &2, E.Error, Unit>}:
  match r:
    case Tuple{sh2, Tuple{x, Tuple{e, y}}}:
      e

def ao_good(-n: Nat, -d: Nat, -t: A.Tree<B.Wd>, -i: Nat, -v: Bool, -b: Bool, r: AssignOK(n, d, t, i, v, b)) -> {ST.good(ao_sh(n, d, t, i, v, b, r)) == True{} : Bool}:
  match r:
    case Tuple{sh2, Tuple{x, Tuple{e, Tuple{g, y}}}}:
      g

def ao_spec(-n: Nat, -d: Nat, -t: A.Tree<B.Wd>, -i: Nat, -v: Bool, -b: Bool, r: AssignOK(n, d, t, i, v, b)) -> {(ST.model(ao_sh(n, d, t, i, v, b, r)), E.OUnit{ao_res(n, d, t, i, v, b, r)}) == S.assign(ST.abs(n, t), i, v) : List<&2, Bool> & E.Obs}:
  match r:
    case Tuple{sh2, Tuple{x, Tuple{e, Tuple{g, s}}}}:
      s

def assign_some(+n: Nat, +ws: List<&2, U32>, +i: Nat, +v: Bool, +h: {Nat.is_lt(i, n) == True{} : Bool}, +g: {ST.invf(n, ST.flat(ws)) == True{} : Bool}) -> {S.assign(SC.take(Bool, ST.flat(ws), n), i, v) == (SC.update(Bool, SC.take(Bool, ST.flat(ws), n), i, v), E.OUnit{Done{Unit{}}}) : List<&2, Bool> & E.Obs}:
  %nth_in(n, ws, i, h, g) : {S.assign_at(_, SC.take(Bool, ST.flat(ws), n), i, v) == (SC.update(Bool, SC.take(Bool, ST.flat(ws), n), i, v), E.OUnit{Done{Unit{}}}) : List<&2, Bool> & E.Obs}
  {==}

def lt_add_succ(+a: Nat, +x: Nat) -> {Nat.is_lt(a, Nat.add(a, 1n+x)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(a, 1n+x), 1n+Nat.add(a, x), N.add_succ(a, x)) : {Nat.is_lt(a, _) == True{} : Bool}
  N.le_lt_succ(a, Nat.add(a, x), N.le_add_right(a, x))

def upd_snoc(+p: List<&2, Bool>, +r: List<&2, Bool>, +xs: List<&2, Bool>, +ea: {xs == SC.append(Bool, p, Con{False{}, BL.rep(SC.length(Bool, r))}) : List<&2, Bool>}) -> {SC.update(Bool, xs, SC.length(Bool, p), True{}) == SC.append(Bool, SC.snoc(Bool, p, True{}), BL.rep(SC.length(Bool, r))) : List<&2, Bool>}:
  %Equal.sym(List<&2, Bool>, xs, SC.append(Bool, p, Con{False{}, BL.rep(SC.length(Bool, r))}), ea) : {SC.update(Bool, _, SC.length(Bool, p), True{}) == SC.append(Bool, SC.snoc(Bool, p, True{}), BL.rep(SC.length(Bool, r))) : List<&2, Bool>}
  %Equal.sym(List<&2, Bool>, SC.update(Bool, SC.append(Bool, p, Con{False{}, BL.rep(SC.length(Bool, r))}), SC.length(Bool, p), True{}), SC.append(Bool, p, SC.update(Bool, Con{False{}, BL.rep(SC.length(Bool, r))}, Nat.sub(SC.length(Bool, p), SC.length(Bool, p)), True{})), LL.update_append_right(Bool, p, Con{False{}, BL.rep(SC.length(Bool, r))}, SC.length(Bool, p), True{}, N.le_refl(SC.length(Bool, p)))) : {_ == SC.append(Bool, SC.snoc(Bool, p, True{}), BL.rep(SC.length(Bool, r))) : List<&2, Bool>}
  %Equal.sym(Nat, Nat.sub(SC.length(Bool, p), SC.length(Bool, p)), 0n, N.sub_self(SC.length(Bool, p))) : {SC.append(Bool, p, SC.update(Bool, Con{False{}, BL.rep(SC.length(Bool, r))}, _, True{})) == SC.append(Bool, SC.snoc(Bool, p, True{}), BL.rep(SC.length(Bool, r))) : List<&2, Bool>}
  Equal.sym(List<&2, Bool>, SC.append(Bool, SC.snoc(Bool, p, True{}), BL.rep(SC.length(Bool, r))), SC.append(Bool, p, Con{True{}, BL.rep(SC.length(Bool, r))}), LL.snoc_append_cons(Bool, p, True{}, BL.rep(SC.length(Bool, r))))

# The index the next bit goes to is inside the bitset.
def pick_lt(+n: Nat, +d: Nat, +t: A.Tree<B.Wd>, +p: List<&2, Bool>, +r: List<&2, Bool>, +g: {ST.rep(n, d, t) == True{} : Bool}, +ea: {ST.abs(n, t) == SC.append(Bool, p, Con{False{}, BL.rep(SC.length(Bool, r))}) : List<&2, Bool>}) -> {Nat.is_lt(SC.length(Bool, p), n) == True{} : Bool}:
  +el = Equal.trans(Nat, n, SC.length(Bool, ST.abs(n, t)), SC.length(Bool, SC.append(Bool, p, Con{False{}, BL.rep(SC.length(Bool, r))})),
    Equal.sym(Nat, SC.length(Bool, ST.abs(n, t)), n, ST.length_abs(n, ST.flat(AR.ws(t)), ST.rep_invf(n, d, t, g))),
    Equal.cong(List<&2, Bool>, Nat, z => SC.length(Bool, z), ST.abs(n, t), SC.append(Bool, p, Con{False{}, BL.rep(SC.length(Bool, r))}), ea))
  +el2 = Equal.trans(Nat, n, SC.length(Bool, SC.append(Bool, p, Con{False{}, BL.rep(SC.length(Bool, r))})), Nat.add(SC.length(Bool, p), 1n+SC.length(Bool, BL.rep(SC.length(Bool, r)))), el, LL.length_append(Bool, p, Con{False{}, BL.rep(SC.length(Bool, r))}))
  L.subst(Nat, q => {Nat.is_lt(SC.length(Bool, p), q) == True{} : Bool}, Nat.add(SC.length(Bool, p), 1n+SC.length(Bool, BL.rep(SC.length(Bool, r)))), n, Equal.sym(Nat, n, Nat.add(SC.length(Bool, p), 1n+SC.length(Bool, BL.rep(SC.length(Bool, r)))), el2), lt_add_succ(SC.length(Bool, p), SC.length(Bool, BL.rep(SC.length(Bool, r)))))

def PickOK(b: Bool, sh: ST.Sh, +p: List<&2, Bool>, +r: List<&2, Bool>) -> Type:
  Sigma<&1, &1, ST.Sh, sh2 => {B.fill_pick(b, ST.real(sh), SC.length(Bool, p)) == ST.real(sh2) : B.Bitset} & ({ST.good(sh2) == True{} : Bool} & {ST.model(sh2) == SC.append(Bool, SC.snoc(Bool, p, b), BL.rep(SC.length(Bool, r))) : List<&2, Bool>})>

def fill_drop_id(-s: B.Bitset, x: Result<&2, &2, E.Error, Unit>) -> {B.fill_drop(s, x) == s : B.Bitset}:
  match x:
    case Fail{e}:
      {==}
    case Done{u}:
      {==}

def AC(+n: Nat, +d: Nat, +t: A.Tree<B.Wd>, +p: List<&2, Bool>, +g: {ST.rep(n, d, t) == True{} : Bool}) -> AssignOK(n, d, t, SC.length(Bool, p), True{}, Nat.is_lt(SC.length(Bool, p), n)):
  assign_case(n, d, t, SC.length(Bool, p), True{}, Nat.is_lt(SC.length(Bool, p), n), {==}, g)

def pick_ok(b: Bool, +n: Nat, +d: Nat, +t: A.Tree<B.Wd>, +p: List<&2, Bool>, +r: List<&2, Bool>, +g: {ST.rep(n, d, t) == True{} : Bool}, +ea: {ST.abs(n, t) == SC.append(Bool, p, Con{False{}, BL.rep(SC.length(Bool, r))}) : List<&2, Bool>}) -> PickOK(b, ST.Sh{n, d, t}, p, r):
  match b:
    case True{}:
      +h = pick_lt(n, d, t, p, r, g, ea)
      +sh2 = ao_sh(n, d, t, SC.length(Bool, p), True{}, Nat.is_lt(SC.length(Bool, p), n), AC(n, d, t, p, g))
      +x = ao_res(n, d, t, SC.length(Bool, p), True{}, Nat.is_lt(SC.length(Bool, p), n), AC(n, d, t, p, g))
      +em = Equal.trans(List<&2, Bool> & E.Obs, (ST.model(sh2), E.OUnit{x}), S.assign(ST.abs(n, t), SC.length(Bool, p), True{}), (SC.update(Bool, ST.abs(n, t), SC.length(Bool, p), True{}), E.OUnit{Done{Unit{}}}),
        ao_spec(n, d, t, SC.length(Bool, p), True{}, Nat.is_lt(SC.length(Bool, p), n), AC(n, d, t, p, g)),
        assign_some(n, AR.ws(t), SC.length(Bool, p), True{}, h, ST.rep_invf(n, d, t, g)))
      (sh2, (
        %Equal.sym(B.Bitset & Result<&2, &2, E.Error, Unit>, B.assign_if(Nat.is_lt(SC.length(Bool, p), n), n, d, A.thaw(B.Wd, t), SC.length(Bool, p), True{}), (ST.real(sh2), x), ao_eq(n, d, t, SC.length(Bool, p), True{}, Nat.is_lt(SC.length(Bool, p), n), AC(n, d, t, p, g))) : {B.fill_set(_) == ST.real(sh2) : B.Bitset}
        fill_drop_id(ST.real(sh2), x),
        (ao_good(n, d, t, SC.length(Bool, p), True{}, Nat.is_lt(SC.length(Bool, p), n), AC(n, d, t, p, g)),
         Equal.trans(List<&2, Bool>, ST.model(sh2), SC.update(Bool, ST.abs(n, t), SC.length(Bool, p), True{}), SC.append(Bool, SC.snoc(Bool, p, True{}), BL.rep(SC.length(Bool, r))),
           Equal.cong(List<&2, Bool> & E.Obs, List<&2, Bool>, z => Pair.fst(List<&2, Bool>, E.Obs, z), (ST.model(sh2), E.OUnit{x}), (SC.update(Bool, ST.abs(n, t), SC.length(Bool, p), True{}), E.OUnit{Done{Unit{}}}), em),
           upd_snoc(p, r, ST.abs(n, t), ea)))))
    case False{}:
      (ST.Sh{n, d, t}, ({==},
        (g,
         Equal.trans(List<&2, Bool>, ST.abs(n, t), SC.append(Bool, p, Con{False{}, BL.rep(SC.length(Bool, r))}), SC.append(Bool, SC.snoc(Bool, p, False{}), BL.rep(SC.length(Bool, r))), ea,
           Equal.sym(List<&2, Bool>, SC.append(Bool, SC.snoc(Bool, p, False{}), BL.rep(SC.length(Bool, r))), SC.append(Bool, p, Con{False{}, BL.rep(SC.length(Bool, r))}), LL.snoc_append_cons(Bool, p, False{}, BL.rep(SC.length(Bool, r))))))))

def po_sh(-b: Bool, -sh: ST.Sh, -p: List<&2, Bool>, -r: List<&2, Bool>, z: PickOK(b, sh, p, r)) -> ST.Sh:
  match z:
    case Tuple{sh2, y}:
      sh2

def po_eq(-b: Bool, -sh: ST.Sh, -p: List<&2, Bool>, -r: List<&2, Bool>, z: PickOK(b, sh, p, r)) -> {B.fill_pick(b, ST.real(sh), SC.length(Bool, p)) == ST.real(po_sh(b, sh, p, r, z)) : B.Bitset}:
  match z:
    case Tuple{sh2, Tuple{e, y}}:
      e

def po_good(-b: Bool, -sh: ST.Sh, -p: List<&2, Bool>, -r: List<&2, Bool>, z: PickOK(b, sh, p, r)) -> {ST.good(po_sh(b, sh, p, r, z)) == True{} : Bool}:
  match z:
    case Tuple{sh2, Tuple{e, Tuple{gg, m}}}:
      gg

def po_model(-b: Bool, -sh: ST.Sh, -p: List<&2, Bool>, -r: List<&2, Bool>, z: PickOK(b, sh, p, r)) -> {ST.model(po_sh(b, sh, p, r, z)) == SC.append(Bool, SC.snoc(Bool, p, b), BL.rep(SC.length(Bool, r))) : List<&2, Bool>}:
  match z:
    case Tuple{sh2, Tuple{e, Tuple{gg, m}}}:
      m

def pick_sh(b: Bool, sh: ST.Sh, +p: List<&2, Bool>, +r: List<&2, Bool>, +g: {ST.good(sh) == True{} : Bool}, +ea: {ST.model(sh) == SC.append(Bool, p, Con{False{}, BL.rep(SC.length(Bool, r))}) : List<&2, Bool>}) -> PickOK(b, sh, p, r):
  match sh:
    case ST.Sh{+n, +d, +t}:
      pick_ok(b, n, d, t, p, r, g, ea)

def FillOK(zs: List<&2, Bool>, +p: List<&2, Bool>, sh: ST.Sh) -> Type:
  Sigma<&1, &1, ST.Sh, sh2 => {B.fill(zs, SC.length(Bool, p), ST.real(sh)) == ST.real(sh2) : B.Bitset} & ({ST.good(sh2) == True{} : Bool} & {ST.model(sh2) == SC.append(Bool, p, zs) : List<&2, Bool>})>

def fo_sh(-zs: List<&2, Bool>, -p: List<&2, Bool>, -sh: ST.Sh, z: FillOK(zs, p, sh)) -> ST.Sh:
  match z:
    case Tuple{sh2, y}:
      sh2

def fo_eq(-zs: List<&2, Bool>, -p: List<&2, Bool>, -sh: ST.Sh, z: FillOK(zs, p, sh)) -> {B.fill(zs, SC.length(Bool, p), ST.real(sh)) == ST.real(fo_sh(zs, p, sh, z)) : B.Bitset}:
  match z:
    case Tuple{sh2, Tuple{e, y}}:
      e

def fo_good(-zs: List<&2, Bool>, -p: List<&2, Bool>, -sh: ST.Sh, z: FillOK(zs, p, sh)) -> {ST.good(fo_sh(zs, p, sh, z)) == True{} : Bool}:
  match z:
    case Tuple{sh2, Tuple{e, Tuple{gg, m}}}:
      gg

def fo_model(-zs: List<&2, Bool>, -p: List<&2, Bool>, -sh: ST.Sh, z: FillOK(zs, p, sh)) -> {ST.model(fo_sh(zs, p, sh, z)) == SC.append(Bool, p, zs) : List<&2, Bool>}:
  match z:
    case Tuple{sh2, Tuple{e, Tuple{gg, m}}}:
      m

def fill_ok(zs: List<&2, Bool>, +p: List<&2, Bool>, +sh: ST.Sh, +g: {ST.good(sh) == True{} : Bool}, +ea: {ST.model(sh) == SC.append(Bool, p, BL.rep(SC.length(Bool, zs))) : List<&2, Bool>}) -> FillOK(zs, p, sh):
  match zs:
    case Nil{}:
      (sh, ({==}, (g, ea)))
    case Con{+b, +r}:
      +sh1 = po_sh(b, sh, p, r, pick_sh(b, sh, p, r, g, ea))
      +g1 = po_good(b, sh, p, r, pick_sh(b, sh, p, r, g, ea))
      +ea1 = po_model(b, sh, p, r, pick_sh(b, sh, p, r, g, ea))
      +sh2 = fo_sh(r, SC.snoc(Bool, p, b), sh1, fill_ok(r, SC.snoc(Bool, p, b), sh1, g1, ea1))
      (sh2, (
        %Equal.sym(B.Bitset, B.fill_pick(b, ST.real(sh), SC.length(Bool, p)), ST.real(sh1), po_eq(b, sh, p, r, pick_sh(b, sh, p, r, g, ea))) : {B.fill(r, 1n+SC.length(Bool, p), _) == ST.real(sh2) : B.Bitset}
        %LL.length_snoc(Bool, p, b) : {B.fill(r, _, ST.real(sh1)) == ST.real(sh2) : B.Bitset}
        fo_eq(r, SC.snoc(Bool, p, b), sh1, fill_ok(r, SC.snoc(Bool, p, b), sh1, g1, ea1)),
        (fo_good(r, SC.snoc(Bool, p, b), sh1, fill_ok(r, SC.snoc(Bool, p, b), sh1, g1, ea1)),
         Equal.trans(List<&2, Bool>, ST.model(sh2), SC.append(Bool, SC.snoc(Bool, p, b), r), SC.append(Bool, p, Con{b, r}),
           fo_model(r, SC.snoc(Bool, p, b), sh1, fill_ok(r, SC.snoc(Bool, p, b), sh1, g1, ea1)),
           LL.snoc_append_cons(Bool, p, b, r)))))

def bool_count_len(+ys: List<&2, Bool>) -> {B.bool_count(ys) == SC.length(Bool, ys) : Nat}:
  match ys:
    case Nil{}:
      {==}
    case Con{b, +t}:
      N.succ_cong(B.bool_count(t), SC.length(Bool, t), bool_count_len(t))

def FromOK(ys: List<&2, Bool>) -> Type:
  Sigma<&1, &1, ST.Sh, sh2 => {B.from_bools(ys) == ST.real(sh2) : B.Bitset} & ({ST.good(sh2) == True{} : Bool} & {ST.model(sh2) == ys : List<&2, Bool>})>

def from_ok(+ys: List<&2, Bool>, +hf: {Nat.is_le(B.bool_count(ys), Nat.mul(SC.pow2(B.depth_for(B.bool_count(ys))), 32n)) == True{} : Bool}) -> FromOK(ys):
  +c = B.bool_count(ys)
  +sh0 = {ST.Sh{c, B.depth_for(c), A.trep(B.Wd, B.depth_for(c), B.W{0})} : ST.Sh}
  +ea0 = L.subst(Nat, q => {ST.model(sh0) == BL.rep(q) : List<&2, Bool>}, c, SC.length(Bool, ys), bool_count_len(ys), ST.new_abs(c, hf))
  +sh2 = fo_sh(ys, Nil{}, sh0, fill_ok(ys, Nil{}, sh0, ST.new_rep(c, hf), ea0))
  (sh2, (
    %Equal.sym(B.Bitset, B.new(c), ST.real(sh0), ST.new_form(c)) : {B.fill(ys, 0n, _) == ST.real(sh2) : B.Bitset}
    fo_eq(ys, Nil{}, sh0, fill_ok(ys, Nil{}, sh0, ST.new_rep(c, hf), ea0)),
    (fo_good(ys, Nil{}, sh0, fill_ok(ys, Nil{}, sh0, ST.new_rep(c, hf), ea0)),
     fo_model(ys, Nil{}, sh0, fill_ok(ys, Nil{}, sh0, ST.new_rep(c, hf), ea0)))))

# ---- binary operations ----

def ws_len_eq(+d: Nat, +t: A.Tree<B.Wd>, +tb: A.Tree<B.Wd>, +pa: {A.perfect(B.Wd, d, t) == True{} : Bool}, +pb: {A.perfect(B.Wd, d, tb) == True{} : Bool}) -> {SC.length(U32, AR.ws(tb)) == SC.length(U32, AR.ws(t)) : Nat}:
  Equal.trans(Nat, SC.length(U32, AR.ws(tb)), SC.pow2(d), SC.length(U32, AR.ws(t)),
    AR.ws_length(d, tb, pb),
    Equal.sym(Nat, SC.length(U32, AR.ws(t)), SC.pow2(d), AR.ws_length(d, t, pa)))

def ztz(+k: B.WordOp, +d: Nat, +t: A.Tree<B.Wd>, +tb: A.Tree<B.Wd>) -> A.Tree<B.Wd>:
  ZP.ztree(SC.pow2(d), k, d, t, tb, 0n)

def ws_zip(+k: B.WordOp, +d: Nat, +t: A.Tree<B.Wd>, +tb: A.Tree<B.Wd>, +pa: {A.perfect(B.Wd, d, t) == True{} : Bool}, +pb: {A.perfect(B.Wd, d, tb) == True{} : Bool}) -> {AR.ws(ztz(k, d, t, tb)) == MD.zip_words(k, AR.ws(t), AR.ws(tb)) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, AR.ws(ztz(k, d, t, tb)), ZP.zl(SC.pow2(d), k, 0n, AR.ws(t), AR.ws(tb)), MD.zip_words(k, AR.ws(t), AR.ws(tb)),
    ZP.ztree_ws(SC.pow2(d), k, d, t, tb, 0n, pa, N.le_refl(SC.pow2(d))),
    L.subst(Nat, z => {ZP.zl(z, k, 0n, AR.ws(t), AR.ws(tb)) == MD.zip_words(k, AR.ws(t), AR.ws(tb)) : List<&2, U32>},
      SC.length(U32, AR.ws(t)), SC.pow2(d), AR.ws_length(d, t, pa),
      ZP.zl_full(k, AR.ws(t), AR.ws(tb), ws_len_eq(d, t, tb, pa, pb))))

def zip_flat(+k: B.WordOp, +d: Nat, +t: A.Tree<B.Wd>, +tb: A.Tree<B.Wd>, +pa: {A.perfect(B.Wd, d, t) == True{} : Bool}, +pb: {A.perfect(B.Wd, d, tb) == True{} : Bool}) -> {ST.flat(AR.ws(ztz(k, d, t, tb))) == BL.zipk(k, ST.flat(AR.ws(t)), ST.flat(AR.ws(tb))) : List<&2, Bool>}:
  Equal.trans(List<&2, Bool>, ST.flat(AR.ws(ztz(k, d, t, tb))), ST.flat(MD.zip_words(k, AR.ws(t), AR.ws(tb))), BL.zipk(k, ST.flat(AR.ws(t)), ST.flat(AR.ws(tb))),
    Equal.cong(List<&2, U32>, List<&2, Bool>, ST.flat, AR.ws(ztz(k, d, t, tb)), MD.zip_words(k, AR.ws(t), AR.ws(tb)), ws_zip(k, d, t, tb, pa, pb)),
    ST.zip_words(k, AR.ws(t), AR.ws(tb)))

def zip_rep(+k: B.WordOp, +n: Nat, +d: Nat, +t: A.Tree<B.Wd>, +tb: A.Tree<B.Wd>, +g: {ST.rep(n, d, t) == True{} : Bool}, +gb: {ST.rep(n, d, tb) == True{} : Bool}) -> {ST.rep(n, d, ztz(k, d, t, tb)) == True{} : Bool}:
  ST.rep_mk(n, d, ztz(k, d, t, tb),
    ST.rep_depth(n, d, t, g),
    ZP.ztree_perfect(SC.pow2(d), k, d, t, tb, 0n, ST.rep_perfect(n, d, t, g)),
    L.subst(List<&2, Bool>, z => {ST.invf(n, z) == True{} : Bool}, BL.zipk(k, ST.flat(AR.ws(t)), ST.flat(AR.ws(tb))), ST.flat(AR.ws(ztz(k, d, t, tb))),
      Equal.sym(List<&2, Bool>, ST.flat(AR.ws(ztz(k, d, t, tb))), BL.zipk(k, ST.flat(AR.ws(t)), ST.flat(AR.ws(tb))), zip_flat(k, d, t, tb, ST.rep_perfect(n, d, t, g), ST.rep_perfect(n, d, tb, gb))),
      ST.invf_zipk(k, n, ST.flat(AR.ws(t)), ST.flat(AR.ws(tb)), ST.rep_invf(n, d, t, g), ST.rep_invf(n, d, tb, gb))))

def zip_abs(+k: B.WordOp, +n: Nat, +d: Nat, +t: A.Tree<B.Wd>, +tb: A.Tree<B.Wd>, +pa: {A.perfect(B.Wd, d, t) == True{} : Bool}, +pb: {A.perfect(B.Wd, d, tb) == True{} : Bool}) -> {ST.abs(n, ztz(k, d, t, tb)) == BL.zipk(k, ST.abs(n, t), ST.abs(n, tb)) : List<&2, Bool>}:
  Equal.trans(List<&2, Bool>, SC.take(Bool, ST.flat(AR.ws(ztz(k, d, t, tb))), n), SC.take(Bool, BL.zipk(k, ST.flat(AR.ws(t)), ST.flat(AR.ws(tb))), n), BL.zipk(k, ST.abs(n, t), ST.abs(n, tb)),
    Equal.cong(List<&2, Bool>, List<&2, Bool>, z => SC.take(Bool, z, n), ST.flat(AR.ws(ztz(k, d, t, tb))), BL.zipk(k, ST.flat(AR.ws(t)), ST.flat(AR.ws(tb))), zip_flat(k, d, t, tb, pa, pb)),
    BL.take_zipk(k, ST.flat(AR.ws(t)), ST.flat(AR.ws(tb)), n))

def CombOK(+n: Nat, +d: Nat, +t: A.Tree<B.Wd>, +k: B.WordOp, +ys: List<&2, Bool>, +z: List<&2, Bool>) -> Type:
  Sigma<&1, &1, ST.Sh, sh2 => Sigma<&1, &1, Result<&2, &2, E.Error, Unit>, x => {B.comb_bits(k, ST.real(ST.Sh{n, d, t}), ys) == (ST.real(sh2), x) : B.Bitset & Result<&2, &2, E.Error, Unit>} & ({ST.good(sh2) == True{} : Bool} & {(ST.model(sh2), E.OUnit{x}) == S.combine(ST.abs(n, t), ys, z) : List<&2, Bool> & E.Obs})>>

def comb_at(+k: B.WordOp, +n: Nat, +d: Nat, +t: A.Tree<B.Wd>, +tb: A.Tree<B.Wd>, +ys: List<&2, Bool>, +z: List<&2, Bool>, +ez: {BL.zipk(k, ST.abs(n, t), ys) == z : List<&2, Bool>}, +g: {ST.rep(n, d, t) == True{} : Bool}, +gb: {ST.rep(n, d, tb) == True{} : Bool}, +eab: {ST.abs(n, tb) == ys : List<&2, Bool>}, +etrue: {Nat.is_eq(n, B.bool_count(ys)) == True{} : Bool}, +efb: {B.from_bools(ys) == ST.real(ST.Sh{n, d, tb}) : B.Bitset}) -> CombOK(n, d, t, k, ys, z):
  (ST.Sh{n, d, ztz(k, d, t, tb)}, (Done{Unit{}}, (
    %Equal.sym(Bool, Nat.is_eq(n, B.bool_count(ys)), True{}, etrue) : {B.comb_go(_, k, n, d, A.thaw(B.Wd, t), ys) == (ST.real(ST.Sh{n, d, ztz(k, d, t, tb)}), Done{Unit{}}) : B.Bitset & Result<&2, &2, E.Error, Unit>}
    %Equal.sym(B.Bitset, B.from_bools(ys), ST.real(ST.Sh{n, d, tb}), efb) : {B.drop_right(B.combine(k, B.BS{n, d, A.thaw(B.Wd, t)}, _)) == (ST.real(ST.Sh{n, d, ztz(k, d, t, tb)}), Done{Unit{}}) : B.Bitset & Result<&2, &2, E.Error, Unit>}
    %Equal.sym(Bool, Nat.is_eq(n, n), True{}, N.is_eq_refl(n)) : {B.drop_right(B.combine_if(Bool.and(_, Nat.is_eq(d, d)), k, n, d, A.thaw(B.Wd, t), n, d, A.thaw(B.Wd, tb))) == (ST.real(ST.Sh{n, d, ztz(k, d, t, tb)}), Done{Unit{}}) : B.Bitset & Result<&2, &2, E.Error, Unit>}
    %Equal.sym(Bool, Nat.is_eq(d, d), True{}, N.is_eq_refl(d)) : {B.drop_right(B.combine_if(Bool.and(True{}, _), k, n, d, A.thaw(B.Wd, t), n, d, A.thaw(B.Wd, tb))) == (ST.real(ST.Sh{n, d, ztz(k, d, t, tb)}), Done{Unit{}}) : B.Bitset & Result<&2, &2, E.Error, Unit>}
    %Equal.sym(Nat, P2.pow2t(d), SC.pow2(d), PT.same(d)) : {B.drop_right(B.zip_fin(B.zip_go(_, (A.thaw(B.Wd, t), A.thaw(B.Wd, tb)), k, d, 0n), n, d, n, d)) == (ST.real(ST.Sh{n, d, ztz(k, d, t, tb)}), Done{Unit{}}) : B.Bitset & Result<&2, &2, E.Error, Unit>}
    %Equal.sym(Array<B.Wd> & Array<B.Wd>, B.zip_go(SC.pow2(d), (A.thaw(B.Wd, t), A.thaw(B.Wd, tb)), k, d, 0n), (A.thaw(B.Wd, ztz(k, d, t, tb)), A.thaw(B.Wd, tb)), ZP.zip_go_ok(SC.pow2(d), k, d, t, tb, 0n, ST.rep_lt(n, d, t, g), ST.rep_perfect(n, d, t, g), ST.rep_perfect(n, d, tb, gb), N.le_refl(SC.pow2(d)))) : {B.drop_right(B.zip_fin(_, n, d, n, d)) == (ST.real(ST.Sh{n, d, ztz(k, d, t, tb)}), Done{Unit{}}) : B.Bitset & Result<&2, &2, E.Error, Unit>}
    %Equal.sym(Unit, B.dispose(B.BS{n, d, A.thaw(B.Wd, tb)}), Unit{}, ST.dispose_ok(n, d, tb)) : {B.drop_right_go(B.BS{n, d, A.thaw(B.Wd, ztz(k, d, t, tb))}, _, Done{Unit{}}) == (ST.real(ST.Sh{n, d, ztz(k, d, t, tb)}), Done{Unit{}}) : B.Bitset & Result<&2, &2, E.Error, Unit>}
    {==},
    (zip_rep(k, n, d, t, tb, g, gb),
     %Equal.sym(Nat, SC.length(Bool, ST.abs(n, t)), n, ST.length_abs(n, ST.flat(AR.ws(t)), ST.rep_invf(n, d, t, g))) : {(ST.abs(n, ztz(k, d, t, tb)), E.OUnit{Done{Unit{}}}) == S.combine_if(Nat.is_eq(_, SC.length(Bool, ys)), ST.abs(n, t), z) : List<&2, Bool> & E.Obs}
     %bool_count_len(ys) : {(ST.abs(n, ztz(k, d, t, tb)), E.OUnit{Done{Unit{}}}) == S.combine_if(Nat.is_eq(n, _), ST.abs(n, t), z) : List<&2, Bool> & E.Obs}
     %Equal.sym(Bool, Nat.is_eq(n, B.bool_count(ys)), True{}, etrue) : {(ST.abs(n, ztz(k, d, t, tb)), E.OUnit{Done{Unit{}}}) == S.combine_if(_, ST.abs(n, t), z) : List<&2, Bool> & E.Obs}
     Equal.cong(List<&2, Bool>, List<&2, Bool> & E.Obs, w => (w, E.OUnit{Done{Unit{}}}), ST.abs(n, ztz(k, d, t, tb)), z,
       Equal.trans(List<&2, Bool>, ST.abs(n, ztz(k, d, t, tb)), BL.zipk(k, ST.abs(n, t), ys), z,
         Equal.trans(List<&2, Bool>, ST.abs(n, ztz(k, d, t, tb)), BL.zipk(k, ST.abs(n, t), ST.abs(n, tb)), BL.zipk(k, ST.abs(n, t), ys),
           zip_abs(k, n, d, t, tb, ST.rep_perfect(n, d, t, g), ST.rep_perfect(n, d, tb, gb)),
           Equal.cong(List<&2, Bool>, List<&2, Bool>, w => BL.zipk(k, ST.abs(n, t), w), ST.abs(n, tb), ys, eab)),
         ez))))))

def fr_sh(-ys: List<&2, Bool>, z: FromOK(ys)) -> ST.Sh:
  match z:
    case Tuple{sh2, y}:
      sh2

def fr_eq(-ys: List<&2, Bool>, z: FromOK(ys)) -> {B.from_bools(ys) == ST.real(fr_sh(ys, z)) : B.Bitset}:
  match z:
    case Tuple{sh2, Tuple{e, y}}:
      e

def fr_good(-ys: List<&2, Bool>, z: FromOK(ys)) -> {ST.good(fr_sh(ys, z)) == True{} : Bool}:
  match z:
    case Tuple{sh2, Tuple{e, Tuple{gg, m}}}:
      gg

def fr_model(-ys: List<&2, Bool>, z: FromOK(ys)) -> {ST.model(fr_sh(ys, z)) == ys : List<&2, Bool>}:
  match z:
    case Tuple{sh2, Tuple{e, Tuple{gg, m}}}:
      m

def comb_sh(+k: B.WordOp, +n: Nat, +d: Nat, +t: A.Tree<B.Wd>, shf: ST.Sh, +ys: List<&2, Bool>, +z: List<&2, Bool>, +ez: {BL.zipk(k, ST.abs(n, t), ys) == z : List<&2, Bool>}, +g: {ST.rep(n, d, t) == True{} : Bool}, +gf: {ST.good(shf) == True{} : Bool}, +eaf: {ST.model(shf) == ys : List<&2, Bool>}, +etrue: {Nat.is_eq(n, B.bool_count(ys)) == True{} : Bool}, +efb: {B.from_bools(ys) == ST.real(shf) : B.Bitset}) -> CombOK(n, d, t, k, ys, z):
  match shf:
    case ST.Sh{+m, +e, +tb}:
      +eyn = Equal.trans(Nat, SC.length(Bool, ys), B.bool_count(ys), n,
        Equal.sym(Nat, B.bool_count(ys), SC.length(Bool, ys), bool_count_len(ys)),
        Equal.sym(Nat, n, B.bool_count(ys), N.eq_from_is_eq(n, B.bool_count(ys), etrue)))
      +em = Equal.trans(Nat, m, SC.length(Bool, ys), n,
        Equal.trans(Nat, m, SC.length(Bool, ST.abs(m, tb)), SC.length(Bool, ys),
          Equal.sym(Nat, SC.length(Bool, ST.abs(m, tb)), m, ST.length_abs(m, ST.flat(AR.ws(tb)), ST.rep_invf(m, e, tb, gf))),
          Equal.cong(List<&2, Bool>, Nat, w => SC.length(Bool, w), ST.abs(m, tb), ys, eaf)),
        eyn)
      +ee = Equal.trans(Nat, e, B.depth_for(n), d,
        Equal.trans(Nat, e, B.depth_for(m), B.depth_for(n),
          N.eq_from_is_eq(e, B.depth_for(m), ST.rep_depth(m, e, tb, gf)),
          Equal.cong(Nat, Nat, w => B.depth_for(w), m, n, em)),
        Equal.sym(Nat, d, B.depth_for(n), N.eq_from_is_eq(d, B.depth_for(n), ST.rep_depth(n, d, t, g))))
      comb_at(k, n, d, t, tb, ys, z, ez, g,
        L.subst(Nat, x => {ST.rep(n, x, tb) == True{} : Bool}, e, d, ee,
          L.subst(Nat, x => {ST.rep(x, e, tb) == True{} : Bool}, m, n, em, gf)),
        L.subst(Nat, x => {ST.abs(x, tb) == ys : List<&2, Bool>}, m, n, em, eaf),
        etrue,
        L.subst(Nat, x => {B.from_bools(ys) == ST.real(ST.Sh{n, x, tb}) : B.Bitset}, e, d, ee,
          L.subst(Nat, x => {B.from_bools(ys) == ST.real(ST.Sh{x, e, tb}) : B.Bitset}, m, n, em, efb)))

def comb_false(+k: B.WordOp, +n: Nat, +d: Nat, +t: A.Tree<B.Wd>, +ys: List<&2, Bool>, +z: List<&2, Bool>, +g: {ST.rep(n, d, t) == True{} : Bool}, +efalse: {Nat.is_eq(n, B.bool_count(ys)) == False{} : Bool}) -> CombOK(n, d, t, k, ys, z):
  (ST.Sh{n, d, t}, (Fail{E.LengthMismatch{}}, (
    %Equal.sym(Bool, Nat.is_eq(n, B.bool_count(ys)), False{}, efalse) : {B.comb_go(_, k, n, d, A.thaw(B.Wd, t), ys) == (ST.real(ST.Sh{n, d, t}), Fail{E.LengthMismatch{}}) : B.Bitset & Result<&2, &2, E.Error, Unit>}
    {==},
    (g,
     %Equal.sym(Nat, SC.length(Bool, ST.abs(n, t)), n, ST.length_abs(n, ST.flat(AR.ws(t)), ST.rep_invf(n, d, t, g))) : {(ST.abs(n, t), E.OUnit{Fail{E.LengthMismatch{}}}) == S.combine_if(Nat.is_eq(_, SC.length(Bool, ys)), ST.abs(n, t), z) : List<&2, Bool> & E.Obs}
     %bool_count_len(ys) : {(ST.abs(n, t), E.OUnit{Fail{E.LengthMismatch{}}}) == S.combine_if(Nat.is_eq(n, _), ST.abs(n, t), z) : List<&2, Bool> & E.Obs}
     %Equal.sym(Bool, Nat.is_eq(n, B.bool_count(ys)), False{}, efalse) : {(ST.abs(n, t), E.OUnit{Fail{E.LengthMismatch{}}}) == S.combine_if(_, ST.abs(n, t), z) : List<&2, Bool> & E.Obs}
     {==}))))

def comb_case(+k: B.WordOp, +n: Nat, +d: Nat, +t: A.Tree<B.Wd>, +ys: List<&2, Bool>, +z: List<&2, Bool>, +ez: {BL.zipk(k, ST.abs(n, t), ys) == z : List<&2, Bool>}, +g: {ST.rep(n, d, t) == True{} : Bool}, b: Bool, +eb: {Nat.is_eq(n, B.bool_count(ys)) == b : Bool}) -> CombOK(n, d, t, k, ys, z):
  match b:
    case True{}:
      +hf = L.subst(Nat, x => {Nat.is_le(x, Nat.mul(SC.pow2(B.depth_for(x)), 32n)) == True{} : Bool}, n, B.bool_count(ys), N.eq_from_is_eq(n, B.bool_count(ys), eb), ST.rep_fits(n, d, t, g))
      comb_sh(k, n, d, t, fr_sh(ys, from_ok(ys, hf)), ys, z, ez, g,
        fr_good(ys, from_ok(ys, hf)), fr_model(ys, from_ok(ys, hf)), eb, fr_eq(ys, from_ok(ys, hf)))
    case False{}:
      comb_false(k, n, d, t, ys, z, g, eb)

def co_sh(-n: Nat, -d: Nat, -t: A.Tree<B.Wd>, -k: B.WordOp, -ys: List<&2, Bool>, -z: List<&2, Bool>, c: CombOK(n, d, t, k, ys, z)) -> ST.Sh:
  match c:
    case Tuple{sh2, y}:
      sh2

def co_res(-n: Nat, -d: Nat, -t: A.Tree<B.Wd>, -k: B.WordOp, -ys: List<&2, Bool>, -z: List<&2, Bool>, c: CombOK(n, d, t, k, ys, z)) -> Result<&2, &2, E.Error, Unit>:
  match c:
    case Tuple{sh2, Tuple{x, y}}:
      x

def co_eq(-n: Nat, -d: Nat, -t: A.Tree<B.Wd>, -k: B.WordOp, -ys: List<&2, Bool>, -z: List<&2, Bool>, c: CombOK(n, d, t, k, ys, z)) -> {B.comb_bits(k, ST.real(ST.Sh{n, d, t}), ys) == (ST.real(co_sh(n, d, t, k, ys, z, c)), co_res(n, d, t, k, ys, z, c)) : B.Bitset & Result<&2, &2, E.Error, Unit>}:
  match c:
    case Tuple{sh2, Tuple{x, Tuple{e, y}}}:
      e

def co_good(-n: Nat, -d: Nat, -t: A.Tree<B.Wd>, -k: B.WordOp, -ys: List<&2, Bool>, -z: List<&2, Bool>, c: CombOK(n, d, t, k, ys, z)) -> {ST.good(co_sh(n, d, t, k, ys, z, c)) == True{} : Bool}:
  match c:
    case Tuple{sh2, Tuple{x, Tuple{e, Tuple{gg, s}}}}:
      gg

def co_spec(-n: Nat, -d: Nat, -t: A.Tree<B.Wd>, -k: B.WordOp, -ys: List<&2, Bool>, -z: List<&2, Bool>, c: CombOK(n, d, t, k, ys, z)) -> {(ST.model(co_sh(n, d, t, k, ys, z, c)), E.OUnit{co_res(n, d, t, k, ys, z, c)}) == S.combine(ST.abs(n, t), ys, z) : List<&2, Bool> & E.Obs}:
  match c:
    case Tuple{sh2, Tuple{x, Tuple{e, Tuple{gg, s}}}}:
      s

def CC(+k: B.WordOp, +n: Nat, +d: Nat, +t: A.Tree<B.Wd>, +ys: List<&2, Bool>, +z: List<&2, Bool>, +ez: {BL.zipk(k, ST.abs(n, t), ys) == z : List<&2, Bool>}, +g: {ST.rep(n, d, t) == True{} : Bool}) -> CombOK(n, d, t, k, ys, z):
  comb_case(k, n, d, t, ys, z, ez, g, Nat.is_eq(n, B.bool_count(ys)), {==})

def comb_step(+k: B.WordOp, +n: Nat, +d: Nat, +t: A.Tree<B.Wd>, +ys: List<&2, Bool>, +z: List<&2, Bool>, +ez: {BL.zipk(k, ST.abs(n, t), ys) == z : List<&2, Bool>}, +g: {ST.rep(n, d, t) == True{} : Bool}) -> Sigma<&1, &1, ST.Sh, sh2 => Sigma<&1, &1, E.Obs, o => {B.obs_unit(B.comb_bits(k, ST.real(ST.Sh{n, d, t}), ys)) == (ST.real(sh2), o) : B.Bitset & E.Obs} & ({ST.good(sh2) == True{} : Bool} & {(ST.model(sh2), o) == S.combine(ST.abs(n, t), ys, z) : List<&2, Bool> & E.Obs})>>:
  (co_sh(n, d, t, k, ys, z, CC(k, n, d, t, ys, z, ez, g)), (E.OUnit{co_res(n, d, t, k, ys, z, CC(k, n, d, t, ys, z, ez, g))}, (
    Equal.cong(B.Bitset & Result<&2, &2, E.Error, Unit>, B.Bitset & E.Obs, w => B.obs_unit(w),
      B.comb_bits(k, ST.real(ST.Sh{n, d, t}), ys),
      (ST.real(co_sh(n, d, t, k, ys, z, CC(k, n, d, t, ys, z, ez, g))), co_res(n, d, t, k, ys, z, CC(k, n, d, t, ys, z, ez, g))),
      co_eq(n, d, t, k, ys, z, CC(k, n, d, t, ys, z, ez, g))),
    (co_good(n, d, t, k, ys, z, CC(k, n, d, t, ys, z, ez, g)),
     co_spec(n, d, t, k, ys, z, CC(k, n, d, t, ys, z, ez, g))))))

def assign_step(+n: Nat, +d: Nat, +t: A.Tree<B.Wd>, +i: Nat, +v: Bool, +g: {ST.rep(n, d, t) == True{} : Bool}) -> Sigma<&1, &1, ST.Sh, sh2 => Sigma<&1, &1, E.Obs, o => {B.obs_unit(B.assign(B.BS{n, d, A.thaw(B.Wd, t)}, i, v)) == (ST.real(sh2), o) : B.Bitset & E.Obs} & ({ST.good(sh2) == True{} : Bool} & {(ST.model(sh2), o) == S.assign(ST.abs(n, t), i, v) : List<&2, Bool> & E.Obs})>>:
  (ao_sh(n, d, t, i, v, Nat.is_lt(i, n), assign_case(n, d, t, i, v, Nat.is_lt(i, n), {==}, g)),
   (E.OUnit{ao_res(n, d, t, i, v, Nat.is_lt(i, n), assign_case(n, d, t, i, v, Nat.is_lt(i, n), {==}, g))}, (
     Equal.cong(B.Bitset & Result<&2, &2, E.Error, Unit>, B.Bitset & E.Obs, w => B.obs_unit(w),
       B.assign_if(Nat.is_lt(i, n), n, d, A.thaw(B.Wd, t), i, v),
       (ST.real(ao_sh(n, d, t, i, v, Nat.is_lt(i, n), assign_case(n, d, t, i, v, Nat.is_lt(i, n), {==}, g))), ao_res(n, d, t, i, v, Nat.is_lt(i, n), assign_case(n, d, t, i, v, Nat.is_lt(i, n), {==}, g))),
       ao_eq(n, d, t, i, v, Nat.is_lt(i, n), assign_case(n, d, t, i, v, Nat.is_lt(i, n), {==}, g))),
     (ao_good(n, d, t, i, v, Nat.is_lt(i, n), assign_case(n, d, t, i, v, Nat.is_lt(i, n), {==}, g)),
      ao_spec(n, d, t, i, v, Nat.is_lt(i, n), assign_case(n, d, t, i, v, Nat.is_lt(i, n), {==}, g))))))

# ---- every operation ----

def step_ok(sh: ST.Sh, op: E.Op, +g: {ST.good(sh) == True{} : Bool}) -> StepOK(sh, op):
  match sh op:
    case ST.Sh{+n, +d, +t} E.Length{}:
      length_ok(n, d, t, g)
    case ST.Sh{+n, +d, +t} E.Get{+i}:
      get_case(n, d, t, i, Nat.is_lt(i, n), {==}, g)
    case ST.Sh{+n, +d, +t} E.Set{+i}:
      assign_step(n, d, t, i, True{}, g)
    case ST.Sh{+n, +d, +t} E.Clear{+i}:
      assign_step(n, d, t, i, False{}, g)
    case ST.Sh{+n, +d, +t} E.Count{}:
      count_ok(n, d, t, g)
    case ST.Sh{+n, +d, +t} E.Union{+ys}:
      comb_step(B.KOr{}, n, d, t, ys, S.zip_or(ST.abs(n, t), ys), Equal.sym(List<&2, Bool>, S.zip_or(ST.abs(n, t), ys), BL.zipk(B.KOr{}, ST.abs(n, t), ys), BL.spec_or(ST.abs(n, t), ys)), g)
    case ST.Sh{+n, +d, +t} E.Intersection{+ys}:
      comb_step(B.KAnd{}, n, d, t, ys, S.zip_and(ST.abs(n, t), ys), Equal.sym(List<&2, Bool>, S.zip_and(ST.abs(n, t), ys), BL.zipk(B.KAnd{}, ST.abs(n, t), ys), BL.spec_and(ST.abs(n, t), ys)), g)
    case ST.Sh{+n, +d, +t} E.Difference{+ys}:
      comb_step(B.KDiff{}, n, d, t, ys, S.zip_diff(ST.abs(n, t), ys), Equal.sym(List<&2, Bool>, S.zip_diff(ST.abs(n, t), ys), BL.zipk(B.KDiff{}, ST.abs(n, t), ys), BL.spec_diff(ST.abs(n, t), ys)), g)
    case ST.Sh{+n, +d, +t} E.Xor{+ys}:
      comb_step(B.KXor{}, n, d, t, ys, S.zip_xor(ST.abs(n, t), ys), Equal.sym(List<&2, Bool>, S.zip_xor(ST.abs(n, t), ys), BL.zipk(B.KXor{}, ST.abs(n, t), ys), BL.spec_xor(ST.abs(n, t), ys)), g)
    case ST.Sh{+n, +d, +t} E.ToList{}:
      tolist_ok(n, d, t, g)
