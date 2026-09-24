import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/array.bend as AR
import ../../lib/spec_common.bend as SC
import ../../../src/containers/dynamic_array.bend as D
import ../../../src/containers/types/dynamic_array.bend as DE
import ../dynamic_array/spec.bend as DS
import ../dynamic_array/layout.bend as LY
import ../dynamic_array/state.bend as DAS
import ../dynamic_array/steps.bend as DSP
import ../dynamic_array/trace.bend as DTR

# The word array of a bitlist, used only through the dynamic array's proved
# contract (proofs/containers/dynamic_array: DSP.step_ok / DTR.so_*): each
# operation on the array of a good shadow lands on the array of another good
# shadow, whose model and answer are the dynamic-array spec step. Nothing
# here looks inside the array; only the item list `ws` and the depth limit
# `lim` of the model are used.
# (source: proofs/containers/bitlist/da.src)


def items(m: DS.Model<U32>) -> List<&2, U32>:
  match m:
    case DS.M{l, d, xs}:
      xs

def mlim(m: DS.Model<U32>) -> Nat:
  match m:
    case DS.M{l, d, xs}:
      l

# The stored words and the depth limit of a shadow.
def ws(w: DAS.Shadow<U32>) -> List<&2, U32>:
  items(DAS.model(U32, w))

def lim(w: DAS.Shadow<U32>) -> Nat:
  mlim(DAS.model(U32, w))

def unitem(o: DE.Obs<U32>) -> Result<&2, &2, DE.Error, U32>:
  match o:
    case DE.OItem{x}:
      x
    case DE.ONat{k}:
      Fail{DE.IndexOutOfRange{}}
    case DE.OUnit{r}:
      Fail{DE.IndexOutOfRange{}}
    case DE.OList{xs}:
      Fail{DE.IndexOutOfRange{}}

def ununit(o: DE.Obs<U32>) -> Result<&2, &2, DE.Error, Unit>:
  match o:
    case DE.OItem{x}:
      Fail{DE.IndexOutOfRange{}}
    case DE.ONat{k}:
      Fail{DE.IndexOutOfRange{}}
    case DE.OUnit{r}:
      r
    case DE.OList{xs}:
      Fail{DE.IndexOutOfRange{}}

def unnat(o: DE.Obs<U32>) -> Nat:
  match o:
    case DE.OItem{x}:
      0n
    case DE.ONat{k}:
      k
    case DE.OUnit{r}:
      0n
    case DE.OList{xs}:
      0n

def uitem(p: D.DynArray<&2, U32> & DE.Obs<U32>) -> D.DynArray<&2, U32> & Result<&2, &2, DE.Error, U32>:
  (a, o) = p
  (a, unitem(o))

def uunit(p: D.DynArray<&2, U32> & DE.Obs<U32>) -> D.DynArray<&2, U32> & Result<&2, &2, DE.Error, Unit>:
  (a, o) = p
  (a, ununit(o))

def unat(p: D.DynArray<&2, U32> & DE.Obs<U32>) -> D.DynArray<&2, U32> & Nat:
  (a, o) = p
  (a, unnat(o))

def uitem_obs(r: D.DynArray<&2, U32> & Result<&2, &2, DE.Error, U32>) -> {uitem(D.obs_item(U32, r)) == r : D.DynArray<&2, U32> & Result<&2, &2, DE.Error, U32>}:
  match r:
    case Tuple{a, x}:
      {==}

def uunit_obs(r: D.DynArray<&2, U32> & Result<&2, &2, DE.Error, Unit>) -> {uunit(D.obs_unit(U32, r)) == r : D.DynArray<&2, U32> & Result<&2, &2, DE.Error, Unit>}:
  match r:
    case Tuple{a, x}:
      {==}

def unat_obs(r: D.DynArray<&2, U32> & Nat) -> {unat(D.obs_nat(U32, r)) == r : D.DynArray<&2, U32> & Nat}:
  match r:
    case Tuple{a, x}:
      {==}

# ---- reading the pieces of a spec answer ----

def p_items(+a: DS.Model<U32>, o: DE.Obs<U32>, +b: DS.Model<U32>, o2: DE.Obs<U32>, e: {(a, o) == (b, o2) : DS.Model<U32> & DE.Obs<U32>}) -> {items(a) == items(b) : List<&2, U32>}:
  Equal.cong(DS.Model<U32> & DE.Obs<U32>, List<&2, U32>, p => items(Pair.fst(DS.Model<U32>, DE.Obs<U32>, p)), (a, o), (b, o2), e)

def p_lim(+a: DS.Model<U32>, o: DE.Obs<U32>, +b: DS.Model<U32>, o2: DE.Obs<U32>, e: {(a, o) == (b, o2) : DS.Model<U32> & DE.Obs<U32>}) -> {mlim(a) == mlim(b) : Nat}:
  Equal.cong(DS.Model<U32> & DE.Obs<U32>, Nat, p => mlim(Pair.fst(DS.Model<U32>, DE.Obs<U32>, p)), (a, o), (b, o2), e)

def p_item(+a: DS.Model<U32>, o: DE.Obs<U32>, +b: DS.Model<U32>, o2: DE.Obs<U32>, e: {(a, o) == (b, o2) : DS.Model<U32> & DE.Obs<U32>}) -> {unitem(o) == unitem(o2) : Result<&2, &2, DE.Error, U32>}:
  Equal.cong(DS.Model<U32> & DE.Obs<U32>, Result<&2, &2, DE.Error, U32>, p => unitem(Pair.snd(DS.Model<U32>, DE.Obs<U32>, p)), (a, o), (b, o2), e)

def p_unit(+a: DS.Model<U32>, o: DE.Obs<U32>, +b: DS.Model<U32>, o2: DE.Obs<U32>, e: {(a, o) == (b, o2) : DS.Model<U32> & DE.Obs<U32>}) -> {ununit(o) == ununit(o2) : Result<&2, &2, DE.Error, Unit>}:
  Equal.cong(DS.Model<U32> & DE.Obs<U32>, Result<&2, &2, DE.Error, Unit>, p => ununit(Pair.snd(DS.Model<U32>, DE.Obs<U32>, p)), (a, o), (b, o2), e)

def p_nat(+a: DS.Model<U32>, o: DE.Obs<U32>, +b: DS.Model<U32>, o2: DE.Obs<U32>, e: {(a, o) == (b, o2) : DS.Model<U32> & DE.Obs<U32>}) -> {unnat(o) == unnat(o2) : Nat}:
  Equal.cong(DS.Model<U32> & DE.Obs<U32>, Nat, p => unnat(Pair.snd(DS.Model<U32>, DE.Obs<U32>, p)), (a, o), (b, o2), e)

# ---- facts of a good shadow ----

def ws_len(+l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, U32>>, +g: {DAS.good(U32, DAS.Sh{l, d, n, t}) == True{} : Bool}) -> {SC.length(U32, ws(DAS.Sh{l, d, n, t})) == n : Nat}:
  LY.lay_len(U32, AR.slots(Maybe<&2, U32>, t), n, DAS.g_lay(U32, l, d, n, t, g))

# at most 2^lim words
def ws_cap(+l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, U32>>, +g: {DAS.good(U32, DAS.Sh{l, d, n, t}) == True{} : Bool}) -> {Nat.is_le(SC.length(U32, ws(DAS.Sh{l, d, n, t})), SC.pow2(lim(DAS.Sh{l, d, n, t}))) == True{} : Bool}:
  %Equal.sym(Nat, SC.length(U32, ws(DAS.Sh{l, d, n, t})), n, ws_len(l, d, n, t, g)) : {Nat.is_le(_, SC.pow2(l)) == True{} : Bool}
  N.le_trans(n, SC.pow2(d), SC.pow2(l), DSP.n_le_cap(U32, l, d, n, t, g), N.pow2_mono(d, l, DAS.g_depth(U32, l, d, n, t, g)))

def wcap(+w: DAS.Shadow<U32>, +g: {DAS.good(U32, w) == True{} : Bool}) -> {Nat.is_le(SC.length(U32, ws(w)), SC.pow2(lim(w))) == True{} : Bool}:
  match w:
    case DAS.Sh{+l, +d, +n, +t}:
      ws_cap(l, d, n, t, g)

# ---- get ----

def gsh(+w: DAS.Shadow<U32>, +g: {DAS.good(U32, w) == True{} : Bool}, +q: Nat) -> DAS.Shadow<U32>:
  DTR.so_sh(U32, w, DE.Get{q}, DSP.step_ok(U32, w, DE.Get{q}, g))

def get_eq(+w: DAS.Shadow<U32>, +g: {DAS.good(U32, w) == True{} : Bool}, +q: Nat) -> {D.get(U32, DAS.real(U32, w), q) == (DAS.real(U32, gsh(w, g, q)), unitem(DTR.so_obs(U32, w, DE.Get{q}, DSP.step_ok(U32, w, DE.Get{q}, g)))) : D.DynArray<&2, U32> & Result<&2, &2, DE.Error, U32>}:
  Equal.trans(D.DynArray<&2, U32> & Result<&2, &2, DE.Error, U32>, D.get(U32, DAS.real(U32, w), q), uitem(D.obs_item(U32, D.get(U32, DAS.real(U32, w), q))), (DAS.real(U32, gsh(w, g, q)), unitem(DTR.so_obs(U32, w, DE.Get{q}, DSP.step_ok(U32, w, DE.Get{q}, g)))),
    Equal.sym(D.DynArray<&2, U32> & Result<&2, &2, DE.Error, U32>, uitem(D.obs_item(U32, D.get(U32, DAS.real(U32, w), q))), D.get(U32, DAS.real(U32, w), q), uitem_obs(D.get(U32, DAS.real(U32, w), q))),
    Equal.cong(D.DynArray<&2, U32> & DE.Obs<U32>, D.DynArray<&2, U32> & Result<&2, &2, DE.Error, U32>, p => uitem(p), D.step(U32, DAS.real(U32, w), DE.Get{q}), (DAS.real(U32, DTR.so_sh(U32, w, DE.Get{q}, DSP.step_ok(U32, w, DE.Get{q}, g))), DTR.so_obs(U32, w, DE.Get{q}, DSP.step_ok(U32, w, DE.Get{q}, g))), DTR.so_step(U32, w, DE.Get{q}, DSP.step_ok(U32, w, DE.Get{q}, g))))

def get_good(+w: DAS.Shadow<U32>, +g: {DAS.good(U32, w) == True{} : Bool}, +q: Nat) -> {DAS.good(U32, gsh(w, g, q)) == True{} : Bool}:
  DTR.so_good(U32, w, DE.Get{q}, DSP.step_ok(U32, w, DE.Get{q}, g))

def get_all(+w: DAS.Shadow<U32>, +g: {DAS.good(U32, w) == True{} : Bool}, +q: Nat) -> {(DAS.model(U32, gsh(w, g, q)), DTR.so_obs(U32, w, DE.Get{q}, DSP.step_ok(U32, w, DE.Get{q}, g))) == (DAS.model(U32, w), DE.OItem{DS.item_result(U32, SC.nth(U32, ws(w), q))}) : DS.Model<U32> & DE.Obs<U32>}:
  match w:
    case DAS.Sh{+l, +d, +n, +t}:
      DTR.so_spec(U32, DAS.Sh{l, d, n, t}, DE.Get{q}, DSP.step_ok(U32, DAS.Sh{l, d, n, t}, DE.Get{q}, g))

def get_val(+w: DAS.Shadow<U32>, +g: {DAS.good(U32, w) == True{} : Bool}, +q: Nat) -> {unitem(DTR.so_obs(U32, w, DE.Get{q}, DSP.step_ok(U32, w, DE.Get{q}, g))) == DS.item_result(U32, SC.nth(U32, ws(w), q)) : Result<&2, &2, DE.Error, U32>}:
  p_item(DAS.model(U32, gsh(w, g, q)), DTR.so_obs(U32, w, DE.Get{q}, DSP.step_ok(U32, w, DE.Get{q}, g)), DAS.model(U32, w), DE.OItem{DS.item_result(U32, SC.nth(U32, ws(w), q))}, get_all(w, g, q))

def get_ws(+w: DAS.Shadow<U32>, +g: {DAS.good(U32, w) == True{} : Bool}, +q: Nat) -> {ws(gsh(w, g, q)) == ws(w) : List<&2, U32>}:
  p_items(DAS.model(U32, gsh(w, g, q)), DTR.so_obs(U32, w, DE.Get{q}, DSP.step_ok(U32, w, DE.Get{q}, g)), DAS.model(U32, w), DE.OItem{DS.item_result(U32, SC.nth(U32, ws(w), q))}, get_all(w, g, q))

def get_lim(+w: DAS.Shadow<U32>, +g: {DAS.good(U32, w) == True{} : Bool}, +q: Nat) -> {lim(gsh(w, g, q)) == lim(w) : Nat}:
  p_lim(DAS.model(U32, gsh(w, g, q)), DTR.so_obs(U32, w, DE.Get{q}, DSP.step_ok(U32, w, DE.Get{q}, g)), DAS.model(U32, w), DE.OItem{DS.item_result(U32, SC.nth(U32, ws(w), q))}, get_all(w, g, q))

# ---- length ----

def lsh(+w: DAS.Shadow<U32>, +g: {DAS.good(U32, w) == True{} : Bool}) -> DAS.Shadow<U32>:
  DTR.so_sh(U32, w, DE.Length{}, DSP.step_ok(U32, w, DE.Length{}, g))

def len_eq(+w: DAS.Shadow<U32>, +g: {DAS.good(U32, w) == True{} : Bool}) -> {D.length(U32, DAS.real(U32, w)) == (DAS.real(U32, lsh(w, g)), unnat(DTR.so_obs(U32, w, DE.Length{}, DSP.step_ok(U32, w, DE.Length{}, g)))) : D.DynArray<&2, U32> & Nat}:
  Equal.trans(D.DynArray<&2, U32> & Nat, D.length(U32, DAS.real(U32, w)), unat(D.obs_nat(U32, D.length(U32, DAS.real(U32, w)))), (DAS.real(U32, lsh(w, g)), unnat(DTR.so_obs(U32, w, DE.Length{}, DSP.step_ok(U32, w, DE.Length{}, g)))),
    Equal.sym(D.DynArray<&2, U32> & Nat, unat(D.obs_nat(U32, D.length(U32, DAS.real(U32, w)))), D.length(U32, DAS.real(U32, w)), unat_obs(D.length(U32, DAS.real(U32, w)))),
    Equal.cong(D.DynArray<&2, U32> & DE.Obs<U32>, D.DynArray<&2, U32> & Nat, p => unat(p), D.step(U32, DAS.real(U32, w), DE.Length{}), (DAS.real(U32, DTR.so_sh(U32, w, DE.Length{}, DSP.step_ok(U32, w, DE.Length{}, g))), DTR.so_obs(U32, w, DE.Length{}, DSP.step_ok(U32, w, DE.Length{}, g))), DTR.so_step(U32, w, DE.Length{}, DSP.step_ok(U32, w, DE.Length{}, g))))

def len_good(+w: DAS.Shadow<U32>, +g: {DAS.good(U32, w) == True{} : Bool}) -> {DAS.good(U32, lsh(w, g)) == True{} : Bool}:
  DTR.so_good(U32, w, DE.Length{}, DSP.step_ok(U32, w, DE.Length{}, g))

def len_all(+w: DAS.Shadow<U32>, +g: {DAS.good(U32, w) == True{} : Bool}) -> {(DAS.model(U32, lsh(w, g)), DTR.so_obs(U32, w, DE.Length{}, DSP.step_ok(U32, w, DE.Length{}, g))) == (DAS.model(U32, w), DE.ONat{SC.length(U32, ws(w))}) : DS.Model<U32> & DE.Obs<U32>}:
  match w:
    case DAS.Sh{+l, +d, +n, +t}:
      DTR.so_spec(U32, DAS.Sh{l, d, n, t}, DE.Length{}, DSP.step_ok(U32, DAS.Sh{l, d, n, t}, DE.Length{}, g))

def len_val(+w: DAS.Shadow<U32>, +g: {DAS.good(U32, w) == True{} : Bool}) -> {unnat(DTR.so_obs(U32, w, DE.Length{}, DSP.step_ok(U32, w, DE.Length{}, g))) == SC.length(U32, ws(w)) : Nat}:
  p_nat(DAS.model(U32, lsh(w, g)), DTR.so_obs(U32, w, DE.Length{}, DSP.step_ok(U32, w, DE.Length{}, g)), DAS.model(U32, w), DE.ONat{SC.length(U32, ws(w))}, len_all(w, g))

def len_ws(+w: DAS.Shadow<U32>, +g: {DAS.good(U32, w) == True{} : Bool}) -> {ws(lsh(w, g)) == ws(w) : List<&2, U32>}:
  p_items(DAS.model(U32, lsh(w, g)), DTR.so_obs(U32, w, DE.Length{}, DSP.step_ok(U32, w, DE.Length{}, g)), DAS.model(U32, w), DE.ONat{SC.length(U32, ws(w))}, len_all(w, g))

def len_lim(+w: DAS.Shadow<U32>, +g: {DAS.good(U32, w) == True{} : Bool}) -> {lim(lsh(w, g)) == lim(w) : Nat}:
  p_lim(DAS.model(U32, lsh(w, g)), DTR.so_obs(U32, w, DE.Length{}, DSP.step_ok(U32, w, DE.Length{}, g)), DAS.model(U32, w), DE.ONat{SC.length(U32, ws(w))}, len_all(w, g))

def dep(w: DAS.Shadow<U32>) -> Nat:
  match w:
    case DAS.Sh{l, d, n, t}:
      d

# ---- set (an index below the length) ----

def sp_set(+l: Nat, +d: Nat, +xs: List<&2, U32>, +q: Nat, +v: U32, +h: {Nat.is_lt(q, SC.length(U32, xs)) == True{} : Bool}) -> {DS.step_parts(U32, l, d, xs, DE.Set{q, v}) == (DS.M{l, d, SC.update(U32, xs, q, v)}, DE.OUnit{Done{Unit{}}}) : DS.Model<U32> & DE.Obs<U32>}:
  %Equal.sym(Bool, Nat.is_lt(q, SC.length(U32, xs)), True{}, h) : {Bool.pick(DS.Model<U32> & DE.Obs<U32>, _, (DS.M{l, d, SC.update(U32, xs, q, v)}, DE.OUnit{DS.ok_unit()}), (DS.M{l, d, xs}, DE.OUnit{Fail{DE.IndexOutOfRange{}}})) == (DS.M{l, d, SC.update(U32, xs, q, v)}, DE.OUnit{Done{Unit{}}}) : DS.Model<U32> & DE.Obs<U32>}
  {==}

def ssh(+w: DAS.Shadow<U32>, +g: {DAS.good(U32, w) == True{} : Bool}, +q: Nat, +v: U32) -> DAS.Shadow<U32>:
  DTR.so_sh(U32, w, DE.Set{q, v}, DSP.step_ok(U32, w, DE.Set{q, v}, g))

def set_eq(+w: DAS.Shadow<U32>, +g: {DAS.good(U32, w) == True{} : Bool}, +q: Nat, +v: U32) -> {D.set(U32, DAS.real(U32, w), q, v) == (DAS.real(U32, ssh(w, g, q, v)), ununit(DTR.so_obs(U32, w, DE.Set{q, v}, DSP.step_ok(U32, w, DE.Set{q, v}, g)))) : D.DynArray<&2, U32> & Result<&2, &2, DE.Error, Unit>}:
  Equal.trans(D.DynArray<&2, U32> & Result<&2, &2, DE.Error, Unit>, D.set(U32, DAS.real(U32, w), q, v), uunit(D.obs_unit(U32, D.set(U32, DAS.real(U32, w), q, v))), (DAS.real(U32, ssh(w, g, q, v)), ununit(DTR.so_obs(U32, w, DE.Set{q, v}, DSP.step_ok(U32, w, DE.Set{q, v}, g)))),
    Equal.sym(D.DynArray<&2, U32> & Result<&2, &2, DE.Error, Unit>, uunit(D.obs_unit(U32, D.set(U32, DAS.real(U32, w), q, v))), D.set(U32, DAS.real(U32, w), q, v), uunit_obs(D.set(U32, DAS.real(U32, w), q, v))),
    Equal.cong(D.DynArray<&2, U32> & DE.Obs<U32>, D.DynArray<&2, U32> & Result<&2, &2, DE.Error, Unit>, p => uunit(p), D.step(U32, DAS.real(U32, w), DE.Set{q, v}), (DAS.real(U32, DTR.so_sh(U32, w, DE.Set{q, v}, DSP.step_ok(U32, w, DE.Set{q, v}, g))), DTR.so_obs(U32, w, DE.Set{q, v}, DSP.step_ok(U32, w, DE.Set{q, v}, g))), DTR.so_step(U32, w, DE.Set{q, v}, DSP.step_ok(U32, w, DE.Set{q, v}, g))))

def set_good(+w: DAS.Shadow<U32>, +g: {DAS.good(U32, w) == True{} : Bool}, +q: Nat, +v: U32) -> {DAS.good(U32, ssh(w, g, q, v)) == True{} : Bool}:
  DTR.so_good(U32, w, DE.Set{q, v}, DSP.step_ok(U32, w, DE.Set{q, v}, g))

def set_all(+w: DAS.Shadow<U32>, +g: {DAS.good(U32, w) == True{} : Bool}, +q: Nat, +v: U32, +h: {Nat.is_lt(q, SC.length(U32, ws(w))) == True{} : Bool}) -> {(DAS.model(U32, ssh(w, g, q, v)), DTR.so_obs(U32, w, DE.Set{q, v}, DSP.step_ok(U32, w, DE.Set{q, v}, g))) == (DS.M{lim(w), dep(w), SC.update(U32, ws(w), q, v)}, DE.OUnit{Done{Unit{}}}) : DS.Model<U32> & DE.Obs<U32>}:
  match w:
    case DAS.Sh{+l, +d, +n, +t}:
      Equal.trans(DS.Model<U32> & DE.Obs<U32>, (DAS.model(U32, ssh(DAS.Sh{l, d, n, t}, g, q, v)), DTR.so_obs(U32, DAS.Sh{l, d, n, t}, DE.Set{q, v}, DSP.step_ok(U32, DAS.Sh{l, d, n, t}, DE.Set{q, v}, g))), DS.step_parts(U32, l, d, LY.somes(U32, AR.slots(Maybe<&2, U32>, t)), DE.Set{q, v}), (DS.M{l, d, SC.update(U32, LY.somes(U32, AR.slots(Maybe<&2, U32>, t)), q, v)}, DE.OUnit{Done{Unit{}}}),
        DTR.so_spec(U32, DAS.Sh{l, d, n, t}, DE.Set{q, v}, DSP.step_ok(U32, DAS.Sh{l, d, n, t}, DE.Set{q, v}, g)), sp_set(l, d, LY.somes(U32, AR.slots(Maybe<&2, U32>, t)), q, v, h))

def set_val(+w: DAS.Shadow<U32>, +g: {DAS.good(U32, w) == True{} : Bool}, +q: Nat, +v: U32, +h: {Nat.is_lt(q, SC.length(U32, ws(w))) == True{} : Bool}) -> {ununit(DTR.so_obs(U32, w, DE.Set{q, v}, DSP.step_ok(U32, w, DE.Set{q, v}, g))) == Done{Unit{}} : Result<&2, &2, DE.Error, Unit>}:
  p_unit(DAS.model(U32, ssh(w, g, q, v)), DTR.so_obs(U32, w, DE.Set{q, v}, DSP.step_ok(U32, w, DE.Set{q, v}, g)), DS.M{lim(w), dep(w), SC.update(U32, ws(w), q, v)}, DE.OUnit{Done{Unit{}}}, set_all(w, g, q, v, h))

def set_ws(+w: DAS.Shadow<U32>, +g: {DAS.good(U32, w) == True{} : Bool}, +q: Nat, +v: U32, +h: {Nat.is_lt(q, SC.length(U32, ws(w))) == True{} : Bool}) -> {ws(ssh(w, g, q, v)) == SC.update(U32, ws(w), q, v) : List<&2, U32>}:
  p_items(DAS.model(U32, ssh(w, g, q, v)), DTR.so_obs(U32, w, DE.Set{q, v}, DSP.step_ok(U32, w, DE.Set{q, v}, g)), DS.M{lim(w), dep(w), SC.update(U32, ws(w), q, v)}, DE.OUnit{Done{Unit{}}}, set_all(w, g, q, v, h))

def set_lim(+w: DAS.Shadow<U32>, +g: {DAS.good(U32, w) == True{} : Bool}, +q: Nat, +v: U32, +h: {Nat.is_lt(q, SC.length(U32, ws(w))) == True{} : Bool}) -> {lim(ssh(w, g, q, v)) == lim(w) : Nat}:
  p_lim(DAS.model(U32, ssh(w, g, q, v)), DTR.so_obs(U32, w, DE.Set{q, v}, DSP.step_ok(U32, w, DE.Set{q, v}, g)), DS.M{lim(w), dep(w), SC.update(U32, ws(w), q, v)}, DE.OUnit{Done{Unit{}}}, set_all(w, g, q, v, h))

# ---- push ----


# below the depth limit a push succeeds (in place, or after one doubling)
def sp_push_c(+l: Nat, +d: Nat, +xs: List<&2, U32>, +v: U32, c: Bool, +ec: {Nat.is_lt(d, l) == c : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +h: {Nat.is_lt(SC.length(U32, xs), SC.pow2(l)) == True{} : Bool}, +e1: {Nat.is_lt(SC.length(U32, xs), SC.pow2(d)) == False{} : Bool}) -> {Bool.pick(DS.Model<U32> & DE.Obs<U32>, Nat.is_lt(d, l), (DS.M{l, 1n+d, SC.snoc(U32, xs, v)}, DE.OUnit{DS.ok_unit()}), (DS.M{l, d, xs}, DE.OUnit{Fail{DE.CapacityExceeded{}}})) == (DS.M{l, 1n+d, SC.snoc(U32, xs, v)}, DE.OUnit{Done{Unit{}}}) : DS.Model<U32> & DE.Obs<U32>}:
  match c:
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(d, l), True{}, ec) : {Bool.pick(DS.Model<U32> & DE.Obs<U32>, _, (DS.M{l, 1n+d, SC.snoc(U32, xs, v)}, DE.OUnit{DS.ok_unit()}), (DS.M{l, d, xs}, DE.OUnit{Fail{DE.CapacityExceeded{}}})) == (DS.M{l, 1n+d, SC.snoc(U32, xs, v)}, DE.OUnit{Done{Unit{}}}) : DS.Model<U32> & DE.Obs<U32>}
      {==}
    case False{}:
      +edl = N.le_antisym(d, l, hd, N.not_lt_le(d, l, ec))
      Empty.absurd({Bool.pick(DS.Model<U32> & DE.Obs<U32>, Nat.is_lt(d, l), (DS.M{l, 1n+d, SC.snoc(U32, xs, v)}, DE.OUnit{DS.ok_unit()}), (DS.M{l, d, xs}, DE.OUnit{Fail{DE.CapacityExceeded{}}})) == (DS.M{l, 1n+d, SC.snoc(U32, xs, v)}, DE.OUnit{Done{Unit{}}}) : DS.Model<U32> & DE.Obs<U32>}, L.true_not_false(Nat.is_lt(SC.length(U32, xs), SC.pow2(d)), L.subst(Nat, x => {Nat.is_lt(SC.length(U32, xs), SC.pow2(x)) == True{} : Bool}, l, d, Equal.sym(Nat, d, l, edl), h), e1))

def sp_push_b(+l: Nat, +d: Nat, +xs: List<&2, U32>, +v: U32, b: Bool, +eb: {Nat.is_lt(SC.length(U32, xs), SC.pow2(d)) == b : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +h: {Nat.is_lt(SC.length(U32, xs), SC.pow2(l)) == True{} : Bool}) -> {DS.step_parts(U32, l, d, xs, DE.Push{v}) == (DS.M{l, Bool.pick(Nat, Nat.is_lt(SC.length(U32, xs), SC.pow2(d)), d, 1n+d), SC.snoc(U32, xs, v)}, DE.OUnit{Done{Unit{}}}) : DS.Model<U32> & DE.Obs<U32>}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(SC.length(U32, xs), SC.pow2(d)), True{}, eb) : {Bool.pick(DS.Model<U32> & DE.Obs<U32>, _, (DS.M{l, d, SC.snoc(U32, xs, v)}, DE.OUnit{DS.ok_unit()}), Bool.pick(DS.Model<U32> & DE.Obs<U32>, Nat.is_lt(d, l), (DS.M{l, 1n+d, SC.snoc(U32, xs, v)}, DE.OUnit{DS.ok_unit()}), (DS.M{l, d, xs}, DE.OUnit{Fail{DE.CapacityExceeded{}}}))) == (DS.M{l, Bool.pick(Nat, _, d, 1n+d), SC.snoc(U32, xs, v)}, DE.OUnit{Done{Unit{}}}) : DS.Model<U32> & DE.Obs<U32>}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_lt(SC.length(U32, xs), SC.pow2(d)), False{}, eb) : {Bool.pick(DS.Model<U32> & DE.Obs<U32>, _, (DS.M{l, d, SC.snoc(U32, xs, v)}, DE.OUnit{DS.ok_unit()}), Bool.pick(DS.Model<U32> & DE.Obs<U32>, Nat.is_lt(d, l), (DS.M{l, 1n+d, SC.snoc(U32, xs, v)}, DE.OUnit{DS.ok_unit()}), (DS.M{l, d, xs}, DE.OUnit{Fail{DE.CapacityExceeded{}}}))) == (DS.M{l, Bool.pick(Nat, _, d, 1n+d), SC.snoc(U32, xs, v)}, DE.OUnit{Done{Unit{}}}) : DS.Model<U32> & DE.Obs<U32>}
      sp_push_c(l, d, xs, v, Nat.is_lt(d, l), {==}, hd, h, eb)

# at the depth limit with every slot used a push is rejected
def sp_full_c(+l: Nat, +d: Nat, +xs: List<&2, U32>, +v: U32, c: Bool, +ec: {Nat.is_lt(d, l) == c : Bool}, +hc: {Nat.is_le(SC.length(U32, xs), SC.pow2(d)) == True{} : Bool}, +h: {Nat.is_lt(SC.length(U32, xs), SC.pow2(l)) == False{} : Bool}) -> {Bool.pick(DS.Model<U32> & DE.Obs<U32>, Nat.is_lt(d, l), (DS.M{l, 1n+d, SC.snoc(U32, xs, v)}, DE.OUnit{DS.ok_unit()}), (DS.M{l, d, xs}, DE.OUnit{Fail{DE.CapacityExceeded{}}})) == (DS.M{l, d, xs}, DE.OUnit{Fail{DE.CapacityExceeded{}}}) : DS.Model<U32> & DE.Obs<U32>}:
  match c:
    case False{}:
      %Equal.sym(Bool, Nat.is_lt(d, l), False{}, ec) : {Bool.pick(DS.Model<U32> & DE.Obs<U32>, _, (DS.M{l, 1n+d, SC.snoc(U32, xs, v)}, DE.OUnit{DS.ok_unit()}), (DS.M{l, d, xs}, DE.OUnit{Fail{DE.CapacityExceeded{}}})) == (DS.M{l, d, xs}, DE.OUnit{Fail{DE.CapacityExceeded{}}}) : DS.Model<U32> & DE.Obs<U32>}
      {==}
    case True{}:
      Empty.absurd({Bool.pick(DS.Model<U32> & DE.Obs<U32>, Nat.is_lt(d, l), (DS.M{l, 1n+d, SC.snoc(U32, xs, v)}, DE.OUnit{DS.ok_unit()}), (DS.M{l, d, xs}, DE.OUnit{Fail{DE.CapacityExceeded{}}})) == (DS.M{l, d, xs}, DE.OUnit{Fail{DE.CapacityExceeded{}}}) : DS.Model<U32> & DE.Obs<U32>}, L.true_not_false(Nat.is_lt(SC.length(U32, xs), SC.pow2(l)), N.le_lt_trans(SC.length(U32, xs), SC.pow2(d), SC.pow2(l), hc, N.pow2_strict(d, l, ec)), h))

def sp_full(+l: Nat, +d: Nat, +xs: List<&2, U32>, +v: U32, +hc: {Nat.is_le(SC.length(U32, xs), SC.pow2(d)) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +h: {Nat.is_lt(SC.length(U32, xs), SC.pow2(l)) == False{} : Bool}) -> {DS.step_parts(U32, l, d, xs, DE.Push{v}) == (DS.M{l, d, xs}, DE.OUnit{Fail{DE.CapacityExceeded{}}}) : DS.Model<U32> & DE.Obs<U32>}:
  +h1 = N.le_not_lt(SC.length(U32, xs), SC.pow2(d), N.le_trans(SC.pow2(d), SC.pow2(l), SC.length(U32, xs), N.pow2_mono(d, l, hd), N.not_lt_le(SC.length(U32, xs), SC.pow2(l), h)))
  %Equal.sym(Bool, Nat.is_lt(SC.length(U32, xs), SC.pow2(d)), False{}, h1) : {Bool.pick(DS.Model<U32> & DE.Obs<U32>, _, (DS.M{l, d, SC.snoc(U32, xs, v)}, DE.OUnit{DS.ok_unit()}), Bool.pick(DS.Model<U32> & DE.Obs<U32>, Nat.is_lt(d, l), (DS.M{l, 1n+d, SC.snoc(U32, xs, v)}, DE.OUnit{DS.ok_unit()}), (DS.M{l, d, xs}, DE.OUnit{Fail{DE.CapacityExceeded{}}}))) == (DS.M{l, d, xs}, DE.OUnit{Fail{DE.CapacityExceeded{}}}) : DS.Model<U32> & DE.Obs<U32>}
  sp_full_c(l, d, xs, v, Nat.is_lt(d, l), {==}, hc, h)

def psh(+w: DAS.Shadow<U32>, +g: {DAS.good(U32, w) == True{} : Bool}, +v: U32) -> DAS.Shadow<U32>:
  DTR.so_sh(U32, w, DE.Push{v}, DSP.step_ok(U32, w, DE.Push{v}, g))

def push_eq(+w: DAS.Shadow<U32>, +g: {DAS.good(U32, w) == True{} : Bool}, +v: U32) -> {D.push(U32, DAS.real(U32, w), v) == (DAS.real(U32, psh(w, g, v)), ununit(DTR.so_obs(U32, w, DE.Push{v}, DSP.step_ok(U32, w, DE.Push{v}, g)))) : D.DynArray<&2, U32> & Result<&2, &2, DE.Error, Unit>}:
  Equal.trans(D.DynArray<&2, U32> & Result<&2, &2, DE.Error, Unit>, D.push(U32, DAS.real(U32, w), v), uunit(D.obs_unit(U32, D.push(U32, DAS.real(U32, w), v))), (DAS.real(U32, psh(w, g, v)), ununit(DTR.so_obs(U32, w, DE.Push{v}, DSP.step_ok(U32, w, DE.Push{v}, g)))),
    Equal.sym(D.DynArray<&2, U32> & Result<&2, &2, DE.Error, Unit>, uunit(D.obs_unit(U32, D.push(U32, DAS.real(U32, w), v))), D.push(U32, DAS.real(U32, w), v), uunit_obs(D.push(U32, DAS.real(U32, w), v))),
    Equal.cong(D.DynArray<&2, U32> & DE.Obs<U32>, D.DynArray<&2, U32> & Result<&2, &2, DE.Error, Unit>, p => uunit(p), D.step(U32, DAS.real(U32, w), DE.Push{v}), (DAS.real(U32, DTR.so_sh(U32, w, DE.Push{v}, DSP.step_ok(U32, w, DE.Push{v}, g))), DTR.so_obs(U32, w, DE.Push{v}, DSP.step_ok(U32, w, DE.Push{v}, g))), DTR.so_step(U32, w, DE.Push{v}, DSP.step_ok(U32, w, DE.Push{v}, g))))

def push_good(+w: DAS.Shadow<U32>, +g: {DAS.good(U32, w) == True{} : Bool}, +v: U32) -> {DAS.good(U32, psh(w, g, v)) == True{} : Bool}:
  DTR.so_good(U32, w, DE.Push{v}, DSP.step_ok(U32, w, DE.Push{v}, g))


def push_all(+w: DAS.Shadow<U32>, +g: {DAS.good(U32, w) == True{} : Bool}, +v: U32, +h: {Nat.is_lt(SC.length(U32, ws(w)), SC.pow2(lim(w))) == True{} : Bool}) -> {(DAS.model(U32, psh(w, g, v)), DTR.so_obs(U32, w, DE.Push{v}, DSP.step_ok(U32, w, DE.Push{v}, g))) == (DS.M{lim(w), Bool.pick(Nat, Nat.is_lt(SC.length(U32, ws(w)), SC.pow2(dep(w))), dep(w), 1n+dep(w)), SC.snoc(U32, ws(w), v)}, DE.OUnit{Done{Unit{}}}) : DS.Model<U32> & DE.Obs<U32>}:
  match w:
    case DAS.Sh{+l, +d, +n, +t}:
      Equal.trans(DS.Model<U32> & DE.Obs<U32>, (DAS.model(U32, psh(DAS.Sh{l, d, n, t}, g, v)), DTR.so_obs(U32, DAS.Sh{l, d, n, t}, DE.Push{v}, DSP.step_ok(U32, DAS.Sh{l, d, n, t}, DE.Push{v}, g))), DS.step_parts(U32, l, d, LY.somes(U32, AR.slots(Maybe<&2, U32>, t)), DE.Push{v}), (DS.M{l, Bool.pick(Nat, Nat.is_lt(SC.length(U32, LY.somes(U32, AR.slots(Maybe<&2, U32>, t))), SC.pow2(d)), d, 1n+d), SC.snoc(U32, LY.somes(U32, AR.slots(Maybe<&2, U32>, t)), v)}, DE.OUnit{Done{Unit{}}}),
        DTR.so_spec(U32, DAS.Sh{l, d, n, t}, DE.Push{v}, DSP.step_ok(U32, DAS.Sh{l, d, n, t}, DE.Push{v}, g)), sp_push_b(l, d, LY.somes(U32, AR.slots(Maybe<&2, U32>, t)), v, Nat.is_lt(SC.length(U32, LY.somes(U32, AR.slots(Maybe<&2, U32>, t))), SC.pow2(d)), {==}, DAS.g_depth(U32, l, d, n, t, g), h))

def push_val(+w: DAS.Shadow<U32>, +g: {DAS.good(U32, w) == True{} : Bool}, +v: U32, +h: {Nat.is_lt(SC.length(U32, ws(w)), SC.pow2(lim(w))) == True{} : Bool}) -> {ununit(DTR.so_obs(U32, w, DE.Push{v}, DSP.step_ok(U32, w, DE.Push{v}, g))) == Done{Unit{}} : Result<&2, &2, DE.Error, Unit>}:
  p_unit(DAS.model(U32, psh(w, g, v)), DTR.so_obs(U32, w, DE.Push{v}, DSP.step_ok(U32, w, DE.Push{v}, g)), DS.M{lim(w), Bool.pick(Nat, Nat.is_lt(SC.length(U32, ws(w)), SC.pow2(dep(w))), dep(w), 1n+dep(w)), SC.snoc(U32, ws(w), v)}, DE.OUnit{Done{Unit{}}}, push_all(w, g, v, h))

def push_ws(+w: DAS.Shadow<U32>, +g: {DAS.good(U32, w) == True{} : Bool}, +v: U32, +h: {Nat.is_lt(SC.length(U32, ws(w)), SC.pow2(lim(w))) == True{} : Bool}) -> {ws(psh(w, g, v)) == SC.snoc(U32, ws(w), v) : List<&2, U32>}:
  p_items(DAS.model(U32, psh(w, g, v)), DTR.so_obs(U32, w, DE.Push{v}, DSP.step_ok(U32, w, DE.Push{v}, g)), DS.M{lim(w), Bool.pick(Nat, Nat.is_lt(SC.length(U32, ws(w)), SC.pow2(dep(w))), dep(w), 1n+dep(w)), SC.snoc(U32, ws(w), v)}, DE.OUnit{Done{Unit{}}}, push_all(w, g, v, h))

def push_lim(+w: DAS.Shadow<U32>, +g: {DAS.good(U32, w) == True{} : Bool}, +v: U32, +h: {Nat.is_lt(SC.length(U32, ws(w)), SC.pow2(lim(w))) == True{} : Bool}) -> {lim(psh(w, g, v)) == lim(w) : Nat}:
  p_lim(DAS.model(U32, psh(w, g, v)), DTR.so_obs(U32, w, DE.Push{v}, DSP.step_ok(U32, w, DE.Push{v}, g)), DS.M{lim(w), Bool.pick(Nat, Nat.is_lt(SC.length(U32, ws(w)), SC.pow2(dep(w))), dep(w), 1n+dep(w)), SC.snoc(U32, ws(w), v)}, DE.OUnit{Done{Unit{}}}, push_all(w, g, v, h))

def full_all(+w: DAS.Shadow<U32>, +g: {DAS.good(U32, w) == True{} : Bool}, +v: U32, +h: {Nat.is_lt(SC.length(U32, ws(w)), SC.pow2(lim(w))) == False{} : Bool}) -> {(DAS.model(U32, psh(w, g, v)), DTR.so_obs(U32, w, DE.Push{v}, DSP.step_ok(U32, w, DE.Push{v}, g))) == (DS.M{lim(w), dep(w), ws(w)}, DE.OUnit{Fail{DE.CapacityExceeded{}}}) : DS.Model<U32> & DE.Obs<U32>}:
  match w:
    case DAS.Sh{+l, +d, +n, +t}:
      +hc = L.subst(Nat, x => {Nat.is_le(x, SC.pow2(d)) == True{} : Bool}, n, SC.length(U32, LY.somes(U32, AR.slots(Maybe<&2, U32>, t))), Equal.sym(Nat, SC.length(U32, LY.somes(U32, AR.slots(Maybe<&2, U32>, t))), n, ws_len(l, d, n, t, g)), DSP.n_le_cap(U32, l, d, n, t, g))
      Equal.trans(DS.Model<U32> & DE.Obs<U32>, (DAS.model(U32, psh(DAS.Sh{l, d, n, t}, g, v)), DTR.so_obs(U32, DAS.Sh{l, d, n, t}, DE.Push{v}, DSP.step_ok(U32, DAS.Sh{l, d, n, t}, DE.Push{v}, g))), DS.step_parts(U32, l, d, LY.somes(U32, AR.slots(Maybe<&2, U32>, t)), DE.Push{v}), (DS.M{l, d, LY.somes(U32, AR.slots(Maybe<&2, U32>, t))}, DE.OUnit{Fail{DE.CapacityExceeded{}}}),
        DTR.so_spec(U32, DAS.Sh{l, d, n, t}, DE.Push{v}, DSP.step_ok(U32, DAS.Sh{l, d, n, t}, DE.Push{v}, g)), sp_full(l, d, LY.somes(U32, AR.slots(Maybe<&2, U32>, t)), v, hc, DAS.g_depth(U32, l, d, n, t, g), h))

def full_val(+w: DAS.Shadow<U32>, +g: {DAS.good(U32, w) == True{} : Bool}, +v: U32, +h: {Nat.is_lt(SC.length(U32, ws(w)), SC.pow2(lim(w))) == False{} : Bool}) -> {ununit(DTR.so_obs(U32, w, DE.Push{v}, DSP.step_ok(U32, w, DE.Push{v}, g))) == Fail{DE.CapacityExceeded{}} : Result<&2, &2, DE.Error, Unit>}:
  p_unit(DAS.model(U32, psh(w, g, v)), DTR.so_obs(U32, w, DE.Push{v}, DSP.step_ok(U32, w, DE.Push{v}, g)), DS.M{lim(w), dep(w), ws(w)}, DE.OUnit{Fail{DE.CapacityExceeded{}}}, full_all(w, g, v, h))

def full_ws(+w: DAS.Shadow<U32>, +g: {DAS.good(U32, w) == True{} : Bool}, +v: U32, +h: {Nat.is_lt(SC.length(U32, ws(w)), SC.pow2(lim(w))) == False{} : Bool}) -> {ws(psh(w, g, v)) == ws(w) : List<&2, U32>}:
  p_items(DAS.model(U32, psh(w, g, v)), DTR.so_obs(U32, w, DE.Push{v}, DSP.step_ok(U32, w, DE.Push{v}, g)), DS.M{lim(w), dep(w), ws(w)}, DE.OUnit{Fail{DE.CapacityExceeded{}}}, full_all(w, g, v, h))

def full_lim(+w: DAS.Shadow<U32>, +g: {DAS.good(U32, w) == True{} : Bool}, +v: U32, +h: {Nat.is_lt(SC.length(U32, ws(w)), SC.pow2(lim(w))) == False{} : Bool}) -> {lim(psh(w, g, v)) == lim(w) : Nat}:
  p_lim(DAS.model(U32, psh(w, g, v)), DTR.so_obs(U32, w, DE.Push{v}, DSP.step_ok(U32, w, DE.Push{v}, g)), DS.M{lim(w), dep(w), ws(w)}, DE.OUnit{Fail{DE.CapacityExceeded{}}}, full_all(w, g, v, h))

# ---- clear ----

def csh(+w: DAS.Shadow<U32>, +g: {DAS.good(U32, w) == True{} : Bool}) -> DAS.Shadow<U32>:
  DTR.so_sh(U32, w, DE.Clear{}, DSP.step_ok(U32, w, DE.Clear{}, g))

def clear_eq(+w: DAS.Shadow<U32>, +g: {DAS.good(U32, w) == True{} : Bool}) -> {D.clear(U32, DAS.real(U32, w)) == DAS.real(U32, csh(w, g)) : D.DynArray<&2, U32>}:
  L.pair_fst(D.DynArray<&2, U32>, DE.Obs<U32>, D.clear(U32, DAS.real(U32, w)), DE.OUnit{Done{Unit{}}}, DAS.real(U32, csh(w, g)), DTR.so_obs(U32, w, DE.Clear{}, DSP.step_ok(U32, w, DE.Clear{}, g)), DTR.so_step(U32, w, DE.Clear{}, DSP.step_ok(U32, w, DE.Clear{}, g)))

def clear_good(+w: DAS.Shadow<U32>, +g: {DAS.good(U32, w) == True{} : Bool}) -> {DAS.good(U32, csh(w, g)) == True{} : Bool}:
  DTR.so_good(U32, w, DE.Clear{}, DSP.step_ok(U32, w, DE.Clear{}, g))

def clear_all(+w: DAS.Shadow<U32>, +g: {DAS.good(U32, w) == True{} : Bool}) -> {(DAS.model(U32, csh(w, g)), DTR.so_obs(U32, w, DE.Clear{}, DSP.step_ok(U32, w, DE.Clear{}, g))) == (DS.M{lim(w), dep(w), Nil{}}, DE.OUnit{Done{Unit{}}}) : DS.Model<U32> & DE.Obs<U32>}:
  match w:
    case DAS.Sh{+l, +d, +n, +t}:
      DTR.so_spec(U32, DAS.Sh{l, d, n, t}, DE.Clear{}, DSP.step_ok(U32, DAS.Sh{l, d, n, t}, DE.Clear{}, g))

def clear_ws(+w: DAS.Shadow<U32>, +g: {DAS.good(U32, w) == True{} : Bool}) -> {ws(csh(w, g)) == Nil{} : List<&2, U32>}:
  p_items(DAS.model(U32, csh(w, g)), DTR.so_obs(U32, w, DE.Clear{}, DSP.step_ok(U32, w, DE.Clear{}, g)), DS.M{lim(w), dep(w), Nil{}}, DE.OUnit{Done{Unit{}}}, clear_all(w, g))

def clear_lim(+w: DAS.Shadow<U32>, +g: {DAS.good(U32, w) == True{} : Bool}) -> {lim(csh(w, g)) == lim(w) : Nat}:
  p_lim(DAS.model(U32, csh(w, g)), DTR.so_obs(U32, w, DE.Clear{}, DSP.step_ok(U32, w, DE.Clear{}, g)), DS.M{lim(w), dep(w), Nil{}}, DE.OUnit{Done{Unit{}}}, clear_all(w, g))
