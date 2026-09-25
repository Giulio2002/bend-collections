import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/array.bend as AR
import ../../../spec/lib/common.bend as SC
import ../../../spec/containers/dynamic_array.bend as S
import ../../../src/containers/dynamic_array.bend as DA
import ./layout.bend as LY
import ./state.bend as ST
import ../../lib/list.bend as LL

# The reserve loop DA.grow_until, described on shadows, and the least
# capacity exponent it reaches (S.fit, fuel-independent).

# The grown shadow (depth + 1, old tree as left half) is good when d < l.
def grow_good(-T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {ST.good(T, ST.Sh{l, d, n, t}) == True{} : Bool}, +hdl: {Nat.is_lt(d, l) == True{} : Bool}) -> {ST.good(T, ST.Sh{l, 1n+d, n, AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})}}) == True{} : Bool}:
  ST.good_intro(T, l, 1n+d, n, AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})}, ST.g_limit(T, l, d, n, t, g), N.lt_succ_le_succ(d, l, hdl),
    L.and_intro(AR.perfect(Maybe<&2, T>, d, t), AR.perfect(Maybe<&2, T>, d, AR.trep(Maybe<&2, T>, d, None{})), ST.g_perfect(T, l, d, n, t, g), AR.trep_perfect(Maybe<&2, T>, d, None{})),
    L.subst(List<&2, Maybe<&2, T>>, ys => {LY.lay(T, ys, n) == True{} : Bool}, SC.append(Maybe<&2, T>, AR.slots(Maybe<&2, T>, t), SC.replicate(Maybe<&2, T>, SC.pow2(d), None{})), AR.slots(Maybe<&2, T>, AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})}), Equal.sym(List<&2, Maybe<&2, T>>, AR.slots(Maybe<&2, T>, AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})}), SC.append(Maybe<&2, T>, AR.slots(Maybe<&2, T>, t), SC.replicate(Maybe<&2, T>, SC.pow2(d), None{})), ST.slots_grown(T, d, t)), LY.lay_grow(T, AR.slots(Maybe<&2, T>, t), n, SC.pow2(d), ST.g_lay(T, l, d, n, t, g))))

def grow_model(-T: Data, +d: Nat, +t: AR.Tree<Maybe<&2, T>>) -> {LY.somes(T, AR.slots(Maybe<&2, T>, AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})})) == LY.somes(T, AR.slots(Maybe<&2, T>, t)) : List<&2, T>}:
  %Equal.sym(List<&2, Maybe<&2, T>>, AR.slots(Maybe<&2, T>, AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})}), SC.append(Maybe<&2, T>, AR.slots(Maybe<&2, T>, t), SC.replicate(Maybe<&2, T>, SC.pow2(d), None{})), ST.slots_grown(T, d, t)) : {LY.somes(T, _) == LY.somes(T, AR.slots(Maybe<&2, T>, t)) : List<&2, T>}
  LY.somes_grow(T, AR.slots(Maybe<&2, T>, t), SC.pow2(d))

def sgstep(-T: Data, +k: Nat, sh: ST.Shadow<T>) -> ST.Shadow<T>:
  match sh:
    case ST.Sh{+l, +d, +n, +t}:
      Bool.pick(ST.Shadow<T>, Nat.is_le(k, SC.pow2(d)), ST.Sh{l, d, n, t}, ST.Sh{l, 1n+d, n, AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})}})

def sgrow(-T: Data, f: Nat, +k: Nat, sh: ST.Shadow<T>) -> ST.Shadow<T>:
  match f:
    case 0n:
      sh
    case 1n+g:
      sgrow(T, g, k, sgstep(T, k, sh))

# The source's own pow2 (still used for the 2^limit feasibility test, which
# is not cached) is the spec's.
def fits_nat(+k: Nat, +d: Nat, +b: Bool, +e: {Nat.is_le(k, DA.pow2(d)) == b : Bool}) -> {Nat.is_le(k, SC.pow2(d)) == b : Bool}:
  L.subst(Nat, x => {Nat.is_le(k, x) == b : Bool}, DA.pow2(d), SC.pow2(d), ST.pow2_src(d), e)

def gstep_case(-T: Data, +k: Nat, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +b: Bool, +eb: {Nat.is_le(k, SC.pow2(d)) == b : Bool}) -> {DA.grow_step(T, k, ST.real(T, ST.Sh{l, d, n, t})) == ST.real(T, sgstep(T, k, ST.Sh{l, d, n, t})) : DA.DynArray<&2, T>}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_le(k, SC.pow2(d)), True{}, eb) : {DA.grow_if(T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), _) == ST.real(T, Bool.pick(ST.Shadow<T>, Nat.is_le(k, SC.pow2(d)), ST.Sh{l, d, n, t}, ST.Sh{l, 1n+d, n, AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})}})) : DA.DynArray<&2, T>}
      %Equal.sym(Bool, Nat.is_le(k, SC.pow2(d)), True{}, eb) : {DA.DA{l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t)} == ST.real(T, Bool.pick(ST.Shadow<T>, _, ST.Sh{l, d, n, t}, ST.Sh{l, 1n+d, n, AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})}})) : DA.DynArray<&2, T>}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_le(k, SC.pow2(d)), False{}, eb) : {DA.grow_if(T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), _) == ST.real(T, Bool.pick(ST.Shadow<T>, Nat.is_le(k, SC.pow2(d)), ST.Sh{l, d, n, t}, ST.Sh{l, 1n+d, n, AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})}})) : DA.DynArray<&2, T>}
      %Equal.sym(Bool, Nat.is_le(k, SC.pow2(d)), False{}, eb) : {DA.DA{l, 1n+d, Nat.double(SC.pow2(d)), n, DA.grown(T, d, AR.thaw(Maybe<&2, T>, t))} == ST.real(T, Bool.pick(ST.Shadow<T>, _, ST.Sh{l, d, n, t}, ST.Sh{l, 1n+d, n, AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})}})) : DA.DynArray<&2, T>}
      %Equal.sym(Array<Maybe<&2, T>>, DA.grown(T, d, AR.thaw(Maybe<&2, T>, t)), AR.thaw(Maybe<&2, T>, AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})}), ST.grown_eq(T, d, t)) : {DA.DA{l, 1n+d, Nat.double(SC.pow2(d)), n, _} == ST.real(T, ST.Sh{l, 1n+d, n, AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})}}) : DA.DynArray<&2, T>}
      {==}

def grow_until_real(-T: Data, +f: Nat, +k: Nat, +sh: ST.Shadow<T>) -> {DA.grow_until(T, f, k, ST.real(T, sh)) == ST.real(T, sgrow(T, f, k, sh)) : DA.DynArray<&2, T>}:
  match f sh:
    case 0n _:
      {==}
    case 1n+g ST.Sh{+l, +d, +n, +t}:
      %Equal.sym(DA.DynArray<&2, T>, DA.grow_step(T, k, ST.real(T, ST.Sh{l, d, n, t})), ST.real(T, sgstep(T, k, ST.Sh{l, d, n, t})), gstep_case(T, k, l, d, n, t, Nat.is_le(k, SC.pow2(d)), {==})) : {DA.grow_until(T, g, k, _) == ST.real(T, sgrow(T, g, k, sgstep(T, k, ST.Sh{l, d, n, t}))) : DA.DynArray<&2, T>}
      grow_until_real(T, g, k, sgstep(T, k, ST.Sh{l, d, n, t}))

# ---- the least exponent ----

def fit_fits(+f: Nat, +d: Nat, +k: Nat, +h: {Nat.is_le(k, SC.pow2(d)) == True{} : Bool}) -> {S.fit(f, d, k) == d : Nat}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      %Equal.sym(Bool, Nat.is_le(k, SC.pow2(d)), True{}, h) : {Bool.pick(Nat, _, d, S.fit(g, 1n+d, k)) == d : Nat}
      {==}

def sgrow_fits(-T: Data, +f: Nat, +k: Nat, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +h: {Nat.is_le(k, SC.pow2(d)) == True{} : Bool}) -> {sgrow(T, f, k, ST.Sh{l, d, n, t}) == ST.Sh{l, d, n, t} : ST.Shadow<T>}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      %Equal.sym(Bool, Nat.is_le(k, SC.pow2(d)), True{}, h) : {sgrow(T, g, k, Bool.pick(ST.Shadow<T>, _, ST.Sh{l, d, n, t}, ST.Sh{l, 1n+d, n, AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})}})) == ST.Sh{l, d, n, t} : ST.Shadow<T>}
      sgrow_fits(T, g, k, l, d, n, t, h)

def room_left(+d: Nat, +g: Nat, +l: Nat, +h: {Nat.is_le(Nat.add(d, 1n+g), l) == True{} : Bool}) -> {Nat.is_lt(d, l) == True{} : Bool}:
  N.succ_le_lt(d, l, N.le_trans(1n+d, Nat.add(d, 1n+g), l, L.subst(Nat, x => {Nat.is_le(1n+d, x) == True{} : Bool}, 1n+Nat.add(d, g), Nat.add(d, 1n+g), Equal.sym(Nat, Nat.add(d, 1n+g), 1n+Nat.add(d, g), N.add_succ(d, g)), N.le_add_right(d, g)), h))

def fuel_shift(+d: Nat, +g: Nat, +l: Nat, +h: {Nat.is_le(Nat.add(d, 1n+g), l) == True{} : Bool}) -> {Nat.is_le(Nat.add(1n+d, g), l) == True{} : Bool}:
  L.subst(Nat, x => {Nat.is_le(x, l) == True{} : Bool}, Nat.add(d, 1n+g), 1n+Nat.add(d, g), N.add_succ(d, g), h)

def sgrow_props(-T: Data, +f: Nat, +k: Nat, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {ST.good(T, ST.Sh{l, d, n, t}) == True{} : Bool}, +hf: {Nat.is_le(Nat.add(d, f), l) == True{} : Bool}, +b: Bool, +eb: {Nat.is_le(k, SC.pow2(d)) == b : Bool}) -> {ST.model(T, sgrow(T, f, k, ST.Sh{l, d, n, t})) == S.M{l, S.fit(f, d, k), LY.somes(T, AR.slots(Maybe<&2, T>, t))} : S.Model<T>} & {ST.good(T, sgrow(T, f, k, ST.Sh{l, d, n, t})) == True{} : Bool}:
  match f b:
    case 0n _:
      ({==}, g)
    case 1n+h True{}:
      %Equal.sym(Bool, Nat.is_le(k, SC.pow2(d)), True{}, eb) : {ST.model(T, sgrow(T, h, k, Bool.pick(ST.Shadow<T>, _, ST.Sh{l, d, n, t}, ST.Sh{l, 1n+d, n, AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})}}))) == S.M{l, Bool.pick(Nat, _, d, S.fit(h, 1n+d, k)), LY.somes(T, AR.slots(Maybe<&2, T>, t))} : S.Model<T>} & {ST.good(T, sgrow(T, h, k, Bool.pick(ST.Shadow<T>, _, ST.Sh{l, d, n, t}, ST.Sh{l, 1n+d, n, AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})}}))) == True{} : Bool}
      %Equal.sym(ST.Shadow<T>, sgrow(T, h, k, ST.Sh{l, d, n, t}), ST.Sh{l, d, n, t}, sgrow_fits(T, h, k, l, d, n, t, eb)) : {ST.model(T, _) == S.M{l, d, LY.somes(T, AR.slots(Maybe<&2, T>, t))} : S.Model<T>} & {ST.good(T, _) == True{} : Bool}
      ({==}, g)
    case 1n+h False{}:
      +t1 = {AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})} : AR.Tree<Maybe<&2, T>>}
      +g1 = grow_good(T, l, d, n, t, g, room_left(d, h, l, hf))
      r = sgrow_props(T, h, k, l, 1n+d, n, t1, g1, fuel_shift(d, h, l, hf), Nat.is_le(k, SC.pow2(1n+d)), {==})
      %Equal.sym(Bool, Nat.is_le(k, SC.pow2(d)), False{}, eb) : {ST.model(T, sgrow(T, h, k, Bool.pick(ST.Shadow<T>, _, ST.Sh{l, d, n, t}, ST.Sh{l, 1n+d, n, t1}))) == S.M{l, Bool.pick(Nat, _, d, S.fit(h, 1n+d, k)), LY.somes(T, AR.slots(Maybe<&2, T>, t))} : S.Model<T>} & {ST.good(T, sgrow(T, h, k, Bool.pick(ST.Shadow<T>, _, ST.Sh{l, d, n, t}, ST.Sh{l, 1n+d, n, t1}))) == True{} : Bool}
      %grow_model(T, d, t) : {ST.model(T, sgrow(T, h, k, ST.Sh{l, 1n+d, n, t1})) == S.M{l, S.fit(h, 1n+d, k), _} : S.Model<T>} & {ST.good(T, sgrow(T, h, k, ST.Sh{l, 1n+d, n, t1})) == True{} : Bool}
      r

def fe_case(+f1: Nat, +f2: Nat, +d: Nat, +k: Nat, +h1: {Nat.is_le(k, SC.pow2(Nat.add(d, f1))) == True{} : Bool}, +h2: {Nat.is_le(k, SC.pow2(Nat.add(d, f2))) == True{} : Bool}, +b: Bool, +eb: {Nat.is_le(k, SC.pow2(d)) == b : Bool}) -> {S.fit(f1, d, k) == S.fit(f2, d, k) : Nat}:
  match f1 f2 b:
    case _ _ True{}:
      Equal.trans(Nat, S.fit(f1, d, k), d, S.fit(f2, d, k), fit_fits(f1, d, k, eb), Equal.sym(Nat, S.fit(f2, d, k), d, fit_fits(f2, d, k, eb)))
    case 0n _ False{}:
      Empty.absurd({d == S.fit(f2, d, k) : Nat}, L.true_not_false(Nat.is_le(k, SC.pow2(d)), L.subst(Nat, x => {Nat.is_le(k, SC.pow2(x)) == True{} : Bool}, Nat.add(d, 0n), d, N.add_zero(d), h1), eb))
    case 1n+g1 0n False{}:
      Empty.absurd({S.fit(1n+g1, d, k) == d : Nat}, L.true_not_false(Nat.is_le(k, SC.pow2(d)), L.subst(Nat, x => {Nat.is_le(k, SC.pow2(x)) == True{} : Bool}, Nat.add(d, 0n), d, N.add_zero(d), h2), eb))
    case 1n+g1 1n+g2 False{}:
      %Equal.sym(Bool, Nat.is_le(k, SC.pow2(d)), False{}, eb) : {Bool.pick(Nat, _, d, S.fit(g1, 1n+d, k)) == Bool.pick(Nat, _, d, S.fit(g2, 1n+d, k)) : Nat}
      fe_case(g1, g2, 1n+d, k, L.subst(Nat, x => {Nat.is_le(k, SC.pow2(x)) == True{} : Bool}, Nat.add(d, 1n+g1), 1n+Nat.add(d, g1), N.add_succ(d, g1), h1), L.subst(Nat, x => {Nat.is_le(k, SC.pow2(x)) == True{} : Bool}, Nat.add(d, 1n+g2), 1n+Nat.add(d, g2), N.add_succ(d, g2), h2), Nat.is_le(k, SC.pow2(1n+d)), {==})

def pow2_gt(+k: Nat) -> {Nat.is_lt(k, SC.pow2(k)) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      N.le_lt_trans(1n+p, SC.pow2(p), Nat.double(SC.pow2(p)), N.lt_succ_le_succ(p, SC.pow2(p), pow2_gt(p)), N.pow2_lt_succ(p))
