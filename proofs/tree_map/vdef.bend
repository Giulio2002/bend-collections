import Base
import ../lib/logic.bend as L
import ../spec/tree_map.bend as S
import ../../src/containers/balanced_search_tree.bend as M
import ./state.bend as ST
import ./mirror.bend as MI
import ./ok.bend as OK

# A view's model and invariant, and the refinement of view results.
# (source: tools/generators/tm_hand/vdef.src)


# ---- a view's model and invariant ----

def vmod(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, w: MI.MView<K, V>) -> S.View<K, V>:
  match w:
    case MI.MV{s, lo2, hi2, d2}:
      S.VW{ST.model(~K, ~V, ~cmp, s), lo2, hi2, d2}

def vgood(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, w: MI.MView<K, V>) -> Bool:
  match w:
    case MI.MV{s, lo2, hi2, d2}:
      ST.good(~K, ~V, ~cmp, s)

def vg_dg(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +w: MI.MView<K, V>, +h: {vgood(~K, ~V, ~cmp, w) == True{} : Bool}) -> {MI.dgv(K, V, w) == True{} : Bool}:
  match w:
    case MI.MV{+s, +lo2, +hi2, +d2}:
      OK.dg_good(~K, ~V, ~cmp, s, h)

# a view refining a specification's
def VOK(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, sp: S.View<K, V>, r: M.View<K, V, cmp>) -> Type:
  Sigma<&1, &1, MI.MView<K, V>, w2 => {r == MI.rv(~K, ~V, ~cmp, w2) : M.View<K, V, cmp>} & ({sp == vmod(~K, ~V, ~cmp, w2) : S.View<K, V>} & {vgood(~K, ~V, ~cmp, w2) == True{} : Bool})>

# a mirror view result refining a specification's
def VM(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, -X: Data, sp: S.View<K, V> & X, mir: MI.MView<K, V> & X) -> Type:
  Sigma<&1, &1, MI.MView<K, V>, w2 => Sigma<&1, &1, X, o => {MI.rvp(~K, ~V, ~cmp, X, mir) == (MI.rv(~K, ~V, ~cmp, w2), o) : M.View<K, V, cmp> & X} & ({sp == (vmod(~K, ~V, ~cmp, w2), o) : S.View<K, V> & X} & {vgood(~K, ~V, ~cmp, w2) == True{} : Bool})>>

# an implementation view result refining a specification's
def VPOK(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, -X: Data, sp: S.View<K, V> & X, r: M.View<K, V, cmp> & X) -> Type:
  Sigma<&1, &1, MI.MView<K, V>, w2 => Sigma<&1, &1, X, o => {r == (MI.rv(~K, ~V, ~cmp, w2), o) : M.View<K, V, cmp> & X} & ({sp == (vmod(~K, ~V, ~cmp, w2), o) : S.View<K, V> & X} & {vgood(~K, ~V, ~cmp, w2) == True{} : Bool})>>

def vm_pok(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, -X: Data, -sp: S.View<K, V> & X, -mir: MI.MView<K, V> & X, -r: M.View<K, V, cmp> & X, +hs: {r == MI.rvp(~K, ~V, ~cmp, X, mir) : M.View<K, V, cmp> & X}, p: VM(~K, ~V, ~cmp, X, sp, mir)) -> VPOK(~K, ~V, ~cmp, X, sp, r):
  match p:
    case Tuple{+w2, Tuple{+o, Tuple{+h1, rest}}}:
      (w2, (o, (Equal.trans(M.View<K, V, cmp> & X, r, MI.rvp(~K, ~V, ~cmp, X, mir), (MI.rv(~K, ~V, ~cmp, w2), o), hs, h1), rest)))

# a mirror result given exactly
def vm_exact(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, -X: Data, -sp: S.View<K, V> & X, -mir: MI.MView<K, V> & X, +w2: MI.MView<K, V>, +o: X, +hm: {mir == (w2, o) : MI.MView<K, V> & X}, +hs: {sp == (vmod(~K, ~V, ~cmp, w2), o) : S.View<K, V> & X}, +hg: {vgood(~K, ~V, ~cmp, w2) == True{} : Bool}) -> VM(~K, ~V, ~cmp, X, sp, mir):
  (w2, (o, (L.subst(MI.MView<K, V> & X, z => {MI.rvp(~K, ~V, ~cmp, X, z) == (MI.rv(~K, ~V, ~cmp, w2), o) : M.View<K, V, cmp> & X}, (w2, o), mir, Equal.sym(MI.MView<K, V> & X, mir, (w2, o), hm), {==}), (hs, hg))))

