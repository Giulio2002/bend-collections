import Base
import ../../lib/logic.bend as L
import ./spec.bend as S
import ../../../src/containers/balanced_search_tree.bend as M
import ./state.bend as ST
import ./mirror.bend as MI

# The refinement statement of one operation: the implementation's result is
# the real map of a good shadow with an answer, the specification's the
# shadow's model with the same answer. (source: tools/generators/tm_hand/ok.src)


def POK(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, -X: Data, spec: S.Model<K, V> & X, r: M.TreeMap<K, V, cmp> & X) -> Type:
  Sigma<&1, &1, ST.Sh<K, V>, sh2 => Sigma<&1, &1, X, o => {r == (ST.real(~K, ~V, ~cmp, sh2), o) : M.TreeMap<K, V, cmp> & X} & ({spec == (ST.model(~K, ~V, ~cmp, sh2), o) : S.Model<K, V> & X} & {ST.good(~K, ~V, ~cmp, sh2) == True{} : Bool})>>

def pok_eq(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, -X: Data, -spec: S.Model<K, V> & X, -spec2: S.Model<K, V> & X, -r: M.TreeMap<K, V, cmp> & X, -r2: M.TreeMap<K, V, cmp> & X, +es: {spec == spec2 : S.Model<K, V> & X}, +er: {r == r2 : M.TreeMap<K, V, cmp> & X}, p: POK(~K, ~V, ~cmp, X, spec2, r2)) -> POK(~K, ~V, ~cmp, X, spec, r):
  p1 = L.subst(M.TreeMap<K, V, cmp> & X, z => POK(~K, ~V, ~cmp, X, spec2, z), r2, r, Equal.sym(M.TreeMap<K, V, cmp> & X, r, r2, er), p)
  L.subst(S.Model<K, V> & X, z => POK(~K, ~V, ~cmp, X, z, r), spec2, spec, Equal.sym(S.Model<K, V> & X, spec, spec2, es), p1)

# the layout facts the simulation needs, from the invariant
def dg_good(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +sh: ST.Sh<K, V>, +hg: {ST.good(~K, ~V, ~cmp, sh) == True{} : Bool}) -> {MI.dg(K, V, sh) == True{} : Bool}:
  match sh:
    case ST.SH{+n, +root, +lo, +hi, +free, +l, +d, +nl, +pl, +t, +fl}:
      L.and_intro(ST.cl(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, t, fl), Bool.and(ST.cd(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, t, fl), Bool.and(ST.ccap(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, t, fl), ST.cpl(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, t, fl))), ST.g_cl(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, t, fl, hg), L.and_intro(ST.cd(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, t, fl), Bool.and(ST.ccap(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, t, fl), ST.cpl(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, t, fl)), ST.g_cd(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, t, fl, hg), L.and_intro(ST.ccap(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, t, fl), ST.cpl(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, t, fl), ST.g_ccap(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, t, fl, hg), ST.g_cpl(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, t, fl, hg))))

# a read-only operation: the same shadow, the answer of both
def pok_read(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, -X: Data, +sh: ST.Sh<K, V>, +hg: {ST.good(~K, ~V, ~cmp, sh) == True{} : Bool}, +o: X, -spec: S.Model<K, V> & X, -r: M.TreeMap<K, V, cmp> & X, +es: {spec == (ST.model(~K, ~V, ~cmp, sh), o) : S.Model<K, V> & X}, +er: {r == (ST.real(~K, ~V, ~cmp, sh), o) : M.TreeMap<K, V, cmp> & X}) -> POK(~K, ~V, ~cmp, X, spec, r):
  (sh, (o, (er, (es, hg))))

# the refinement of a mirror result: its real map and answer are a good
# shadow's, whose model and the answer are the specification's
def MOK(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, -X: Data, spec: S.Model<K, V> & X, mir: ST.Sh<K, V> & X) -> Type:
  Sigma<&1, &1, ST.Sh<K, V>, sh2 => Sigma<&1, &1, X, o => {MI.rp(~K, ~V, ~cmp, X, mir) == (ST.real(~K, ~V, ~cmp, sh2), o) : M.TreeMap<K, V, cmp> & X} & ({spec == (ST.model(~K, ~V, ~cmp, sh2), o) : S.Model<K, V> & X} & {ST.good(~K, ~V, ~cmp, sh2) == True{} : Bool})>>

def mok_eq(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, -X: Data, -spec: S.Model<K, V> & X, -mir: ST.Sh<K, V> & X, -mir2: ST.Sh<K, V> & X, +e: {mir == mir2 : ST.Sh<K, V> & X}, p: MOK(~K, ~V, ~cmp, X, spec, mir2)) -> MOK(~K, ~V, ~cmp, X, spec, mir):
  L.subst(ST.Sh<K, V> & X, z => MOK(~K, ~V, ~cmp, X, spec, z), mir2, mir, Equal.sym(ST.Sh<K, V> & X, mir, mir2, e), p)

# a mirror refinement and the simulation give the implementation's
def mok_pok(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, -X: Data, -spec: S.Model<K, V> & X, -mir: ST.Sh<K, V> & X, -r: M.TreeMap<K, V, cmp> & X, +hs: {r == MI.rp(~K, ~V, ~cmp, X, mir) : M.TreeMap<K, V, cmp> & X}, p: MOK(~K, ~V, ~cmp, X, spec, mir)) -> POK(~K, ~V, ~cmp, X, spec, r):
  match p:
    case Tuple{+sh2, Tuple{+o, Tuple{+h1, rest}}}:
      (sh2, (o, (Equal.trans(M.TreeMap<K, V, cmp> & X, r, MI.rp(~K, ~V, ~cmp, X, mir), (ST.real(~K, ~V, ~cmp, sh2), o), hs, h1), rest)))
