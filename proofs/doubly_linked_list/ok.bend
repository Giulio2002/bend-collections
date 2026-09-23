import Base
import ../lib/logic.bend as L
import ../spec/doubly_linked_list.bend as S
import ../../src/containers/doubly_linked_list.bend as D
import ./state.bend as ST

# The refinement statement of one step: the implementation's result is the
# real list of a new shadow with an observation, the specification's the
# shadow's model with the same observation, and the shadow is good.

def POK(~T: Data, -X: Data, spec: S.DS<T> & X, r: D.DList<T> & X) -> Type:
  Sigma<&1, &1, ST.Sh<T>, sh2 => Sigma<&1, &1, X, o => {r == (ST.real(~T, sh2), o) : D.DList<T> & X} & ({spec == (ST.model(~T, sh2), o) : S.DS<T> & X} & {ST.good(~T, sh2) == True{} : Bool})>>

# both results rewritten
def pok_eq(~T: Data, -X: Data, -spec: S.DS<T> & X, -spec2: S.DS<T> & X, -r: D.DList<T> & X, -r2: D.DList<T> & X, +es: {spec == spec2 : S.DS<T> & X}, +er: {r == r2 : D.DList<T> & X}, p: POK(~T, X, spec2, r2)) -> POK(~T, X, spec, r):
  p1 = L.subst(D.DList<T> & X, z => POK(~T, X, spec2, z), r2, r, Equal.sym(D.DList<T> & X, r, r2, er), p)
  L.subst(S.DS<T> & X, z => POK(~T, X, z, r), spec2, spec, Equal.sym(S.DS<T> & X, spec, spec2, es), p1)
