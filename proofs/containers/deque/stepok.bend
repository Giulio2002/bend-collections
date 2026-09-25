import Base
import ../../../spec/containers/deque.bend as S
import ../../../src/containers/deque.bend as DQ
import ../../../src/containers/types/deque.bend as E
import ./state.bend as ST

# StepOK(sh, op): the public step on the deque of shadow sh lands on the
# deque of a shadow sh2 and emits o, and (model(sh2), o) is exactly the spec
# step on model(sh).

def StepOK(~T: Data, sh: ST.Shadow<T>, op: E.Op<T>) -> Type:
  Sigma<&1, &1, ST.Shadow<T>, sh2 => Sigma<&1, &1, E.Obs<T>, o => {DQ.step(~T, ST.real(T, sh), op) == (ST.real(T, sh2), o) : DQ.Deque<T> & E.Obs<T>} & {(ST.model(T, sh2), o) == S.step(T, ST.model(T, sh), op) : List<&2, T> & E.Obs<T>}>>

def mk(~T: Data, -sh: ST.Shadow<T>, -op: E.Op<T>, sh2: ST.Shadow<T>, o: E.Obs<T>, e1: {DQ.step(~T, ST.real(T, sh), op) == (ST.real(T, sh2), o) : DQ.Deque<T> & E.Obs<T>}, e2: {(ST.model(T, sh2), o) == S.step(T, ST.model(T, sh), op) : List<&2, T> & E.Obs<T>}) -> StepOK(~T, sh, op):
  (sh2, (o, (e1, e2)))
