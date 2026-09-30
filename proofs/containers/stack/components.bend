import Base
import ./proof.bend as P
import ./chunks.bend as K
import ../../../src/containers/stack.bend as D
import ../../../spec/containers/stack.bend as S
import ../../../src/containers/types/stack.bend as E

def step_u32(+sh: K.Sh<U32>, +op: E.Op<U32>, +g: {K.good(U32, sh) == True{} : Bool}) -> {P.view1(~U32, D.step(~U32, K.real(~U32, sh), op)) == S.step(U32, K.model(U32, sh), op) : List<&2, U32> & E.Obs<U32>}:
  P.step_refines(~U32, sh, op, g)

def step_string(+sh: K.Sh<String>, +op: E.Op<String>, +g: {K.good(String, sh) == True{} : Bool}) -> {P.view1(~String, D.step(~String, K.real(~String, sh), op)) == S.step(String, K.model(String, sh), op) : List<&2, String> & E.Obs<String>}:
  P.step_refines(~String, sh, op, g)

def new_u32() -> {D.new(~U32) == K.real(~U32, K.SSE{}) : D.Stack<U32>} & ({K.good(U32, K.SSE{}) == True{} : Bool} & {K.model(U32, K.SSE{}) == Nil{} : List<&2, U32>}):
  P.constructor(~U32)

def new_string() -> {D.new(~String) == K.real(~String, K.SSE{}) : D.Stack<String>} & ({K.good(String, K.SSE{}) == True{} : Bool} & {K.model(String, K.SSE{}) == Nil{} : List<&2, String>}):
  P.constructor(~String)
