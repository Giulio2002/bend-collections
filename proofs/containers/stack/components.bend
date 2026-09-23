import Base
import ./proof.bend as P
import ../../../src/containers/stack.bend as D
import ./spec.bend as S
import ../../../src/containers/types/stack.bend as E

def step_u32(+xs: List<&2, U32>, +op: E.Op<U32>) -> {D.step(~U32, P.real(~U32, xs), op) == P.lift(~U32, S.step(U32, xs, op)) : D.Stack<U32> & E.Obs<U32>}:
  P.step_correct(~U32, xs, op)

def step_string(+xs: List<&2, String>, +op: E.Op<String>) -> {D.step(~String, P.real(~String, xs), op) == P.lift(~String, S.step(String, xs, op)) : D.Stack<String> & E.Obs<String>}:
  P.step_correct(~String, xs, op)

def new_u32() -> {D.new(~U32) == P.real(~U32, Nil{}) : D.Stack<U32>}:
  P.constructor(~U32)

def new_string() -> {D.new(~String) == P.real(~String, Nil{}) : D.Stack<String>}:
  P.constructor(~String)
