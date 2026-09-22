import Base
import ./mu0.bend as MU0
import ./retarget.bend as RT
import ../lib/u32.bend as U
import ../graph/shift.bend as SH
import ../../types/doubly_linked_list.bend as E
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/array.bend as AR
import ../../spec/common.bend as SC
import ../../spec/doubly_linked_list.bend as DS
import ../../src/doubly_linked_list.bend as D
import ./state.bend as ST
import ./links.bend as LK
import ./split.bend as SP
import ./reuse_insert.bend as RI
import ./free_chain.bend as SELF

def new_good_u32() -> {SELF.good(~U32, SELF.initial(~U32)) == True{} : Bool}:
  SELF.new_good(~U32)

def new_real_u32() -> {SELF.real(~U32, SELF.initial(~U32)) == D.new(~U32, 0) : D.DList<U32>}:
  SELF.new_real(~U32)

def new_good_string() -> {SELF.good(~String, SELF.initial(~String)) == True{} : Bool}:
  SELF.new_good(~String)

def new_real_string() -> {SELF.real(~String, SELF.initial(~String)) == D.new(~String, 0) : D.DList<String>}:
  SELF.new_real(~String)

