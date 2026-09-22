import Base
import ../../spec/lru_fast.bend as S
import ../../src/lru/fast.bend as F
import ../../types/lru_model.bend as T
import ./state.bend as ST

# Checked instantiations of the (template) fast-LRU proofs at V = U32, for
# fast local checking; END_TO_END.bend states the public laws at concrete
# value types.

def i_new_real(+cap: U32) -> {F.init(~U32, cap) == ST.real(~U32, ST.initial(~U32, cap)) : F.Fast<U32>}:
  ST.new_real(~U32, cap)

def i_new_model(+cap: U32) -> {ST.model(~U32, ST.initial(~U32, cap)) == S.LM{cap, S.zero_time(), Nil{}, T.zero_metrics()} : S.Model<U32>}:
  ST.new_model(~U32, cap)

def i_new_good(+cap: U32, +hc: {U32.is_eq(cap, 0) == False{} : Bool}) -> {ST.good(~U32, ST.initial(~U32, cap)) == True{} : Bool}:
  ST.new_good(~U32, cap, hc)
