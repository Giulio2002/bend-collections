import Base
import ../../src/lru/fast.bend as F
import ./state.bend as ST
import ./inj.bend as IJ

def real_inj_u32(a: ST.Shadow<U32>, +b: ST.Shadow<U32>, +ga: {ST.good(~U32, a) == True{} : Bool}, +gb: {ST.good(~U32, b) == True{} : Bool}, +e: {ST.real(~U32, a) == ST.real(~U32, b) : F.Fast<U32>}) -> {a == b : ST.Shadow<U32>}:
  IJ.real_inj(~U32, a, b, ga, gb, e)
