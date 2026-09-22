import Base
import ../../src/dynamic_array.bend as DA
import ../../types/dynamic_array.bend as E

type Box is Data:
  Box{v: U32}

def gb(r: DA.DynArray<&2, Box> & Result<&2, &2, E.Error, Box>) -> String:
  (d, x) = r
  match x:
    case Fail{e}:
      "fail"
    case Done{Box{s}}:
      U32.show(s)

def pb(r: DA.DynArray<&2, Box> & Result<&2, &2, E.Error, Unit>) -> String:
  (d, u) = r
  gb(DA.get(Box, d, 0n))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(pb(DA.push(Box, DA.new(Box), Box{5})))
