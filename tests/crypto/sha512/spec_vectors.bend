import Base
import ../../../spec/crypto/sha512.bend as S

def hexd_if(x: U32, small: Bool) -> Char:
  match small:
    case True{}:
      Chr{(48 + x : U32)}
    case False{}:
      Chr{(87 + x : U32)}

def hexd(+x: U32) -> Char:
  hexd_if(x, U32.is_lt(x, 10))

def hex(bs: List<&2, U32>) -> String:
  match bs:
    case Nil{}:
      ""
    case +b <> t:
      SCon{hexd(U32.shrn(b, 4n)), SCon{hexd(U32.and(b, 15)), hex(t)}}

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(hex(S.sha512_bytes([])))
    IO.print(hex(S.sha512_bytes([97, 98, 99])))
