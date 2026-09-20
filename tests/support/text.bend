import Base

# Transport helpers for test drivers: argv tokens "op:a:b" -> fields, and
# rendering of observations. Test-only; never imported by src/ or proofs/.

def field(parts: List<&2, String>, i: Nat) -> String:
  match parts i:
    case Nil{} _:
      ""
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+p:
      field(t, p)

def fields(s: String) -> List<&2, String>:
  String.split(s, ':')

def nat_of(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def u32_of(s: String) -> U32:
  Maybe.default(&2, U32, U32.read(s), 0)

def nat_field(parts: List<&2, String>, i: Nat) -> Nat:
  nat_of(field(parts, i))

def u32_field(parts: List<&2, String>, i: Nat) -> U32:
  u32_of(field(parts, i))

def join_u32(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      match t:
        case Nil{}:
          U32.show(h)
        case Con{h2, t2}:
          U32.show(h) ++ "," ++ join_u32(Con{h2, t2})

def join_nat(xs: List<&2, Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      match t:
        case Nil{}:
          Nat.show(h)
        case Con{h2, t2}:
          Nat.show(h) ++ "," ++ join_nat(Con{h2, t2})

def print_lines(xs: List<&2, String>) -> IO(Unit):
  match xs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{h, t}:
      IO.bind(Unit, Unit, IO.print(h), u => print_lines(t))

def shared(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{h, shared(t)}
