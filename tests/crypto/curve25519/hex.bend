import Base

# Hex transport for the curve25519 test drivers (test-only).

def nib_if(c: U32, digit: Bool, upper: Bool) -> U32:
  match digit:
    case True{}:
      U32.sub(c, 48)
    case False{}:
      match upper:
        case True{}:
          U32.sub(c, 55)
        case False{}:
          U32.sub(c, 87)

def nib(+c: U32) -> U32:
  nib_if(c, U32.is_lt(c, 58), U32.is_lt(c, 71))

def code(c: Char) -> U32:
  match c:
    case Chr{x}:
      x

# "a5c1..." to bytes; an odd trailing digit is dropped
def bytes(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{a, t}:
      match t:
        case SNil{}:
          Nil{}
        case SCon{b, r}:
          Con{U32.add(U32.mul(nib(code(a)), 16), nib(code(b))), bytes(r)}

def digit_if(x: U32, small: Bool) -> Char:
  match small:
    case True{}:
      Chr{U32.add(48, x)}
    case False{}:
      Chr{U32.add(87, x)}

def digit(+x: U32) -> Char:
  digit_if(x, U32.is_lt(x, 10))

def show(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      SNil{}
    case Con{+x, t}:
      SCon{digit(U32.div(x, 16)), SCon{digit(U32.mod(x, 16)), show(t)}}
