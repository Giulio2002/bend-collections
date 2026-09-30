import Base

# Hex helpers for the crypto tests: bytes are U32 values 0..255.

def nibble_if(+c: U32, digit: Bool) -> U32:
  match digit:
    case True{}:
      (c - 48 : U32)
    case False{}:
      (c - 87 : U32)

def nibble(+c: U32) -> U32:
  nibble_if(c, U32.is_lt(c, 58))

# Lower-case hex text to bytes.
def unhex(s: String) -> List<&2, U32>:
  match s:
    case SCon{Chr{+a}, SCon{Chr{+b}, t}}:
      ((nibble(a) * 16) + nibble(b) : U32) <> unhex(t)
    case _:
      Nil{}

def digit_if(x: U32, small: Bool) -> Char:
  match small:
    case True{}:
      Chr{(48 + x : U32)}
    case False{}:
      Chr{(87 + x : U32)}

def digit(+x: U32) -> Char:
  digit_if(x, U32.is_lt(x, 10))

def hex(bs: List<&2, U32>) -> String:
  match bs:
    case Nil{}:
      ""
    case +b <> t:
      SCon{digit(U32.and(U32.shrn(b, 4n), 15)), SCon{digit(U32.and(b, 15)), hex(t)}}

def replicate(n: Nat, +b: U32) -> List<&2, U32>:
  List.replicate(U32, n, b)

def ascii(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{c}, t}:
      c <> ascii(t)

def check_if(name: String, got: String, want: String, ok: Bool) -> IO(Unit):
  match ok:
    case True{}:
      IO.print("ok " ++ name)
    case False{}:
      IO.print("FAIL " ++ name ++ " got " ++ got ++ " want " ++ want)

def check(name: String, +got: String, +want: String) -> IO(Unit):
  check_if(name, got, want, String.eq(got, want))

def show_bool(b: Bool) -> String:
  match b:
    case True{}:
      "true"
    case False{}:
      "false"
