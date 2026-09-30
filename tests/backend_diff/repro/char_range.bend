import Base

# docs/BACKEND_BUGS.md, "char-range". A Char is `Chr{code: U32}`: every U32 is
# a Char in the source language, and every proof about String quantifies over
# such strings. The native build prints "1 55296"; `bend char_range.bend` and
# the JavaScript build stop with "55296 is not a Unicode scalar value" (the
# same for every code in 0xD800..0xDFFF and above 0x10FFFF).

def codes(s: String) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{Chr{c}, t}:
      " " ++ U32.show(c) ++ codes(t)

def show(+s: String) -> String:
  Nat.show(String.length(s)) ++ codes(s)

def main() -> IO(Unit):
  IO.print(show(SCon{Chr{55296}, SNil{}}))
