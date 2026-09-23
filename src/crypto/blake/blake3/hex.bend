import Base

def hex_digit_if(x: U32, small: Bool) -> Char:
  match small:
    case True{}:
      Chr{(48 + x : U32)}
    case False{}:
      Chr{(87 + x : U32)}

def hex_digit(+x: U32) -> Char:
  hex_digit_if(x, U32.is_lt(x, 10))

def hex_byte(+x: U32) -> String:
  SCon{hex_digit(U32.shrn(x,4n)),SCon{hex_digit(U32.and(x,15)),SNil{}}}

def hex_word(+x: U32) -> String:
  hex_byte(U32.and(x,255)) ++ hex_byte(U32.and(U32.shrn(x,8n),255)) ++ hex_byte(U32.and(U32.shrn(x,16n),255)) ++ hex_byte(U32.shrn(x,24n))

def hex_walk(n: Nat, +index: U32, pair: Array<U32> & U32) -> String:
  match n pair:
    case 0n Tuple{a,w}: hex_word(w)
    case 1n+p Tuple{a,w}: hex_word(w) ++ hex_walk(p,U32.inc(index),Array.get(U32,a,index))

# The digest words as lowercase hex, bytes in little-endian word order.
def hex(a: Array<U32>) -> String:
  hex_walk(7n,1,Array.get(U32,a,0))
