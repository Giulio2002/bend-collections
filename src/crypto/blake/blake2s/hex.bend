import Base

def hex_digit_if(x: U32, small: Bool) -> Char:
  match small:
    case True{}:
      Chr{(48 + x : U32)}
    case False{}:
      Chr{(87 + x : U32)}

def hex_digit(+x: U32) -> Char:
  hex_digit_if(x, U32.is_lt(x, 10))

def hex_word_go(n: Nat, +x: U32, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+p:
      hex_word_go(p, U32.shrn(x, 4n), SCon{hex_digit((x .&. 15 : U32)), acc})

def hex_byte(+x: U32) -> String:
  SCon{hex_digit(U32.shrn(x,4n)),SCon{hex_digit(U32.and(x,15)),SNil{}}}

def hex_word(+x: U32) -> String:
  hex_byte(U32.and(x,255)) ++ hex_byte(U32.and(U32.shrn(x,8n),255)) ++ hex_byte(U32.and(U32.shrn(x,16n),255)) ++ hex_byte(U32.shrn(x,24n))

# Formatting helper consumes eight words; it does not create a digest list.
def hex_walk(n: Nat, +index: U32, pair: Array<U32> & U32) -> String:
  match n pair:
    case 0n Tuple{a,w}: hex_word(w)
    case 1n+p Tuple{a,w}: hex_word(w) ++ hex_walk(p,U32.inc(index),Array.get(U32,a,index))

def hex(a: Array<U32>) -> String:
  hex_walk(7n,1,Array.get(U32,a,0))
