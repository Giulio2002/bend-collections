import Base
import ./buffer.bend as Buffer

# Sole production hash API. Packed input and output, four bytes per U32,
# big-endian. Consumes input; returns exactly eight words, or None for an
# oversized byte length. No byte-list or digest-list compatibility API.
def sha256(words: Array<U32>, byte_length: Nat) -> Maybe<&1,Array<U32>>:
  Buffer.sha256(words,byte_length)

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

def hex_word(x: U32) -> String:
  hex_word_go(8n, x, "")

# Formatting helper consumes eight words; it does not create a digest list.
def hex_walk(n: Nat, +index: U32, pair: Array<U32> & U32) -> String:
  match n pair:
    case 0n Tuple{a,w}: hex_word(w)
    case 1n+p Tuple{a,w}: hex_word(w) ++ hex_walk(p,U32.inc(index),Array.get(U32,a,index))

def hex(a: Array<U32>) -> String:
  hex_walk(7n,1,Array.get(U32,a,0))
