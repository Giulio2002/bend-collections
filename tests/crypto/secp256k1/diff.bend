import Base
import ../../../src/crypto/secp256k1.bend as K
import ../bytes.bend as B

# Differential driver for tools/check_secp256k1.py. Reads FUZZ_COUNT records
# from the file FUZZ_INPUT and prints one line per record. A record is an
# op byte then its fields, each a 4-byte little-endian length and that many
# bytes:
#   0 sk hash          sign_compact      -> hex r||s||v | none
#   1 pk hash sig      verify            -> true | false
#   2 pk hash sig      verify_strict     -> true | false
#   3 hash sig         recover           -> hex pk | none
#   4 sk flag          public_key        -> hex pk | none (flag [1]: compressed)
#   5 pk               eth_address       -> hex | none
#   6 sk msg aux       schnorr_sign      -> hex sig | none
#   7 pk msg sig       schnorr_verify    -> true | false
#   8 sk               schnorr_pubkey    -> hex | none
#   9 input            ecrecover         -> hex word | none

def pack(+b0: U32, +b1: U32, +b2: U32, +b3: U32) -> U32:
  U32.or(U32.or(b0, U32.shln(b1, 8n)), U32.or(U32.shln(b2, 16n), U32.shln(b3, 24n)))

def w3(+b0: U32, +b1: U32, +b2: U32, bs: List<&2, U32>) -> U32 & List<&2, U32>:
  match bs:
    case Nil{}: (pack(b0, b1, b2, 0), Nil{})
    case h <> t: (pack(b0, b1, b2, h), t)

def w2(+b0: U32, +b1: U32, bs: List<&2, U32>) -> U32 & List<&2, U32>:
  match bs:
    case Nil{}: (pack(b0, b1, 0, 0), Nil{})
    case h <> t: w3(b0, b1, h, t)

def w1(+b0: U32, bs: List<&2, U32>) -> U32 & List<&2, U32>:
  match bs:
    case Nil{}: (pack(b0, 0, 0, 0), Nil{})
    case h <> t: w2(b0, h, t)

def word(bs: List<&2, U32>) -> U32 & List<&2, U32>:
  match bs:
    case Nil{}: (0, Nil{})
    case h <> t: w1(h, t)

def take(n: Nat, bs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32> & List<&2, U32>:
  match n bs:
    case 0n _: (List.reverse(&2, U32, acc), bs)
    case 1n+p Nil{}: (List.reverse(&2, U32, acc), Nil{})
    case 1n+p h <> t: take(p, t, h <> acc)

def field_of(pair: U32 & List<&2, U32>) -> List<&2, U32> & List<&2, U32>:
  (n, rest) = pair
  take(U32.to_nat(n), rest, Nil{})

def field(bs: List<&2, U32>) -> List<&2, U32> & List<&2, U32>:
  field_of(word(bs))

def show(m: Maybe<&2, List<&2, U32>>) -> String:
  match m:
    case None{}: "none"
    case Some{b}: B.hex(b)

def flag(bs: List<&2, U32>) -> Bool:
  match bs:
    case Nil{}: False{}
    case b <> t: U32.is_eq(b, 1)

# ops by their field count, the fields in order
def op1(op: Nat, +a: List<&2, U32>) -> String:
  match op:
    case 5n: show(K.eth_address(a))
    case 8n: show(K.schnorr_pubkey(a))
    case 9n: show(K.ecrecover(a))
    case _: "bad op"

def op2(op: Nat, +a: List<&2, U32>, +b: List<&2, U32>) -> String:
  match op:
    case 0n: show(K.sign_compact(a, b))
    case 3n: show(K.recover(a, b))
    case 4n: show(K.public_key(a, flag(b)))
    case _: "bad op"

def op3(op: Nat, +a: List<&2, U32>, +b: List<&2, U32>, +c: List<&2, U32>) -> String:
  match op:
    case 1n: B.show_bool(K.verify(a, b, c))
    case 2n: B.show_bool(K.verify_strict(a, b, c))
    case 6n: show(K.schnorr_sign(a, b, c))
    case 7n: B.show_bool(K.schnorr_verify(a, b, c))
    case _: "bad op"

def arity(op: Nat) -> Nat:
  match op:
    case 5n: 1n
    case 8n: 1n
    case 9n: 1n
    case 0n: 2n
    case 3n: 2n
    case 4n: 2n
    case _: 3n

def f3(op: Nat, +a: List<&2, U32>, +b: List<&2, U32>, p: List<&2, U32> & List<&2, U32>) -> String & List<&2, U32>:
  (c, rest) = p
  (op3(op, a, b, c), rest)

def g2(op: Nat, +a: List<&2, U32>, p: List<&2, U32> & List<&2, U32>) -> String & List<&2, U32>:
  (b, rest) = p
  (op2(op, a, b), rest)

def g3(op: Nat, +a: List<&2, U32>, p: List<&2, U32> & List<&2, U32>) -> String & List<&2, U32>:
  (b, rest) = p
  f3(op, a, b, field(rest))

def f2(n: Nat, op: Nat, +a: List<&2, U32>, p: List<&2, U32> & List<&2, U32>) -> String & List<&2, U32>:
  match n:
    case 2n: g2(op, a, p)
    case _: g3(op, a, p)

def h1(op: Nat, p: List<&2, U32> & List<&2, U32>) -> String & List<&2, U32>:
  (a, rest) = p
  (op1(op, a), rest)

def hn(k: Nat, op: Nat, p: List<&2, U32> & List<&2, U32>) -> String & List<&2, U32>:
  (a, rest) = p
  f2(k, op, a, field(rest))

def f1n(k: Nat, op: Nat, p: List<&2, U32> & List<&2, U32>) -> String & List<&2, U32>:
  match k:
    case 1n: h1(op, p)
    case _: hn(k, op, p)

def f1(+op: Nat, p: List<&2, U32> & List<&2, U32>) -> String & List<&2, U32>:
  f1n(arity(op), op, p)

def one(bs: List<&2, U32>) -> String & List<&2, U32>:
  match bs:
    case Nil{}: ("", Nil{})
    case op <> t: f1(U32.to_nat(op), field(t))

def loaded(pair: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(List<&2, U32>):
  (file, result) = pair
  do IO<List<&2, U32>>:
    File.close(file)
    IO.pass(List<&2, U32>, result)

def count(r: Maybe<&2, Nat>) -> Nat:
  match r:
    case None{}: 0n
    case Some{n}: n

def records(n: Nat, pair: String & List<&2, U32>) -> IO(Unit):
  match n:
    case 1n:
      (s, rest) = pair
      IO.print(s)
    case 2n+p:
      (s, rest) = pair
      do IO<Unit>:
        IO.print(s)
        records(1n+p, one(rest))
    case 0n:
      (s, rest) = pair
      IO.pure(Unit, Unit{})

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("FUZZ_INPUT"))
    nt : String <- IO.try(String, IO.get_env("FUZZ_COUNT"))
    file : File <- IO.try(File, File.open(path, "r"))
    pair : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(file, 268435456)
    bytes : List<&2, U32> <- loaded(pair)
    records(count(Nat.read(nt)), one(bytes))
