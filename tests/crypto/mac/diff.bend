import Base
import ../../../src/crypto/mac.bend as MAC
import ../../../src/crypto/kdf.bend as KDF
import ../bytes.bend as B

# Differential driver for tools/check_mac.py. Reads FUZZ_COUNT records from
# the file FUZZ_INPUT and prints one line per record. A record is an op byte
# then its fields, each a 4-byte little-endian length and that many bytes;
# the HKDF ops end with a 4-byte output length:
#   0 key msg            sign        -> hex tag
#   1 key msg tag        verify      -> true | false
#   2 salt ikm info L    hkdf        -> hex okm | LengthTooLarge
#   3 prk info L         expand      -> hex okm | LengthTooLarge
#   4 salt ikm           extract     -> hex prk

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

def show(r: Result<&2, &2, KDF.KdfError, List<&2, U32>>) -> String:
  match r:
    case Fail{e}:
      "LengthTooLarge"
    case Done{okm}:
      B.hex(okm)

def op_sign(+key: List<&2, U32>, p: List<&2, U32> & List<&2, U32>) -> String & List<&2, U32>:
  (msg, rest) = p
  (B.hex(MAC.sign(key, msg)), rest)

def op_verify3(+key: List<&2, U32>, +msg: List<&2, U32>, p: List<&2, U32> & List<&2, U32>) -> String & List<&2, U32>:
  (tag, rest) = p
  (B.show_bool(MAC.verify(key, msg, tag)), rest)

def op_verify(+key: List<&2, U32>, p: List<&2, U32> & List<&2, U32>) -> String & List<&2, U32>:
  (msg, rest) = p
  op_verify3(key, msg, field(rest))

def op_hkdf4(+salt: List<&2, U32>, +ikm: List<&2, U32>, +info: List<&2, U32>, p: U32 & List<&2, U32>) -> String & List<&2, U32>:
  (len, rest) = p
  (show(KDF.hkdf(salt, ikm, info, U32.to_nat(len))), rest)

def op_hkdf3(+salt: List<&2, U32>, +ikm: List<&2, U32>, p: List<&2, U32> & List<&2, U32>) -> String & List<&2, U32>:
  (info, rest) = p
  op_hkdf4(salt, ikm, info, word(rest))

def op_hkdf(+salt: List<&2, U32>, p: List<&2, U32> & List<&2, U32>) -> String & List<&2, U32>:
  (ikm, rest) = p
  op_hkdf3(salt, ikm, field(rest))

def op_expand3(+prk: List<&2, U32>, +info: List<&2, U32>, p: U32 & List<&2, U32>) -> String & List<&2, U32>:
  (len, rest) = p
  (show(KDF.expand(prk, info, U32.to_nat(len))), rest)

def op_expand(+prk: List<&2, U32>, p: List<&2, U32> & List<&2, U32>) -> String & List<&2, U32>:
  (info, rest) = p
  op_expand3(prk, info, word(rest))

def op_extract(+salt: List<&2, U32>, p: List<&2, U32> & List<&2, U32>) -> String & List<&2, U32>:
  (ikm, rest) = p
  (B.hex(KDF.extract(salt, ikm)), rest)

def dispatch(op: Nat, +first: List<&2, U32>, rest: List<&2, U32>) -> String & List<&2, U32>:
  match op:
    case 0n:
      op_sign(first, field(rest))
    case 1n:
      op_verify(first, field(rest))
    case 2n:
      op_hkdf(first, field(rest))
    case 3n:
      op_expand(first, field(rest))
    case 4n:
      op_extract(first, field(rest))
    case _:
      ("bad op", Nil{})

def split(op: Nat, p: List<&2, U32> & List<&2, U32>) -> String & List<&2, U32>:
  (first, rest) = p
  dispatch(op, first, rest)

def one(bs: List<&2, U32>) -> String & List<&2, U32>:
  match bs:
    case Nil{}: ("", Nil{})
    case op <> t: split(U32.to_nat(op), field(t))

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
