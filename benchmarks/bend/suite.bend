import Base

# Shared scaffolding of the benchmarks/bend/suite_*.bend drivers
# (benchmarks/crypto_suite.py; benchmarks/native/suite.h is the C side).
# Trusted measurement code: input loading and message construction precede
# the timed region, the checksum follows it.

# Cut a byte list into messages of +size bytes, in order.
def chunks(xs: List<&2, U32>, +size: Nat, left: Nat,
    acc: List<&2, U32>, out: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs left:
    case Nil{} _:
      List.reverse(&2, List<&2, U32>, List.reverse(&2, U32, acc) <> out)
    case h <> t 0n:
      chunks(t, size, Nat.sub(size, 1n), h <> Nil{}, List.reverse(&2, U32, acc) <> out)
    case h <> t 1n+p:
      chunks(t, size, p, h <> acc, out)

def number(value: Maybe<&2, Nat>) -> IO(Nat):
  match value:
    case None{}:
      IO.die(Nat, 1, "Invalid number in the environment")
    case Some{n}:
      IO.pure(Nat, n)

def env_nat(name: String) -> IO(Nat):
  do IO<Nat>:
    text : String <- IO.try(String, IO.get_env(name))
    number(Nat.read(text))

def loaded(pair: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(List<&2, U32>):
  (file, result) = pair
  do IO<List<&2, U32>>:
    File.close(file)
    IO.pass(List<&2, U32>, result)

# The BENCH_INPUT file cut into BENCH_SIZE-byte messages.
def messages() -> IO(List<&2, List<&2, U32>>):
  do IO<List<&2, List<&2, U32>>>:
    path : String <- IO.try(String, IO.get_env("BENCH_INPUT"))
    +size : Nat <- env_nat("BENCH_SIZE")
    file : File <- IO.try(File, File.open(path, "r"))
    pair : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(file, 67108864)
    bytes : List<&2, U32> <- loaded(pair)
    return chunks(bytes, size, size, Nil{}, Nil{})

# n bytes (a * i + b) mod 256: the fixed keys, nonces and salts.
def pattern_go(n: Nat, +i: U32, +a: U32, +b: U32) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      U32.and(U32.add(U32.mul(a, i), b), 255) <> pattern_go(p, U32.inc(i), a, b)

def pattern(n: Nat, +a: U32, +b: U32) -> List<&2, U32>:
  pattern_go(n, 0, a, b)

# A failed operation (None) shows as the byte 256, which no success produces.
def unwrap(m: Maybe<&2, List<&2, U32>>) -> List<&2, U32>:
  match m:
    case None{}:
      [256]
    case Some{xs}:
      xs

def bit(b: Bool) -> List<&2, U32>:
  match b:
    case True{}:
      [1]
    case False{}:
      [0]

def fold(xs: List<&2, U32>, c: U32) -> U32:
  match xs:
    case Nil{}:
      c
    case h <> t:
      fold(t, U32.add(U32.mul(c, 31), h))

def checksum(xs: List<&2, List<&2, U32>>, c: U32) -> U32:
  match xs:
    case Nil{}:
      c
    case h <> t:
      checksum(t, fold(h, c))

# Outputs arrive last message first (the drivers accumulate by prepending).
def report(start: Nat, stop: Nat, outs: List<&2, List<&2, U32>>) -> IO(Unit):
  do IO<Unit>:
    IO.print("BENCH_MS=" ++ Nat.show(Nat.sub(stop, start)))
    IO.print("SUM=" ++ U32.show(checksum(outs, 0)))
