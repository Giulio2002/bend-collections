import Base
import ../../src/deque.bend as Q
import ../../types/deque.bend as E

type State is Type:
  S{q: Q.Deque<U32>, checksum: U32, errors: U32}

def fill(k: Nat, q: Q.Deque<U32>) -> Q.Deque<U32>:
  match k:
    case 0n:
      q
    case 1n+ +p:
      fill(p, Q.push_back(~U32, q, U32.from_nat(p)))

def restored(checksum: U32, errors: U32, r: Q.Deque<U32> & Result<&2, &2, E.Error, U32>) -> State:
  match r:
    case Tuple{q, Done{+v}}:
      S{Q.push_back(~U32, q, v), U32.add(checksum, v), errors}
    case Tuple{q, Fail{e}}:
      S{q, checksum, U32.inc(errors)}

def one(s: State) -> State:
  S{q, checksum, errors} = s
  restored(checksum, errors, Q.pop_front(~U32, q))

def spin(k: Nat, s: State) -> State:
  match k:
    case 0n:
      s
    case 1n+p:
      spin(p, one(s))

def report(s: State) -> String:
  S{Q.DE{front, back, +nf, +nb}, checksum, errors} = s
  "front=" ++ Nat.show(nf) ++ " back=" ++ Nat.show(nb) ++ " len=" ++ Nat.show(Nat.add(nf, nb)) ++ " errors=" ++ U32.show(errors) ++ " checksum=" ++ U32.show(checksum)

def main() -> IO(Unit):
  IO.print(report(spin(10000000n, S{fill(262144n, Q.new(~U32)), 0, 0})))
