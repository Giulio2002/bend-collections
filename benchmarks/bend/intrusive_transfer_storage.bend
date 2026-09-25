# Diagnostic counterpart; see intrusive_storage_support.bend.
import Base
import ./common.bend as B
import ./intrusive_support.bend as A
import ./intrusive_storage_support.bend as D
import ../../src/containers/internal/dlist_storage.bend as DL

type State is Type:
  S{cells: Array<U32>, left: DL.DList<U32>, right: DL.DList<U32>}

def reordered(source: DL.DList<U32>, owner: U32, r: Array<U32> & DL.DList<U32>) -> State:
  match owner r:
    case 0 Tuple{s, destination}: S{s, source, destination}
    case _ Tuple{s, destination}: S{s, destination, source}

def moved(destination: DL.DList<U32>, +owner: U32, r: Array<U32> & (DL.DList<U32> & U32)) -> State:
  Tuple{s, Tuple{source, n}} = r
  reordered(source, owner, D.push(s, destination, n))

def move_owner(left: DL.DList<U32>, right: DL.DList<U32>, +n: U32, r: Array<U32> & U32) -> State:
  match r:
    case Tuple{s, 0}: moved(right, 0, D.remove(Array.set(U32, s, (8 * n + 5 : U32), 1), left, n, 0))
    case Tuple{s, owner}: moved(left, 1, D.remove(Array.set(U32, s, (8 * n + 5 : U32), 0), right, n, 1))

def move(st: State, +n: U32) -> State:
  S{s, left, right} = st
  move_owner(left, right, n, Array.get(U32, s, (8 * n + 5 : U32)))

def churn(churn_iterations: Nat, +size: U32, st: State, +rng: U32) -> State:
  match churn_iterations:
    case 0n: st
    case 1n+p: churn(p, size, move(st, (1 + rng / 256 % size : U32)), A.lcg(rng))

def ready(right: DL.DList<U32>, r: Array<U32> & DL.DList<U32>) -> State:
  (s, left) = r
  S{s, left, right}

def warmed(size: U32, r: Array<U32> & DL.DList<U32>) -> State:
  (s, right) = r
  ready(right, D.fill(U32.to_nat(size), (s, DL.new(~U32, 0))))

def setup(+size: U32) -> State:
  warmed(size, D.empty(U32.to_nat(size), 1, D.fill(U32.to_nat(size), (A.fresh(size), DL.new(~U32, 1)))))

def output(size: U32, st: State) -> String:
  S{s, left, right} = st
  A.output(D.observe(D.observe(s, left), right), size)

def go(+g: B.Args) -> String:
  output(B.a_size(g), churn(U32.to_nat(B.a_count(g)), B.a_size(g), setup(B.a_size(g)), B.a_seed(g)))

def main() -> IO(Unit):
  do IO<Unit>:
    raw : List<String> <- IO.args()
    IO.print(go(B.parse(raw)))
