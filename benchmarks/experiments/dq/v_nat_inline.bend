import Base

type Deque<-T: Data> is Type:
  DE{}
  DQ{depth: Nat, cap: Nat, lo: Nat, len: Nat, slots: Array<T>}

def copy_go(~T: Data, k: Nat, +j: Nat, +lo: Nat, +cap: Nat, dst: Array<T>, r: Array<T> & T) -> Array<T>:
  match k r:
    case 0n Tuple{src, x}:
      dst
    case 1n+ +p Tuple{src, x}:
      copy_go(~T, p, 1n+j, lo, cap, Array.set(T, dst, U32.from_nat(j), x), Array.get(T, src, U32.from_nat(Nat.mod(Nat.add(lo, 1n+j), cap))))

def grow(~T: Data, +dep: Nat, +cap: Nat, +lo: Nat, +len: Nat, a: Array<T>, +v: T) -> Array<T>:
  copy_go(~T, len, 0n, lo, cap, Array.new(T, 1n+dep, v), Array.get(T, a, U32.from_nat(lo)))

def pb_room(~T: Data, +dep: Nat, +cap: Nat, +lo: Nat, +len: Nat, a: Array<T>, +v: T, room: Bool) -> Deque<T>:
  match room:
    case True{}:
      DQ{dep, cap, lo, 1n+len, Array.set(T, a, U32.from_nat(Nat.add(lo, len)), v)}
    case False{}:
      DQ{1n+dep, Nat.double(cap), 0n, 1n+len, Array.set(T, grow(~T, dep, cap, lo, len, a, v), U32.from_nat(len), v)}

def push_back(~T: Data, d: Deque<T>, +v: T) -> Deque<T>:
  match d:
    case DE{}:
      DQ{0n, 1n, 0n, 1n, Array.new(T, 0n, v)}
    case DQ{+dep, +cap, +lo, +len, a}:
      pb_room(~T, dep, cap, lo, len, a, v, Nat.is_lt(len, cap))

def new(~T: Data) -> Deque<T>:
  DE{}
