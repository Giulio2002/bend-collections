import Base

type Deque<-T: Data> is Type:
  DE{}
  DQ{depth: Nat, cap: U32, lo: U32, len: U32, slots: Array<T>}

def wrap_go(+x: U32, +cap: U32, lt: Bool) -> U32:
  match lt:
    case True{}:
      x
    case False{}:
      U32.sub(x, cap)

def wrap(+x: U32, +cap: U32) -> U32:
  wrap_go(x, cap, U32.is_lt(x, cap))

def new(~T: Data) -> Deque<T>:
  DE{}

def copy_go(~T: Data, k: Nat, +j: U32, +lo: U32, +cap: U32, dst: Array<T>, r: Array<T> & T) -> Array<T>:
  match k r:
    case 0n Tuple{src, x}:
      dst
    case 1n+ +p Tuple{src, x}:
      copy_go(~T, p, U32.inc(j), lo, cap, Array.set(T, dst, j, x), Array.get(T, src, wrap(U32.add(lo, U32.inc(j)), cap)))

def grow(~T: Data, +dep: Nat, +cap: U32, +lo: U32, +len: U32, a: Array<T>, +v: T) -> Array<T>:
  copy_go(~T, U32.to_nat(len), 0, lo, cap, Array.new(T, 1n+dep, v), Array.get(T, a, lo))

def pb_room(~T: Data, +dep: Nat, +cap: U32, +lo: U32, +len: U32, a: Array<T>, +v: T, room: Bool) -> Deque<T>:
  match room:
    case True{}:
      DQ{dep, cap, lo, U32.inc(len), Array.set(T, a, wrap(U32.add(lo, len), cap), v)}
    case False{}:
      DQ{1n+dep, U32.shl(cap), 0, U32.inc(len), Array.set(T, grow(~T, dep, cap, lo, len, a, v), len, v)}

def push_back(~T: Data, d: Deque<T>, +v: T) -> Deque<T>:
  match d:
    case DE{}:
      DQ{0n, 1, 0, 1, Array.new(T, 0n, v)}
    case DQ{+dep, +cap, +lo, +len, a}:
      pb_room(~T, dep, cap, lo, len, a, v, U32.is_lt(len, cap))
