import Base

# A constructive certificate carries the moved values, rather than copying a
# Type-valued input into two recursive proof calls.
def undo(-T: Type, +n: U32, +i: U32, r: Array<T> & T) -> Array<T> & T:
  (a, old) = r
  Array.swap.go(T, a, n, i, old)

def Cert(-T: Type, -a: Array<T>, -n: U32, -i: U32, -v: T) -> Type:
  Sigma<&1, &1, Array<T> & T, r => ({Array.swap.go(T, a, n, i, v) == r : Array<T> & T} & {undo(T, n, i, r) == (a, v) : Array<T> & T})>

def lift_left(-T: Type, -xs: Array<T>, ys: Array<T>, +n: U32, +i: U32, -v: T, +e: {U32.is_lt(i, U32.shr(n)) == True{} : Bool}, r: Cert(T, xs, U32.shr(n), i, v)) -> Cert(T, ANode{xs, ys}, n, i, v):
  match r:
    case Tuple{Tuple{zs, old}, Tuple{+forward, +backward}}:
      ((ANode{zs, ys}, old), (
        %Equal.sym(Bool, U32.is_lt(i, U32.shr(n)), True{}, e) : {Array.swap.if(T, xs, ys, U32.shr(n), i, v, _) == (ANode{zs, ys}, old) : Array<T> & T}
        %Equal.sym(Array<T> & T, Array.swap.go(T, xs, U32.shr(n), i, v), (zs, old), forward) : {Array.swap.lo(T, ys, _) == (ANode{zs, ys}, old) : Array<T> & T}
        {==},
        %Equal.sym(Bool, U32.is_lt(i, U32.shr(n)), True{}, e) : {Array.swap.if(T, zs, ys, U32.shr(n), i, old, _) == (ANode{xs, ys}, v) : Array<T> & T}
        %Equal.sym(Array<T> & T, Array.swap.go(T, zs, U32.shr(n), i, old), (xs, v), backward) : {Array.swap.lo(T, ys, _) == (ANode{xs, ys}, v) : Array<T> & T}
        {==}))

def lift_right(-T: Type, xs: Array<T>, -ys: Array<T>, +n: U32, +i: U32, -v: T, +e: {U32.is_lt(i, U32.shr(n)) == False{} : Bool}, r: Cert(T, ys, U32.shr(n), U32.sub(i, U32.shr(n)), v)) -> Cert(T, ANode{xs, ys}, n, i, v):
  match r:
    case Tuple{Tuple{zs, old}, Tuple{+forward, +backward}}:
      ((ANode{xs, zs}, old), (
        %Equal.sym(Bool, U32.is_lt(i, U32.shr(n)), False{}, e) : {Array.swap.if(T, xs, ys, U32.shr(n), i, v, _) == (ANode{xs, zs}, old) : Array<T> & T}
        %Equal.sym(Array<T> & T, Array.swap.go(T, ys, U32.shr(n), U32.sub(i, U32.shr(n)), v), (zs, old), forward) : {Array.swap.hi(T, xs, _) == (ANode{xs, zs}, old) : Array<T> & T}
        {==},
        %Equal.sym(Bool, U32.is_lt(i, U32.shr(n)), False{}, e) : {Array.swap.if(T, xs, zs, U32.shr(n), i, old, _) == (ANode{xs, ys}, v) : Array<T> & T}
        %Equal.sym(Array<T> & T, Array.swap.go(T, zs, U32.shr(n), U32.sub(i, U32.shr(n)), old), (ys, v), backward) : {Array.swap.hi(T, xs, _) == (ANode{xs, ys}, v) : Array<T> & T}
        {==}))

# The branch decision is an explicit parameter, so recursion remains on a
# proper subarray and the owning replacement is passed to exactly one child.
def certificate(-T: Type, a: Array<T>, +n: U32, +i: U32, v: T, b: Bool, +eb: {U32.is_lt(i, U32.shr(n)) == b : Bool}) -> Cert(T, a, n, i, v):
  match a b:
    case ALeaf{x} _:
      ((ALeaf{v}, x), ({==}, {==}))
    case ANode{xs, ys} True{}:
      lift_left(T, xs, ys, n, i, v, eb, certificate(T, xs, U32.shr(n), i, v, U32.is_lt(i, U32.shr(U32.shr(n))), {==}))
    case ANode{xs, ys} False{}:
      lift_right(T, xs, ys, n, i, v, eb, certificate(T, ys, U32.shr(n), U32.sub(i, U32.shr(n)), v, U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n))), {==}))

def finish(-T: Type, -a: Array<T>, +n: U32, +i: U32, -v: T, r: Cert(T, a, n, i, v)) -> {undo(T, n, i, Array.swap.go(T, a, n, i, v)) == (a, v) : Array<T> & T}:
  match r:
    case Tuple{out, Tuple{+forward, backward}}:
      %Equal.sym(Array<T> & T, Array.swap.go(T, a, n, i, v), out, forward) : {undo(T, n, i, _) == (a, v) : Array<T> & T}
      backward

def roundtrip(-T: Type, a: Array<T>, +n: U32, +i: U32, v: T) -> {undo(T, n, i, Array.swap.go(T, a, n, i, v)) == (a, v) : Array<T> & T}:
  finish(T, a, n, i, v, certificate(T, a, n, i, v, U32.is_lt(i, U32.shr(n)), {==}))
