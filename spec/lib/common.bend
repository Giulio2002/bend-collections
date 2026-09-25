import Base

# Shared specification mathematics. Pure list/number definitions, written
# independently of every implementation module (imports only Base).

# 2^k as a natural number.
def pow2(k: Nat) -> Nat:
  match k:
    case 0n:
      1n
    case 1n+p:
      Nat.double(pow2(p))

def length(-A: Data, xs: List<&2, A>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+length(A, t)

# Element i, if any.
def nth(-A: Data, xs: List<&2, A>, i: Nat) -> Maybe<&2, A>:
  match xs i:
    case Nil{} _:
      None{}
    case Con{h, t} 0n:
      Some{h}
    case Con{h, t} 1n+p:
      nth(A, t, p)

# Replace element i (no change when i is out of range).
def update(-A: Data, xs: List<&2, A>, i: Nat, x: A) -> List<&2, A>:
  match xs i:
    case Nil{} _:
      Nil{}
    case Con{h, t} 0n:
      Con{x, t}
    case Con{h, t} 1n+p:
      Con{h, update(A, t, p, x)}

def snoc(-A: Data, xs: List<&2, A>, x: A) -> List<&2, A>:
  match xs:
    case Nil{}:
      Con{x, Nil{}}
    case Con{h, t}:
      Con{h, snoc(A, t, x)}

def last(-A: Data, xs: List<&2, A>) -> Maybe<&2, A>:
  match xs:
    case Nil{}:
      None{}
    case Con{h, t}:
      match t:
        case Nil{}:
          Some{h}
        case Con{h2, t2}:
          last(A, Con{h2, t2})

def init(-A: Data, xs: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      match t:
        case Nil{}:
          Nil{}
        case Con{h2, t2}:
          Con{h, init(A, Con{h2, t2})}

def head(-A: Data, xs: List<&2, A>) -> Maybe<&2, A>:
  match xs:
    case Nil{}:
      None{}
    case Con{h, t}:
      Some{h}

def tail(-A: Data, xs: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      t

def append(-A: Data, xs: List<&2, A>, ys: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, append(A, t, ys)}

def reverse(-A: Data, xs: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      snoc(A, reverse(A, t), h)

def replicate(-A: Data, n: Nat, +x: A) -> List<&2, A>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{x, replicate(A, p, x)}

def take(-A: Data, xs: List<&2, A>, n: Nat) -> List<&2, A>:
  match xs n:
    case Nil{} _:
      Nil{}
    case Con{h, t} 0n:
      Nil{}
    case Con{h, t} 1n+p:
      Con{h, take(A, t, p)}

def drop(-A: Data, xs: List<&2, A>, n: Nat) -> List<&2, A>:
  match xs n:
    case Nil{} _:
      Nil{}
    case Con{h, t} 0n:
      Con{h, t}
    case Con{h, t} 1n+p:
      drop(A, t, p)

# membership of a natural number in a list of them
def memn(+s: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+x, t}:
      Bool.or(Nat.is_eq(x, s), memn(s, t))
