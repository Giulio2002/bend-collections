import Base

# List and Nat facts for the incremental hasher.

law append_nil:
  for +xs: List<&2, U32>
  {List.append(&2, U32, xs, Nil{}) == xs : List<&2, U32>}

def append_nil(xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %append_nil(t) : {h <> List.append(&2, U32, t, Nil{}) == h <> _ : List<&2, U32>}
      {==}

law append_assoc:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +zs: List<&2, U32>
  {List.append(&2, U32, List.append(&2, U32, xs, ys), zs) == List.append(&2, U32, xs, List.append(&2, U32, ys, zs)) : List<&2, U32>}

def append_assoc(xs, ys, zs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %append_assoc(t, ys, zs) :
        {h <> List.append(&2, U32, List.append(&2, U32, t, ys), zs) == h <> _ : List<&2, U32>}
      {==}

law append_assoc_rev:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +zs: List<&2, U32>
  {List.append(&2, U32, xs, List.append(&2, U32, ys, zs)) == List.append(&2, U32, List.append(&2, U32, xs, ys), zs) : List<&2, U32>}

def append_assoc_rev(xs, ys, zs):
  Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, xs, ys), zs),
    List.append(&2, U32, xs, List.append(&2, U32, ys, zs)), append_assoc(xs, ys, zs))

law add_zero:
  for +n: Nat
  {Nat.add(n, 0n) == n : Nat}

def add_zero(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

law add_assoc:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}

def add_assoc(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

law length_append:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  {List.length(&2, U32, List.append(&2, U32, xs, ys)) == Nat.add(List.length(&2, U32, xs), List.length(&2, U32, ys)) : Nat}

def length_append(xs, ys):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %length_append(t, ys) : {1n+List.length(&2, U32, List.append(&2, U32, t, ys)) == 1n+_ : Nat}
      {==}

# n + |xs| + |ys| == n + |xs ++ ys|
law add_length:
  for +n: Nat
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  {Nat.add(Nat.add(n, List.length(&2, U32, xs)), List.length(&2, U32, ys)) == Nat.add(n, List.length(&2, U32, List.append(&2, U32, xs, ys))) : Nat}

def add_length(n, xs, ys):
  %Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, xs, ys)),
    Nat.add(List.length(&2, U32, xs), List.length(&2, U32, ys)), length_append(xs, ys)) :
    {Nat.add(Nat.add(n, List.length(&2, U32, xs)), List.length(&2, U32, ys)) == Nat.add(n, _) : Nat}
  add_assoc(n, List.length(&2, U32, xs), List.length(&2, U32, ys))
