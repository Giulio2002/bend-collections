import Base

law append_assoc:
  for -A: Data
  for xs: List<&2, A>
  for ys: List<&2, A>
  for zs: List<&2, A>
  {List.append(&2, A, List.append(&2, A, xs, ys), zs)
    == List.append(&2, A, xs, List.append(&2, A, ys, zs)) : List<&2, A>}

def append_assoc(A, xs, ys, zs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %append_assoc(A, t, ys, zs) :
        {h <> List.append(&2, A, List.append(&2, A, t, ys), zs) == h <> _ : List<&2, A>}
      {==}

law reverse_twice:
  for -A: Data
  for xs: List<&2, A>
  for acc: List<&2, A>
  for ys: List<&2, A>
  {List.reverse.go(&2, A, List.reverse.go(&2, A, xs, acc), ys)
    == List.reverse.go(&2, A, acc, List.append(&2, A, xs, ys)) : List<&2, A>}

def reverse_twice(A, xs, acc, ys):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      reverse_twice(A, t, h <> acc, ys)

law reverse_append:
  for -A: Data
  for xs: List<&2, A>
  for ys: List<&2, A>
  {List.reverse.go(&2, A, List.reverse(&2, A, xs), ys)
    == List.append(&2, A, xs, ys) : List<&2, A>}

def reverse_append(A, xs, ys):
  reverse_twice(A, xs, Nil{}, ys)

law add_succ:
  for n: Nat
  for m: Nat
  {Nat.add(n, 1n+m) == 1n+Nat.add(n, m) : Nat}

def add_succ(n, m):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, m) : {1n+Nat.add(p, 1n+m) == 1n+_ : Nat}
      {==}

law add_zero:
  for n: Nat
  {Nat.add(n, 0n) == n : Nat}

def add_zero(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

law append_assoc_reverse:
  for -A: Data
  for +xs: List<&2, A>
  for +ys: List<&2, A>
  for +zs: List<&2, A>
  {List.append(&2, A, xs, List.append(&2, A, ys, zs))
    == List.append(&2, A, List.append(&2, A, xs, ys), zs) : List<&2, A>}

def append_assoc_reverse(A, xs, ys, zs):
  Equal.sym(List<&2, A>, List.append(&2, A, List.append(&2, A, xs, ys), zs),
    List.append(&2, A, xs, List.append(&2, A, ys, zs)), append_assoc(A, xs, ys, zs))

law add_swap:
  for +n: Nat
  for +k: Nat
  for +m: Nat
  {Nat.add(n, Nat.add(k, m)) == Nat.add(k, Nat.add(n, m)) : Nat}

def add_swap(n, k, m):
  match k:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Nat, Nat.add(n, 1n+Nat.add(p, m)),
        1n+Nat.add(n, Nat.add(p, m)), 1n+Nat.add(p, Nat.add(n, m)),
        add_succ(n, Nat.add(p, m)),
        Equal.cong(Nat, Nat, x => 1n+x, Nat.add(n, Nat.add(p, m)),
          Nat.add(p, Nat.add(n, m)), add_swap(n, p, m)))
