import Base

# Independent write programs. These describe field updates and root hooks,
# without importing the implementation or its generated helpers.
type Edit<-N: Data, -I: Data> is Data:
  Next{node: N, link: Maybe<&2, N>}
  Prev{node: N, link: Maybe<&2, N>}
  Head{root: I, link: Maybe<&2, N>}
  Nonempty{root: I, node: N}

def remove(-N: Data, -I: Data, +root: I, +node: N, +before: Maybe<&2, N>, +after: Maybe<&2, N>) -> List<&2, Edit<N, I>>:
  match before after:
    case None{} None{}:
      Con{Head{root, None{}}, Con{Next{node, None{}}, Nil{}}}
    case None{} Some{+q}:
      Con{Prev{q, None{}}, Con{Head{root, Some{q}}, Con{Next{node, None{}}, Nil{}}}}
    case Some{p} None{}:
      Con{Next{p, None{}}, Con{Prev{node, None{}}, Con{Next{node, None{}}, Nil{}}}}
    case Some{p} Some{+q}:
      Con{Prev{q, Some{p}}, Con{Next{p, Some{q}}, Con{Prev{node, None{}}, Con{Next{node, None{}}, Nil{}}}}}

def prepend(-N: Data, -I: Data, root: I, +node: N, head: Maybe<&2, N>) -> List<&2, Edit<N, I>>:
  match head:
    case None{}:
      Con{Next{node, None{}}, Con{Nonempty{root, node}, Nil{}}}
    case Some{+h}:
      Con{Next{node, Some{h}}, Con{Prev{h, Some{node}}, Con{Nonempty{root, node}, Nil{}}}}

def apply(~S: Type, ~N: Data, ~I: Data, ~sn: S -> N -> Maybe<&2, N> -> S, ~sp: S -> N -> Maybe<&2, N> -> S, ~sh: S -> I -> Maybe<&2, N> -> S, ~sf: S -> I -> N -> S, s: S, e: Edit<N, I>) -> S:
  match e:
    case Next{n, m}: sn(s, n, m)
    case Prev{n, m}: sp(s, n, m)
    case Head{i, m}: sh(s, i, m)
    case Nonempty{i, n}: sf(s, i, n)

def run(~S: Type, ~N: Data, ~I: Data, ~sn: S -> N -> Maybe<&2, N> -> S, ~sp: S -> N -> Maybe<&2, N> -> S, ~sh: S -> I -> Maybe<&2, N> -> S, ~sf: S -> I -> N -> S, edits: List<&2, Edit<N, I>>, s: S) -> S:
  match edits:
    case Nil{}: s
    case Con{e, rest}: run(~S, ~N, ~I, ~sn, ~sp, ~sh, ~sf, rest, apply(~S, ~N, ~I, ~sn, ~sp, ~sh, ~sf, s, e))

# Exact ordered callback sequence for clear; no writes on the empty list.
def clear_order(-N: Data, nodes: List<&2, N>) -> List<&2, N>:
  match nodes:
    case Nil{}: Nil{}
    case Con{h, rest}: List.append(&2, N, rest, Con{h, Nil{}})
