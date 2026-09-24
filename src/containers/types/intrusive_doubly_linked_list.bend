import Base

# A traversal consumed its supplied bound before reaching the end.
# The returned owner includes effects of callbacks that already ran.
type Error is Data:
  LimitExceeded{}
  InvalidTraversal{}

type Search<-N: Data> is Data:
  Seeking{next: Maybe<&2, N>}
  Found{node: N}

type Filter<-N: Data> is Data:
  Prefix{head: Maybe<&2, N>}
  Tail{next: Maybe<&2, N>}
  FilterFailed{error: Error}

# The pool reuses the selected next link as a free stack. S continues to own
# the nodes and their payloads; freeing a node does not erase its value.
type Pool<-N: Data> is Type:
  Pool{head: Maybe<&2, N>, count: Nat}

# Optional wrapper for a value that does not already carry an association.
# Store these in application-owned storage and adapt the fields statically.
type DefaultNode<-N: Data, -V: Data> is Data:
  Node{next: Maybe<&2, N>, prev: Maybe<&2, N>, value: V}
