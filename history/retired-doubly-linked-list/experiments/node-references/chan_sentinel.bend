import Base

# Capability experiment, not the production library or a formal proof.
# Stock channels provide shared node identity. Every channel has room for
# one node record. Operations are sequential IO; no custom effects/FFI.
type Node is Data:
  Node{value: U32, prev: Chan(Node), next: Chan(Node)}

type DList is Type:
  DL{sentinel: Chan(Node), length: Nat}

def previous(n: Node) -> Chan(Node):
  Node{value, prev, next} = n
  prev

def following(n: Node) -> Chan(Node):
  Node{value, prev, next} = n
  next

def value(n: Node) -> U32:
  Node{value, prev, next} = n
  value

def put(ref: Chan(Node), n: Node) -> IO(Unit):
  do IO<Unit>:
    Bool <- Chan.send(Node, ref, n)
    return Unit{}

def read_got(+ref: Chan(Node), item: Maybe<&1, Node>) -> IO(Node):
  match item:
    case None{}:
      IO.die(Node, 1, "read of closed node")
    case Some{+n}:
      do IO<Node>:
        put(ref, n)
        return n

def read(+ref: Chan(Node)) -> IO(Node):
  do IO<Node>:
    item: Maybe<&1, Node> <- Chan.recv(Node, ref)
    read_got(ref, item)

def replace_got(ref: Chan(Node), n: Node, old: Maybe<&1, Node>) -> IO(Unit):
  match old:
    case None{}:
      IO.die(Unit, 1, "write of closed node")
    case Some{discard}:
      put(ref, n)

def replace(+ref: Chan(Node), n: Node) -> IO(Unit):
  do IO<Unit>:
    old: Maybe<&1, Node> <- Chan.recv(Node, ref)
    replace_got(ref, n, old)

def with_next(n: Node, next: Chan(Node)) -> Node:
  Node{value, prev, old} = n
  Node{value, prev, next}

def with_prev(n: Node, prev: Chan(Node)) -> Node:
  Node{value, old, next} = n
  Node{value, prev, next}

def set_next(+ref: Chan(Node), next: Chan(Node)) -> IO(Unit):
  do IO<Unit>:
    n: Node <- read(ref)
    replace(ref, with_next(n, next))

def set_prev(+ref: Chan(Node), prev: Chan(Node)) -> IO(Unit):
  do IO<Unit>:
    n: Node <- read(ref)
    replace(ref, with_prev(n, prev))

# A full channel retains its buffered value after close, so drain it first.
def close_node(+ref: Chan(Node)) -> IO(Unit):
  do IO<Unit>:
    old: Maybe<&1, Node> <- Chan.recv(Node, ref)
    Chan.close(Node, ref)

def new() -> IO(DList):
  do IO<DList>:
    +root: Chan(Node) <- Chan.new(Node, 1)
    put(root, Node{0, root, root})
    return DL{root, 0n}

# right must be a live member or sentinel. Updates reread each neighbour:
# left and right may be the same node in the empty/singleton cases.
def insert_before(list: DList, +right: Chan(Node), x: U32) -> IO(DList):
  DL{root, length} = list
  do IO<DList>:
    r: Node <- read(right)
    +left: Chan(Node) = previous(r)
    +node: Chan(Node) <- Chan.new(Node, 1)
    put(node, Node{x, left, right})
    set_next(left, node)
    set_prev(right, node)
    return DL{root, 1n+length}

def push_back(list: DList, x: U32) -> IO(DList):
  DL{+root, length} = list
  insert_before(DL{root, length}, root, x)

def push_front(list: DList, x: U32) -> IO(DList):
  DL{+root, length} = list
  do IO<DList>:
    n: Node <- read(root)
    insert_before(DL{root, length}, following(n), x)

# node must be a live non-sentinel member. A caller must not reuse its
# channel after removal; this experiment does not promise stale handles.
def remove(list: DList, +node: Chan(Node)) -> IO(DList & U32):
  DL{root, length} = list
  match length:
    case 0n:
      IO.die(DList & U32, 1, "remove on empty list")
    case 1n+rest:
      do IO<DList & U32>:
        +n: Node <- read(node)
        set_next(previous(n), following(n))
        set_prev(following(n), previous(n))
        close_node(node)
        return (DL{root, rest}, value(n))

def choose(forward: Bool, next: Chan(Node), prev: Chan(Node)) -> Chan(Node):
  match forward:
    case True{}:
      next
    case False{}:
      prev

def walk(n: Nat, ref: Chan(Node), +forward: Bool) -> IO(List<&2, U32>):
  match n:
    case 0n:
      IO.pure(List<&2, U32>, Nil{})
    case 1n+rest:
      do IO<List<&2, U32>>:
        +node: Node <- read(ref)
        next: Chan(Node) = choose(forward, following(node), previous(node))
        tail: List<&2, U32> <- walk(rest, next, forward)
        return Con{value(node), tail}

def show_list(list: DList, +forward: Bool) -> IO(DList & List<&2, U32>):
  DL{+root, +length} = list
  do IO<DList & List<&2, U32>>:
    +node: Node <- read(root)
    first: Chan(Node) = choose(forward, following(node), previous(node))
    values: List<&2, U32> <- walk(length, first, forward)
    return (DL{root, length}, values)

def check(ok: Bool) -> IO(Unit):
  match ok:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.die(Unit, 1, "value mismatch")

def assert_eq(actual: List<&2, U32>, expected: List<&2, U32>) -> IO(Unit):
  match actual expected:
    case Nil{} Nil{}:
      IO.pure(Unit, Unit{})
    case Con{a, at} Con{b, bt}:
      do IO<Unit>:
        Unit <- check(U32.is_eq(a, b))
        assert_eq(at, bt)
    case _ _:
      IO.die(Unit, 1, "list length mismatch")

def checked_list(expected: List<&2, U32>, r: DList & List<&2, U32>) -> IO(DList):
  (list, actual) = r
  do IO<DList>:
    assert_eq(actual, expected)
    return list

def verify(list: DList, expected: List<&2, U32>, forward: Bool) -> IO(DList):
  do IO<DList>:
    r: DList & List<&2, U32> <- show_list(list, forward)
    checked_list(expected, r)

def removed(expected: U32, r: DList & U32) -> IO(DList):
  (list, actual) = r
  do IO<DList>:
    check(U32.is_eq(actual, expected))
    return list

def pop_front(list: DList, expected: U32) -> IO(DList):
  DL{+root, length} = list
  do IO<DList>:
    node: Node <- read(root)
    r: DList & U32 <- remove(DL{root, length}, following(node))
    removed(expected, r)

def finish(list: DList) -> IO(Unit):
  DL{+root, length} = list
  do IO<Unit>:
    check(Nat.is_eq(length, 0n))
    +node: Node <- read(root)
    # Following either link of the empty sentinel must reach its record.
    prev: Node <- read(previous(node))
    next: Node <- read(following(node))
    check(U32.is_eq(value(prev), 0))
    check(U32.is_eq(value(next), 0))
    close_node(root)
    IO.print("PASS: sentinel, stored length, forward/backward traversal, insertion, removal, empty reuse\n")

def main() -> IO(Unit):
  do IO<Unit>:
    list: DList <- new()
    list: DList <- push_back(list, 10)
    list: DList <- push_back(list, 20)
    list: DList <- push_front(list, 5)
    list: DList <- verify(list, [5, 10, 20], True{})
    list: DList <- verify(list, [20, 10, 5], False{})
    list: DList <- pop_front(list, 5)
    list: DList <- pop_front(list, 10)
    list: DList <- pop_front(list, 20)
    list: DList <- verify(list, [], True{})
    list: DList <- push_back(list, 99)
    list: DList <- verify(list, [99], False{})
    list: DList <- pop_front(list, 99)
    finish(list)
