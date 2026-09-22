import Base
import ../../src/balanced_search_tree.bend as M

type Payload is Data:
  Payload{name: String, score: U32}

def show(p: Payload) -> String:
  Payload{name, score} = p
  name ++ ":" ++ U32.show(score)

def finish(r: M.Cursor<String, Payload, String.order> & Maybe<&2, M.Entry<String, Payload>>) -> String:
  match r:
    case Tuple{cursor, None{}}:
      "missing"
    case Tuple{cursor, Some{M.Entry{k, v}}}:
      k ++ "=" ++ show(v)

def second(r: M.TreeMap<String, Payload, String.order> & Result<&2, &2, M.Rejected<String, Payload>, Maybe<&2, Payload>>) -> String:
  (m, status) = r
  finish(M.iterator_next(~String, ~Payload, ~String.order, M.iterator(~String, ~Payload, ~String.order, m)))

def first(r: M.TreeMap<String, Payload, String.order> & Result<&2, &2, M.Rejected<String, Payload>, Maybe<&2, Payload>>) -> String:
  (m, status) = r
  second(M.put(~String, ~Payload, ~String.order, m, "alice", Payload{"Alice", 42}))

def main() -> String:
  first(M.put(~String, ~Payload, ~String.order, M.new(~String, ~Payload, ~String.order), "bob", Payload{"Bob", 7}))
