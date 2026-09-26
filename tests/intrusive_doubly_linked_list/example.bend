import Base
import ../../src/containers/intrusive_doubly_linked_list.bend as IL
import ../../src/containers/types/intrusive_doubly_linked_list.bend as Types

# Application-owned storage, identities and root contexts. Node zero is not
# issued. This example has 31 slots and two groups; its IDs are trusted.
# A real boundary should validate an external ID before using these adapters.
type Entity is Data:
  Entity{id: U32}
type Group is Data:
  Group{id: U32}
type Writer is Data:
  Writer{group: U32}

def present(n: U32, empty: Bool) -> Maybe<&2, Entity>:
  match empty:
    case True{}: None{}
    case False{}: Some{Entity{n}}

def read_link(r: Array<U32> & U32) -> Array<U32> & Maybe<&2, Entity>:
  (world, +n) = r
  (world, present(n, U32.is_eq(n, 0)))

def number(node: Maybe<&2, Entity>) -> U32:
  match node:
    case None{}: 0
    case Some{Entity{id}}: id

def next(world: Array<U32>, node: Entity) -> Array<U32> & Maybe<&2, Entity>:
  Entity{id} = node
  read_link(Array.get(U32, world, (32 + id : U32)))

def prev(world: Array<U32>, node: Entity) -> Array<U32> & Maybe<&2, Entity>:
  Entity{id} = node
  read_link(Array.get(U32, world, (64 + id : U32)))

def set_next(world: Array<U32>, node: Entity, link: Maybe<&2, Entity>) -> Array<U32>:
  Entity{id} = node
  Array.set(U32, world, (32 + id : U32), number(link))

def set_prev(world: Array<U32>, node: Entity, link: Maybe<&2, Entity>) -> Array<U32>:
  Entity{id} = node
  Array.set(U32, world, (64 + id : U32), number(link))

def get_head(world: Array<U32>, group: Group) -> Array<U32> & Maybe<&2, Entity>:
  Group{id} = group
  read_link(Array.get(U32, world, id))

def set_head(world: Array<U32>, writer: Writer, head: Maybe<&2, Entity>) -> Array<U32>:
  Writer{group} = writer
  Array.set(U32, world, group, number(head))

def set_nonempty(world: Array<U32>, writer: Writer, node: Entity) -> Array<U32>:
  match writer node:
    case Writer{group} Entity{id}: Array.set(U32, world, group, id)

def value(world: Array<U32>, node: Entity) -> Array<U32> & U32:
  Entity{id} = node
  (world, id)

# Bind the static adapters once. Application calls have the usual small API.
def prepend(world: Array<U32>, group: Group, writer: Writer, node: Entity) -> Array<U32>:
  IL.prepend_as(~Array<U32>, ~Entity, ~Group, ~Writer, ~get_head, ~set_next, ~set_prev, ~set_nonempty, world, group, writer, node)

def remove(world: Array<U32>, writer: Writer, node: Entity) -> Array<U32>:
  IL.remove(~Array<U32>, ~Entity, ~Writer, ~next, ~prev, ~set_next, ~set_prev, ~set_head, world, writer, node)

def move(world: Array<U32>, from: Writer, to: Group, writer: Writer, +entity: Entity) -> Array<U32>:
  prepend(remove(world, from, entity), to, writer, entity)

def show_nodes(xs: List<U32>) -> String:
  match xs:
    case Nil{}: ""
    case Con{x, rest}: U32.show(x) ++ " " ++ show_nodes(rest)

def show_result(r: Array<U32> & Result<&2, &1, Types.Error, List<U32>>) -> Array<U32> & String:
  match r:
    case Tuple{world, Fail{e}}: (world, "traversal failed")
    case Tuple{world, Done{xs}}: (world, show_nodes(xs))

def show(world: Array<U32>, group: Group) -> Array<U32> & String:
  show_result(IL.to_list(~Array<U32>, ~Entity, ~U32, ~Group, ~get_head, ~next, ~prev, ~value, 31n, world, group))

def finish(a: String, r: Array<U32> & String) -> String:
  (world, b) = r
  "Group 0: " ++ a ++ "\nGroup 1: " ++ b

def moved(r: Array<U32> & String) -> String:
  (world, a) = r
  finish(a, show(world, Group{1}))

def demo() -> String:
  world : Array<U32> = Array.new(U32, 7n, 0)
  world : Array<U32> = prepend(world, Group{0}, Writer{0}, Entity{3})
  world : Array<U32> = prepend(world, Group{0}, Writer{0}, Entity{2})
  world : Array<U32> = prepend(world, Group{0}, Writer{0}, Entity{1})
  moved(show(move(world, Writer{0}, Group{1}, Writer{1}, Entity{2}), Group{0}))

def main() -> IO(Unit):
  IO.print(demo())
