import Base
import ./example.bend as E
import ../../src/containers/intrusive_doubly_linked_list.bend as IL

# One world owns entity payloads and two independent associations. Scheduler
# links are at 32/64; render links are at 128/160. Roots 0/1 select ready and
# waiting; root 2 is the render list. All issued IDs are the trusted 1..3.
def render_next(s: Array<U32>, n: E.Entity) -> Array<U32> & Maybe<&2,E.Entity>:
  E.Entity{id} = n
  E.read_link(Array.get(U32,s,(128 + id : U32)))

def render_prev(s: Array<U32>, n: E.Entity) -> Array<U32> & Maybe<&2,E.Entity>:
  E.Entity{id} = n
  E.read_link(Array.get(U32,s,(160 + id : U32)))

def set_render_next(s: Array<U32>, n: E.Entity, m: Maybe<&2,E.Entity>) -> Array<U32>:
  E.Entity{id} = n
  Array.set(U32,s,(128 + id : U32),E.number(m))

def set_render_prev(s: Array<U32>, n: E.Entity, m: Maybe<&2,E.Entity>) -> Array<U32>:
  E.Entity{id} = n
  Array.set(U32,s,(160 + id : U32),E.number(m))

def add_render(s: Array<U32>, n: E.Entity) -> Array<U32>:
  IL.prepend_as(~Array<U32>,~E.Entity,~E.Group,~E.Writer,~E.get_head,~set_render_next,~set_render_prev,~E.set_nonempty,s,E.Group{2},E.Writer{2},n)

def add(s: Array<U32>, +n: U32, payload: U32) -> Array<U32>:
  add_render(E.prepend(Array.set(U32,s,(96 + n : U32),payload),E.Group{0},E.Writer{0},E.Entity{n}),E.Entity{n})

def render(s: Array<U32>) -> Array<U32> & String:
  E.show_result(IL.to_list(~Array<U32>,~E.Entity,~U32,~E.Group,~E.get_head,~render_next,~render_prev,~E.value,3n,s,E.Group{2}))

def payloads(n: Nat, total: U32, r: Array<U32> & U32) -> Array<U32> & U32:
  match n r:
    case 0n Tuple{s,v}: (s,(total + v : U32))
    case 1n+ +p Tuple{s,v}:
      payloads(p,(total + v : U32),Array.get(U32,s,(96 + U32.from_nat(1n+p) : U32)))

def finish(ready: String, waiting: String, visible: String, r: Array<U32> & U32) -> String:
  (s,total) = r
  "Ready: " ++ ready ++ "\nWaiting: " ++ waiting ++ "\nRender: " ++ visible ++ "\nPayload sum: " ++ U32.show(total)

def shown_render(ready: String, waiting: String, r: Array<U32> & String) -> String:
  (s,visible) = r
  finish(ready,waiting,visible,payloads(3n,0,(s,0)))

def shown_waiting(ready: String, r: Array<U32> & String) -> String:
  (s,waiting) = r
  shown_render(ready,waiting,render(s))

def shown_ready(r: Array<U32> & String) -> String:
  (s,ready) = r
  shown_waiting(ready,E.show(s,E.Group{1}))

def demo() -> String:
  s : Array<U32> = add(add(add(Array.new(U32,8n,0),3,300),2,200),1,100)
  # Sleep 2, then 1; wake 2. Render membership and payloads stay intact.
  s : Array<U32> = E.move(s,E.Writer{0},E.Group{1},E.Writer{1},E.Entity{2})
  s : Array<U32> = E.move(s,E.Writer{0},E.Group{1},E.Writer{1},E.Entity{1})
  s : Array<U32> = E.move(s,E.Writer{1},E.Group{0},E.Writer{0},E.Entity{2})
  shown_ready(E.show(s,E.Group{0}))

def main() -> IO(Unit):
  IO.print(demo())
