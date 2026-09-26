import Base
import ./writes.bend as Writes
import ../../../spec/containers/intrusive_doubly_linked_list/model.bend as Graph
import ./shape.bend as Shape
import ./edits.bend as Edits
import ./adapter.bend as Adapter
import ./history.bend as History
import ./array_adapter.bend as ArrayAdapter
import ./links.bend as Links
import ./frames.bend as Frames
import ./example.bend as Example
import ./costs.bend as Costs
import ../../../spec/containers/intrusive_doubly_linked_list/main.bend as Contract
import ../../../spec/containers/intrusive_doubly_linked_list/model.bend as G

# Checked entry point. The semantic theorems apply to arbitrary identity and
# payload types through primitive adapter equations. array_adapter discharges
# all those equations for an actual owned-array representation; history proves
# arbitrary finite legal edit sequences, not a fixed test bound. links proves the
# ready-made table src/containers/intrusive_links.bend for EVERY size: its
# remove and prepend are the model graph's remove and prepend.
# See docs/INTRUSIVE_LIST.md for theorem signatures and the adapter boundary.

# ---- the contract clauses of spec/containers/intrusive_doubly_linked_list ----

def prepend_valid(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, ~req: R -> R -> Bool, ~reflex: @x: N -> {eq(x,x) == True{} : Bool}, +g: G.Graph<N,R,P>, +r: R, +n: N, +xs: List<&2,N>, +rsame: {req(r,r) == True{} : Bool}, +away: G.away(~N,~eq,n,xs), +detached: {G.prev(~N,~R,~P,~eq,g,n) == None{} : Maybe<&2,N>}, +valid: G.valid(~N,~R,~P,~eq,~req,g,r,xs)) -> Contract.Prepend.valid(~N,~R,~P,~eq,~req,~reflex,g,r,n,xs,rsame,away,detached,valid):
  Edits.prepend_preserves(~N,~R,~P,~eq,~req,~reflex,g,r,n,xs,rsame,away,detached,valid)

def prepend_other_roots(~N: Data, ~R: Data, ~P: Data, ~req: R -> R -> Bool, +g: G.Graph<N,R,P>, +r: R, +n: N, +x: R, +neq: {req(r,x) == False{} : Bool}) -> Contract.Prepend.other_roots(~N,~R,~P,~req,g,r,n,x,neq):
  Frames.prepend_other_root(~N,~R,~P,~req,g,r,n,G.head(~N,~R,~P,~req,g,r),x,neq)

def prepend_frame(~N: Data, ~R: Data, ~P: Data, ~req: R -> R -> Bool, +g: G.Graph<N,R,P>, +r: R, +n: N) -> Contract.Prepend.frame(~N,~R,~P,~req,g,r,n):
  Edits.attach_frame(~N,~R,~P,g,r,n,G.head(~N,~R,~P,~req,g,r))

def delete_first(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, ~req: R -> R -> Bool, ~reflex: @x: N -> {eq(x,x) == True{} : Bool}, +g: G.Graph<N,R,P>, +r: R, +n: N, +xs: List<&2,N>, +rsame: {req(r,r) == True{} : Bool}, +valid: G.valid(~N,~R,~P,~eq,~req,g,r,Con{n,xs})) -> Contract.Delete.first(~N,~R,~P,~eq,~req,~reflex,g,r,n,xs,rsame,valid):
  Edits.remove_head_preserves(~N,~R,~P,~eq,~req,~reflex,g,r,n,xs,rsame,valid)

def delete_inner(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, ~req: R -> R -> Bool, ~reflex: @x: N -> {eq(x,x) == True{} : Bool}, +g: G.Graph<N,R,P>, +r: R, +n: N, +a: List<&2,N>, +p: N, +b: List<&2,N>, +valid: G.valid(~N,~R,~P,~eq,~req,g,r,G.append(~N,G.append(~N,a,Con{p,Nil{}}),Con{n,b}))) -> Contract.Delete.inner(~N,~R,~P,~eq,~req,~reflex,g,r,n,a,p,b,valid):
  Edits.remove_nonhead_preserves(~N,~R,~P,~eq,~req,~reflex,g,r,n,a,p,b,valid)

def delete_other_roots(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, ~req: R -> R -> Bool, +g: G.Graph<N,R,P>, +r: R, +n: N, +x: R, +neq: {req(r,x) == False{} : Bool}) -> Contract.Delete.other_roots(~N,~R,~P,~eq,~req,g,r,n,x,neq):
  Frames.remove_other_root(~N,~R,~P,~req,g,r,n,G.prev(~N,~R,~P,~eq,g,n),G.next(~N,~R,~P,~eq,g,n),x,neq)

def delete_frame(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, +g: G.Graph<N,R,P>, +r: R, +n: N) -> Contract.Delete.frame(~N,~R,~P,~eq,g,r,n):
  Edits.cut_frame(~N,~R,~P,g,r,n,G.prev(~N,~R,~P,~eq,g,n),G.next(~N,~R,~P,~eq,g,n))

def delete_detached(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, +g: G.Graph<N,R,P>, +r: R, +n: N, +same: {eq(n,n) == True{} : Bool}) -> Contract.Delete.detached(~N,~R,~P,~eq,g,r,n,same):
  Frames.removed_next(~N,~R,~P,~eq,g,r,n,G.prev(~N,~R,~P,~eq,g,n),G.next(~N,~R,~P,~eq,g,n),same)

def first_head(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, ~req: R -> R -> Bool, +g: G.Graph<N,R,P>, +r: R, +xs: List<&2,N>, +valid: G.valid(~N,~R,~P,~eq,~req,g,r,xs)) -> Contract.First.head(~N,~R,~P,~eq,~req,g,r,xs,valid):
  match valid:
    case Tuple{un, Tuple{+h, s}}:
      h
