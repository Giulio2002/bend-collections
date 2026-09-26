import Base
import ./model.bend as G
import ./programs.bend as W

# Contract of the intrusive doubly linked list (src/containers/
# intrusive_doubly_linked_list.bend; contributed by Ryan Berckmans in
# https://github.com/Giulio2002/bend-collections/pull/5).
#
# The model (model.bend) is a finite-map graph: every entity's next and prev
# link, every root's head, and a frame P standing for everything else the
# application owns. A list is valid when its members are unique, the root
# reads the first member, and every member's links point at its neighbours
# (a reciprocal, acyclic chain). programs.bend lists the exact field writes
# each operation performs.
#
# The caller owns membership, so the SPARK preconditions below are real
# obligations of the caller (SPARK's Pre): the list is valid, a prepended
# entity is detached and not already a member, a removed entity is a member.
# Under them, the clauses restate SPARK's Post for the model; the proof
# package proves each one, and proves that the exported operations execute
# the model's writes (for the ready-made table src/containers/
# intrusive_links.bend: for every size).
#
#   SPARK Formal_Doubly_Linked_Lists   ours                 clauses
#   (SPARKlib spark-containers-formal-doubly_linked_lists.ads)
#   Prepend (Post: Model = new & old)  prepend / prepend_as  Prepend.valid, Prepend.other_roots, Prepend.frame
#   Delete (Post: Model = old minus    remove                Delete.first, Delete.inner, Delete.other_roots,
#     the element; P.Keys_Included)                          Delete.frame, Delete.detached
#   First (Post: head of the model)    get_head              First.head
#
# Not applicable: Append/Insert-after/Last/Length-by-count (no tail or count
# in the root, by design), Element (payload stays in the application's
# state), Clear/Copy/Move/Splice (the application owns node storage).

# eq is a lawful identity test (~reflex) wherever the proof compares entities.

# Prepend: a detached non-member n becomes the first member.
def Prepend.valid(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, ~req: R -> R -> Bool, ~reflex: @x: N -> {eq(x,x) == True{} : Bool}, +g: G.Graph<N,R,P>, +r: R, +n: N, +xs: List<&2,N>, +rsame: {req(r,r) == True{} : Bool}, +away: G.away(~N,~eq,n,xs), +detached: {G.prev(~N,~R,~P,~eq,g,n) == None{} : Maybe<&2,N>}, +valid: G.valid(~N,~R,~P,~eq,~req,g,r,xs)) -> Type:
  G.valid(~N,~R,~P,~eq,~req,G.prepend(~N,~R,~P,~req,g,r,n),r,Con{n,xs})

# Prepend: every other root reads what it read before.
def Prepend.other_roots(~N: Data, ~R: Data, ~P: Data, ~req: R -> R -> Bool, +g: G.Graph<N,R,P>, +r: R, +n: N, +x: R, +neq: {req(r,x) == False{} : Bool}) -> Type:
  {G.head(~N,~R,~P,~req,G.prepend(~N,~R,~P,~req,g,r,n),x) == G.head(~N,~R,~P,~req,g,x) : Maybe<&2,N>}

# Prepend: everything else the application owns is unchanged.
def Prepend.frame(~N: Data, ~R: Data, ~P: Data, ~req: R -> R -> Bool, +g: G.Graph<N,R,P>, +r: R, +n: N) -> Type:
  {G.frame(~N,~R,~P,G.prepend(~N,~R,~P,~req,g,r,n)) == G.frame(~N,~R,~P,g) : P}

# Delete the first member.
def Delete.first(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, ~req: R -> R -> Bool, ~reflex: @x: N -> {eq(x,x) == True{} : Bool}, +g: G.Graph<N,R,P>, +r: R, +n: N, +xs: List<&2,N>, +rsame: {req(r,r) == True{} : Bool}, +valid: G.valid(~N,~R,~P,~eq,~req,g,r,Con{n,xs})) -> Type:
  G.valid(~N,~R,~P,~eq,~req,G.remove(~N,~R,~P,~eq,g,r,n),r,xs)

# Delete a member after the prefix a ++ [p].
def Delete.inner(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, ~req: R -> R -> Bool, ~reflex: @x: N -> {eq(x,x) == True{} : Bool}, +g: G.Graph<N,R,P>, +r: R, +n: N, +a: List<&2,N>, +p: N, +b: List<&2,N>, +valid: G.valid(~N,~R,~P,~eq,~req,g,r,G.append(~N,G.append(~N,a,Con{p,Nil{}}),Con{n,b}))) -> Type:
  G.valid(~N,~R,~P,~eq,~req,G.remove(~N,~R,~P,~eq,g,r,n),r,G.append(~N,G.append(~N,a,Con{p,Nil{}}),b))

# Delete: every other root reads what it read before.
def Delete.other_roots(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, ~req: R -> R -> Bool, +g: G.Graph<N,R,P>, +r: R, +n: N, +x: R, +neq: {req(r,x) == False{} : Bool}) -> Type:
  {G.head(~N,~R,~P,~req,G.remove(~N,~R,~P,~eq,g,r,n),x) == G.head(~N,~R,~P,~req,g,x) : Maybe<&2,N>}

# Delete: everything else the application owns is unchanged.
def Delete.frame(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, +g: G.Graph<N,R,P>, +r: R, +n: N) -> Type:
  {G.frame(~N,~R,~P,G.remove(~N,~R,~P,~eq,g,r,n)) == G.frame(~N,~R,~P,g) : P}

# Delete: the removed entity no longer links forward (it can join another list).
def Delete.detached(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, +g: G.Graph<N,R,P>, +r: R, +n: N, +same: {eq(n,n) == True{} : Bool}) -> Type:
  {G.next(~N,~R,~P,~eq,G.remove(~N,~R,~P,~eq,g,r,n),n) == None{} : Maybe<&2,N>}

# First: a valid list's root reads its first member.
def First.head(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, ~req: R -> R -> Bool, +g: G.Graph<N,R,P>, +r: R, +xs: List<&2,N>, +valid: G.valid(~N,~R,~P,~eq,~req,g,r,xs)) -> Type:
  {G.head(~N,~R,~P,~req,g,r) == G.first(~N,xs,None{}) : Maybe<&2,N>}
