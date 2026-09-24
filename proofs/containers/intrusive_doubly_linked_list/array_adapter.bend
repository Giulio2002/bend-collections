import Base
import ./graph.bend as G
import ./adapter.bend as A
import ./spec.bend as Spec
import ./history.bend as H
import ../../../src/containers/intrusive_doubly_linked_list.bend as L

# A concrete owned-array witness for the adapter laws, for every graph over
# these nominal IDs, every payload P, and every primitive write. This is not
# a sampled test and it does not claim to prove arbitrary user adapters.
type Node is Data:
  A{}
  B{}
  C{}
  D{}

type Root is Data:
  Ready{}
  Waiting{}

type Reader is Data:
  Reader{root: Root}

type Writer is Data:
  Writer{root: Root}

type Store<-P: Data> is Type:
  Store{cells: Array<Maybe<&2,Node>>, payload: P}

def eq(a: Node, b: Node) -> Bool:
  match a b:
    case A{} A{}: True{}
    case B{} B{}: True{}
    case C{} C{}: True{}
    case D{} D{}: True{}
    case _ _: False{}

def req(a: Root, b: Root) -> Bool:
  match a b:
    case Ready{} Ready{}: True{}
    case Waiting{} Waiting{}: True{}
    case _ _: False{}

def reflex(+n: Node) -> {eq(n,n) == True{} : Bool}:
  match n:
    case A{}: {==}
    case B{}: {==}
    case C{}: {==}
    case D{}: {==}

def root(i: Writer) -> Root:
  Writer{r} = i
  r

def ni(n: Node) -> U32:
  match n:
    case A{}: 0
    case B{}: 1
    case C{}: 2
    case D{}: 3

def pi(n: Node) -> U32:
  match n:
    case A{}: 4
    case B{}: 5
    case C{}: 6
    case D{}: 7

def ri(r: Root) -> U32:
  match r:
    case Ready{}: 8
    case Waiting{}: 9

def real(~P: Data, +g: G.Graph<Node,Root,P>) -> Store<P>:
  Store{ANode{
    ANode{ANode{ANode{ALeaf{G.next(~Node,~Root,~P,~eq,g,A{})},ALeaf{G.next(~Node,~Root,~P,~eq,g,B{})}},ANode{ALeaf{G.next(~Node,~Root,~P,~eq,g,C{})},ALeaf{G.next(~Node,~Root,~P,~eq,g,D{})}}},
          ANode{ANode{ALeaf{G.prev(~Node,~Root,~P,~eq,g,A{})},ALeaf{G.prev(~Node,~Root,~P,~eq,g,B{})}},ANode{ALeaf{G.prev(~Node,~Root,~P,~eq,g,C{})},ALeaf{G.prev(~Node,~Root,~P,~eq,g,D{})}}}},
    ANode{ANode{ANode{ALeaf{G.head(~Node,~Root,~P,~req,g,Ready{})},ALeaf{G.head(~Node,~Root,~P,~req,g,Waiting{})}},ANode{ALeaf{None{}},ALeaf{None{}}}},ANode{ANode{ALeaf{None{}},ALeaf{None{}}},ANode{ALeaf{None{}},ALeaf{None{}}}}}},G.frame(~Node,~Root,~P,g)}

def read_result(~P: Data, f: P, r: Array<Maybe<&2,Node>> & Maybe<&2,Node>) -> Store<P> & Maybe<&2,Node>:
  (cells,n) = r
  (Store{cells,f},n)

def read(~P: Data, s: Store<P>, i: U32) -> Store<P> & Maybe<&2,Node>:
  Store{cells,f} = s
  read_result(~P,f,Array.get(Maybe<&2,Node>,cells,i))

def write(~P: Data, s: Store<P>, i: U32, v: Maybe<&2,Node>) -> Store<P>:
  Store{cells,f} = s
  Store{Array.set(Maybe<&2,Node>,cells,i,v),f}

def next(~P: Data, s: Store<P>, n: Node) -> Store<P> & Maybe<&2,Node>:
  read(~P,s,ni(n))

def prev(~P: Data, s: Store<P>, n: Node) -> Store<P> & Maybe<&2,Node>:
  read(~P,s,pi(n))

def head(~P: Data, s: Store<P>, h: Reader) -> Store<P> & Maybe<&2,Node>:
  Reader{r} = h
  read(~P,s,ri(r))

def sn(~P: Data, s: Store<P>, n: Node, v: Maybe<&2,Node>) -> Store<P>:
  write(~P,s,ni(n),v)

def sp(~P: Data, s: Store<P>, n: Node, v: Maybe<&2,Node>) -> Store<P>:
  write(~P,s,pi(n),v)

def sh(~P: Data, s: Store<P>, i: Writer, v: Maybe<&2,Node>) -> Store<P>:
  write(~P,s,ri(root(i)),v)

def sf(~P: Data, s: Store<P>, i: Writer, n: Node) -> Store<P>:
  sh(~P,s,i,Some{n})

def next_law(~P: Data, +g: G.Graph<Node,Root,P>, +n: Node) -> {next(~P,real(~P,g),n) == (real(~P,g),G.next(~Node,~Root,~P,~eq,g,n)) : Store<P> & Maybe<&2,Node>}:
  match n:
    case A{}: {==}
    case B{}: {==}
    case C{}: {==}
    case D{}: {==}

def prev_law(~P: Data, +g: G.Graph<Node,Root,P>, +n: Node) -> {prev(~P,real(~P,g),n) == (real(~P,g),G.prev(~Node,~Root,~P,~eq,g,n)) : Store<P> & Maybe<&2,Node>}:
  match n:
    case A{}: {==}
    case B{}: {==}
    case C{}: {==}
    case D{}: {==}

def head_law(~P: Data, +g: G.Graph<Node,Root,P>, +r: Root) -> {head(~P,real(~P,g),Reader{r}) == (real(~P,g),G.head(~Node,~Root,~P,~req,g,r)) : Store<P> & Maybe<&2,Node>}:
  match r:
    case Ready{}: {==}
    case Waiting{}: {==}

def sn_law(~P: Data, +g: G.Graph<Node,Root,P>, +n: Node, +v: Maybe<&2,Node>) -> {sn(~P,real(~P,g),n,v) == real(~P,G.sn(~Node,~Root,~P,g,n,v)) : Store<P>}:
  match g n:
    case G.Graph{ns,ps,rs,f} A{}: {==}
    case G.Graph{ns,ps,rs,f} B{}: {==}
    case G.Graph{ns,ps,rs,f} C{}: {==}
    case G.Graph{ns,ps,rs,f} D{}: {==}

def sp_law(~P: Data, +g: G.Graph<Node,Root,P>, +n: Node, +v: Maybe<&2,Node>) -> {sp(~P,real(~P,g),n,v) == real(~P,G.sp(~Node,~Root,~P,g,n,v)) : Store<P>}:
  match g n:
    case G.Graph{ns,ps,rs,f} A{}: {==}
    case G.Graph{ns,ps,rs,f} B{}: {==}
    case G.Graph{ns,ps,rs,f} C{}: {==}
    case G.Graph{ns,ps,rs,f} D{}: {==}

def sh_law(~P: Data, +g: G.Graph<Node,Root,P>, +i: Writer, +v: Maybe<&2,Node>) -> {sh(~P,real(~P,g),i,v) == real(~P,G.sh(~Node,~Root,~P,g,root(i),v)) : Store<P>}:
  match g i:
    case G.Graph{ns,ps,rs,f} Writer{Ready{}}: {==}
    case G.Graph{ns,ps,rs,f} Writer{Waiting{}}: {==}



def write_law(~P: Data, +g: G.Graph<Node,Root,P>, +e: Spec.Edit<Node,Writer>) -> {Spec.apply(~Store<P>, ~Node, ~Writer, ~(s => n => v => sn(~P,s,n,v)), ~(s => n => v => sp(~P,s,n,v)), ~(s => i => v => sh(~P,s,i,v)), ~(s => i => n => sf(~P,s,i,n)),real(~P,g),e) == real(~P,A.apply(~Node, ~Root, ~P, ~Writer, ~root,g,e)) : Store<P>}:
  match e:
    case Spec.Next{n,v}: sn_law(~P,g,n,v)
    case Spec.Prev{n,v}: sp_law(~P,g,n,v)
    case Spec.Head{i,v}: sh_law(~P,g,i,v)
    case Spec.Nonempty{i,n}: sh_law(~P,g,i,Some{n})

def write_laws(~P: Data, +es: List<&2,Spec.Edit<Node,Writer>>, +g: G.Graph<Node,Root,P>) -> A.laws(~Store<P>, ~Node, ~Root, ~P, ~Writer, ~(g => real(~P,g)), ~root, ~(s => n => v => sn(~P,s,n,v)), ~(s => n => v => sp(~P,s,n,v)), ~(s => i => v => sh(~P,s,i,v)), ~(s => i => n => sf(~P,s,i,n)),es,g):
  match es:
    case Nil{}: Unit{}
    case Con{+e,+rest}: (write_law(~P,g,e),write_laws(~P,rest,A.apply(~Node, ~Root, ~P, ~Writer, ~root,g,e)))

def remove(~P: Data, s: Store<P>, r: Root, n: Node) -> Store<P>:
  L.remove(~Store<P>,~Node,~Writer,~(s => n => next(~P,s,n)),~(s => n => prev(~P,s,n)),~(s => n => v => sn(~P,s,n,v)),~(s => n => v => sp(~P,s,n,v)),~(s => i => v => sh(~P,s,i,v)),s,Writer{r},n)

def prepend(~P: Data, s: Store<P>, +r: Root, n: Node) -> Store<P>:
  L.prepend_as(~Store<P>,~Node,~Reader,~Writer,~(s => h => head(~P,s,h)),~(s => n => v => sn(~P,s,n,v)),~(s => n => v => sp(~P,s,n,v)),~(s => i => n => sf(~P,s,i,n)),s,Reader{r},Writer{r},n)

def remove_refines(~P: Data, +g: G.Graph<Node,Root,P>, +r: Root, +n: Node) -> {remove(~P,real(~P,g),r,n) == real(~P,G.remove(~Node, ~Root, ~P,~eq,g,r,n)) : Store<P>}:
  A.remove_refines(~Store<P>, ~Node, ~Root, ~P, ~Writer, ~(g => real(~P,g)), ~root, ~(s => n => v => sn(~P,s,n,v)), ~(s => n => v => sp(~P,s,n,v)), ~(s => i => v => sh(~P,s,i,v)), ~(s => i => n => sf(~P,s,i,n)),~eq,~(s => n => next(~P,s,n)),~(s => n => prev(~P,s,n)),g,Writer{r},n,next_law(~P,g,n),prev_law(~P,g,n),write_laws(~P,Spec.remove(Node,Writer,Writer{r},n,G.prev(~Node, ~Root, ~P,~eq,g,n),G.next(~Node, ~Root, ~P,~eq,g,n)),g))

def prepend_refines(~P: Data, +g: G.Graph<Node,Root,P>, +r: Root, +n: Node) -> {prepend(~P,real(~P,g),r,n) == real(~P,G.prepend(~Node, ~Root, ~P,~req,g,r,n)) : Store<P>}:
  A.prepend_refines(~Store<P>, ~Node, ~Root, ~P, ~Writer, ~(g => real(~P,g)), ~root, ~(s => n => v => sn(~P,s,n,v)), ~(s => n => v => sp(~P,s,n,v)), ~(s => i => v => sh(~P,s,i,v)), ~(s => i => n => sf(~P,s,i,n)),~Reader,~req,~(s => h => head(~P,s,h)),g,Reader{r},Writer{r},n,head_law(~P,g,r),write_laws(~P,Spec.prepend(Node,Writer,Writer{r},n,G.head(~Node, ~Root, ~P,~req,g,r)),g))

def step(~P: Data, s: Store<P>, r: Root, op: H.Edit<Node>) -> Store<P>:
  match op:
    case H.Prepend{n}: prepend(~P,s,r,n)
    case H.RemoveHead{n,rest}: remove(~P,s,r,n)
    case H.RemoveAfter{a,p,n,b}: remove(~P,s,r,n)

def run(~P: Data, ops: List<&2,H.Edit<Node>>, s: Store<P>, +r: Root) -> Store<P>:
  match ops:
    case Nil{}: s
    case Con{op,rest}: run(~P,rest,step(~P,s,r,op),r)

def step_refines(~P: Data, +op: H.Edit<Node>, +g: G.Graph<Node,Root,P>, +r: Root) -> {step(~P,real(~P,g),r,op) == real(~P,H.step(~Node, ~Root, ~P,~eq,~req,g,r,op)) : Store<P>}:
  match op:
    case H.Prepend{n}: prepend_refines(~P,g,r,n)
    case H.RemoveHead{n,rest}: remove_refines(~P,g,r,n)
    case H.RemoveAfter{a,p,n,b}: remove_refines(~P,g,r,n)

# Every actual array-backed history refines the independent graph execution.
# Combine with history.run_preserves for arbitrary-length legal sequences.
def run_refines(~P: Data, +ops: List<&2,H.Edit<Node>>, +g: G.Graph<Node,Root,P>, +r: Root) -> {run(~P,ops,real(~P,g),r) == real(~P,H.run(~Node, ~Root, ~P,~eq,~req,ops,g,r)) : Store<P>}:
  match ops:
    case Nil{}: {==}
    case Con{+op,+rest}:
      %Equal.sym(Store<P>,step(~P,real(~P,g),r,op),real(~P,H.step(~Node, ~Root, ~P,~eq,~req,g,r,op)),step_refines(~P,op,g,r)) : {run(~P,rest,_,r) == real(~P,H.run(~Node, ~Root, ~P,~eq,~req,rest,H.step(~Node, ~Root, ~P,~eq,~req,g,r,op),r)) : Store<P>}
      run_refines(~P,rest,H.step(~Node, ~Root, ~P,~eq,~req,g,r,op),r)

def root_reflex(+r: Root) -> {req(r,r) == True{} : Bool}:
  match r:
    case Ready{}: {==}
    case Waiting{}: {==}

# End-to-end corollary: the actual public functions return the represented
# final sequence, all its bidirectional links remain valid, and every payload
# in P (which can also hold another association) is preserved.
def histories_correct(~P: Data, +ops: List<&2,H.Edit<Node>>, +g: G.Graph<Node,Root,P>, +r: Root, +xs: List<&2,Node>, legal: H.legal(~Node, ~Root, ~P,~eq,~req,ops,g,r,xs), initial: G.valid(~Node, ~Root, ~P,~eq,~req,g,r,xs)) -> G.both({run(~P,ops,real(~P,g),r) == real(~P,H.run(~Node, ~Root, ~P,~eq,~req,ops,g,r)) : Store<P>},G.both(G.valid(~Node, ~Root, ~P,~eq,~req,H.run(~Node, ~Root, ~P,~eq,~req,ops,g,r),r,H.orders(~Node,ops,xs)),{G.frame(~Node, ~Root, ~P,H.run(~Node, ~Root, ~P,~eq,~req,ops,g,r)) == G.frame(~Node, ~Root, ~P,g) : P})):
  (run_refines(~P,ops,g,r),(H.run_preserves(~Node, ~Root, ~P,~eq,~req,~(x => reflex(x)),ops,g,r,xs,root_reflex(r),legal,initial),H.run_frame(~Node, ~Root, ~P,~eq,~req,ops,g,r)))
