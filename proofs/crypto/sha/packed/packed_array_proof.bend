import Base

# A duplicable proof-only description of an array. Never used by the hash.
type Tree is Data:
  Leaf{value: U32}
  Node{left: Tree, right: Tree}

def thaw(t: Tree) -> Array<U32>:
  match t:
    case Leaf{x}: ALeaf{x}
    case Node{l,r}: ANode{thaw(l),thaw(r)}

# Consume any linear array once, retaining a proof of its exact representation.
law reify:
  for a: Array<U32>
  Sigma<&2,&1,Tree,t => {a == thaw(t) : Array<U32>}>

law reify_node:
  for -l: Array<U32>
  for -r: Array<U32>
  for left: Sigma<&2,&1,Tree,t => {l == thaw(t) : Array<U32>}>
  for right: Sigma<&2,&1,Tree,t => {r == thaw(t) : Array<U32>}>
  Sigma<&2,&1,Tree,t => {ANode{l,r} == thaw(t) : Array<U32>}>

def reify_node(l,r,left,right):
  match left right:
    case Tuple{+lt,lp} Tuple{+rt,rp}:
      (Node{lt,rt},
        Equal.trans(Array<U32>,ANode{l,r},ANode{thaw(lt),r},ANode{thaw(lt),thaw(rt)},
          Equal.cong(Array<U32>,Array<U32>,x => ANode{x,r},l,thaw(lt),lp),
          Equal.cong(Array<U32>,Array<U32>,x => ANode{thaw(lt),x},r,thaw(rt),rp)))

def reify(a):
  match a:
    case ALeaf{+x}: (Leaf{x},{==})
    case ANode{l,r}: reify_node(l,r,reify(l),reify(r))
