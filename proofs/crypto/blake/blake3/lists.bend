import Base
import ../../../lib/logic.bend as L
import ../../../lib/nat.bend as N
import ../../../../spec/lib/common.bend as SC

# List and arithmetic facts used by the tree proof (generic over the element
# type, on the spec/common list functions).

def cons_cong(-A: Data, +h: A, +xs: List<&2,A>, +ys: List<&2,A>, e: {xs == ys : List<&2,A>}) -> {Con{h,xs} == Con{h,ys} : List<&2,A>}:
  Equal.cong(List<&2,A>,List<&2,A>,zs => Con{h,zs},xs,ys,e)

def take_drop(-A: Data, +xs: List<&2,A>, +k: Nat) -> {SC.append(A,SC.take(A,xs,k),SC.drop(A,xs,k)) == xs : List<&2,A>}:
  match xs k:
    case Nil{} _: {==}
    case Con{+h,+t} 0n: {==}
    case Con{+h,+t} 1n+j: cons_cong(A,h,SC.append(A,SC.take(A,t,j),SC.drop(A,t,j)),t,take_drop(A,t,j))

def length_drop(-A: Data, +xs: List<&2,A>, +k: Nat) -> {SC.length(A,SC.drop(A,xs,k)) == Nat.sub(SC.length(A,xs),k) : Nat}:
  match xs k:
    case Nil{} 0n: {==}
    case Nil{} 1n+j: {==}
    case Con{+h,+t} 0n: {==}
    case Con{+h,+t} 1n+j: length_drop(A,t,j)

def take_all(-A: Data, +xs: List<&2,A>, +k: Nat, +h: {Nat.is_le(SC.length(A,xs),k) == True{} : Bool}) -> {SC.take(A,xs,k) == xs : List<&2,A>}:
  match xs k:
    case Nil{} _: {==}
    case Con{+a,+t} 0n: Empty.absurd({SC.take(A,Con{a,t},0n) == Con{a,t} : List<&2,A>},L.false_true(h))
    case Con{+a,+t} 1n+j: cons_cong(A,a,SC.take(A,t,j),t,take_all(A,t,j,h))

def drop_all(-A: Data, +xs: List<&2,A>, +k: Nat, +h: {Nat.is_le(SC.length(A,xs),k) == True{} : Bool}) -> {SC.drop(A,xs,k) == Nil{} : List<&2,A>}:
  match xs k:
    case Nil{} _: {==}
    case Con{+a,+t} 0n: Empty.absurd({SC.drop(A,Con{a,t},0n) == Nil{} : List<&2,A>},L.false_true(h))
    case Con{+a,+t} 1n+j: drop_all(A,t,j,h)

def drop_zero(-A: Data, +ys: List<&2,A>) -> {SC.drop(A,ys,0n) == ys : List<&2,A>}:
  match ys:
    case Nil{}: {==}
    case Con{+b,+u}: {==}

def take_zero(-A: Data, +ys: List<&2,A>) -> {SC.take(A,ys,0n) == Nil{} : List<&2,A>}:
  match ys:
    case Nil{}: {==}
    case Con{+b,+u}: {==}

def drop_append_left(-A: Data, +xs: List<&2,A>, +ys: List<&2,A>, +k: Nat, +h: {Nat.is_le(k,SC.length(A,xs)) == True{} : Bool}) -> {SC.drop(A,SC.append(A,xs,ys),k) == SC.append(A,SC.drop(A,xs,k),ys) : List<&2,A>}:
  match xs k:
    case Nil{} 0n: drop_zero(A,ys)
    case Nil{} 1n+j: Empty.absurd({SC.drop(A,ys,1n+j) == ys : List<&2,A>},L.false_true(h))
    case Con{+a,+t} 0n: {==}
    case Con{+a,+t} 1n+j: drop_append_left(A,t,ys,j,h)

def take_append_left(-A: Data, +xs: List<&2,A>, +ys: List<&2,A>, +k: Nat, +h: {Nat.is_le(k,SC.length(A,xs)) == True{} : Bool}) -> {SC.take(A,SC.append(A,xs,ys),k) == SC.take(A,xs,k) : List<&2,A>}:
  match xs k:
    case Nil{} 0n: take_zero(A,ys)
    case Nil{} 1n+j: Empty.absurd({SC.take(A,ys,1n+j) == Nil{} : List<&2,A>},L.false_true(h))
    case Con{+a,+t} 0n: {==}
    case Con{+a,+t} 1n+j: cons_cong(A,a,SC.take(A,SC.append(A,t,ys),j),SC.take(A,t,j),take_append_left(A,t,ys,j,h))

def length_take(-A: Data, +xs: List<&2,A>, +k: Nat, +h: {Nat.is_le(k,SC.length(A,xs)) == True{} : Bool}) -> {SC.length(A,SC.take(A,xs,k)) == k : Nat}:
  match xs k:
    case Nil{} 0n: {==}
    case Nil{} 1n+j: Empty.absurd({SC.length(A,SC.take(A,Nil{},1n+j)) == 1n+j : Nat},L.false_true(h))
    case Con{+a,+t} 0n: {==}
    case Con{+a,+t} 1n+j: N.succ_cong(SC.length(A,SC.take(A,t,j)),j,length_take(A,t,j,h))

def length_snoc(-A: Data, +xs: List<&2,A>, +x: A) -> {SC.length(A,SC.append(A,xs,Con{x,Nil{}})) == 1n+SC.length(A,xs) : Nat}:
  match xs:
    case Nil{}: {==}
    case Con{+a,+t}: N.succ_cong(SC.length(A,SC.append(A,t,Con{x,Nil{}})),1n+SC.length(A,t),length_snoc(A,t,x))

def is_empty(-A: Data, xs: List<&2,A>) -> Bool:
  match xs:
    case Nil{}: True{}
    case Con{a,t}: False{}

def empty_drop(-A: Data, +xs: List<&2,A>, +k: Nat) -> {is_empty(A,SC.drop(A,xs,k)) == Nat.is_le(SC.length(A,xs),k) : Bool}:
  match xs k:
    case Nil{} 0n: {==}
    case Nil{} 1n+j: {==}
    case Con{+a,+t} 0n: {==}
    case Con{+a,+t} 1n+j: empty_drop(A,t,j)

def double_add(+p: Nat) -> {Nat.double(p) == Nat.add(p,p) : Nat}:
  match p:
    case 0n: {==}
    case 1n+q:
      %Equal.sym(Nat,Nat.add(q,1n+q),1n+Nat.add(q,q),N.add_succ(q,q)) : {2n+Nat.double(q) == 1n+_ : Nat}
      N.succ_cong(1n+Nat.double(q),1n+Nat.add(q,q),N.succ_cong(Nat.double(q),Nat.add(q,q),double_add(q)))

def sub_double(+p: Nat) -> {Nat.sub(Nat.double(p),p) == p : Nat}:
  %Equal.sym(Nat,Nat.double(p),Nat.add(p,p),double_add(p)) : {Nat.sub(_,p) == p : Nat}
  N.add_sub_cancel(p,p)

# 2^h is strictly above h - 1, i.e. n < 2^(n+1).
def lt_pow2(+n: Nat) -> {Nat.is_lt(n,SC.pow2(n)) == True{} : Bool}:
  match n:
    case 0n: {==}
    case 1n+q:
      N.lt_le_trans(1n+q,1n+SC.pow2(q),Nat.double(SC.pow2(q)),lt_pow2(q),N.double_succ_le(SC.pow2(q),N.pow2_pos(q)))

def lt_pow2_succ(+n: Nat) -> {Nat.is_lt(n,SC.pow2(1n+n)) == True{} : Bool}:
  N.lt_trans(n,SC.pow2(n),SC.pow2(1n+n),lt_pow2(n),N.pow2_lt_succ(n))
