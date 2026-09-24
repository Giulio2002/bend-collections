import Base
import ./spec.bend as S

def writes(~N: Data, ~I: Data, es: List<&2,S.Edit<N,I>>) -> Nat:
  match es:
    case Nil{}: 0n
    case Con{e,rest}: 1n+writes(~N,~I,rest)

# Combined with write refinement: the number of primitive field/root writes
# is bounded independently of list size. Accessor work is application-defined.
def remove_bound(~N: Data, ~I: Data, +r: I, +n: N, +p: Maybe<&2,N>, +q: Maybe<&2,N>) -> {Nat.is_lt(writes(~N,~I,S.remove(N,I,r,n,p,q)),5n) == True{} : Bool}:
  match p q:
    case None{} None{}: {==}
    case None{} Some{b}: {==}
    case Some{a} None{}: {==}
    case Some{a} Some{b}: {==}

def prepend_bound(~N: Data, ~I: Data, +r: I, +n: N, +h: Maybe<&2,N>) -> {Nat.is_lt(writes(~N,~I,S.prepend(N,I,r,n,h)),4n) == True{} : Bool}:
  match h:
    case None{}: {==}
    case Some{a}: {==}
