import Base
import ./types.bend as T

def xor(a: T.Lane, b: T.Lane) -> T.Lane:
  match a b:
    case T.W{al,ah} T.W{bl,bh}: T.W{U32.xor(al,bl),U32.xor(ah,bh)}

def chi(a: T.Lane, b: T.Lane, c: T.Lane) -> T.Lane:
  match a b c:
    case T.W{al,ah} T.W{bl,bh} T.W{cl,ch}:
      T.W{U32.xor(al,U32.and(U32.xor(bl,4294967295),cl)),U32.xor(ah,U32.and(U32.xor(bh,4294967295),ch))}

def small(+lo: U32, +hi: U32, +n: Nat) -> T.Lane:
  T.W{U32.or(U32.shln(lo,n),U32.shrn(hi,Nat.sub(32n,n))),U32.or(U32.shln(hi,n),U32.shrn(lo,Nat.sub(32n,n)))}

def rotate_if(lo: U32, hi: U32, +n: Nat, b: Bool) -> T.Lane:
  match b:
    case True{}: small(lo,hi,n)
    case False{}: small(hi,lo,Nat.sub(n,32n))

def rotate(s: T.Lane, +n: Nat) -> T.Lane:
  match s n:
    case T.W{lo,hi} 0n: T.W{lo,hi}
    case T.W{lo,hi} 32n: T.W{hi,lo}
    case T.W{lo,hi} n:
      rotate_if(lo,hi,n,Nat.is_lt(n,32n))


# Fixed rotations make constant shifts visible to the native compiler.
def rol0(a: T.Lane) -> T.Lane:
  match a:
    case T.W{+lo,+hi}:
      T.W{lo,hi}

def rol1(a: T.Lane) -> T.Lane:
  match a:
    case T.W{+lo,+hi}:
      T.W{U32.or(U32.shln(lo,1n),U32.shrn(hi,31n)),U32.or(U32.shln(hi,1n),U32.shrn(lo,31n))}

def rol2(a: T.Lane) -> T.Lane:
  match a:
    case T.W{+lo,+hi}:
      T.W{U32.or(U32.shln(lo,2n),U32.shrn(hi,30n)),U32.or(U32.shln(hi,2n),U32.shrn(lo,30n))}

def rol3(a: T.Lane) -> T.Lane:
  match a:
    case T.W{+lo,+hi}:
      T.W{U32.or(U32.shln(lo,3n),U32.shrn(hi,29n)),U32.or(U32.shln(hi,3n),U32.shrn(lo,29n))}

def rol6(a: T.Lane) -> T.Lane:
  match a:
    case T.W{+lo,+hi}:
      T.W{U32.or(U32.shln(lo,6n),U32.shrn(hi,26n)),U32.or(U32.shln(hi,6n),U32.shrn(lo,26n))}

def rol8(a: T.Lane) -> T.Lane:
  match a:
    case T.W{+lo,+hi}:
      T.W{U32.or(U32.shln(lo,8n),U32.shrn(hi,24n)),U32.or(U32.shln(hi,8n),U32.shrn(lo,24n))}

def rol10(a: T.Lane) -> T.Lane:
  match a:
    case T.W{+lo,+hi}:
      T.W{U32.or(U32.shln(lo,10n),U32.shrn(hi,22n)),U32.or(U32.shln(hi,10n),U32.shrn(lo,22n))}

def rol14(a: T.Lane) -> T.Lane:
  match a:
    case T.W{+lo,+hi}:
      T.W{U32.or(U32.shln(lo,14n),U32.shrn(hi,18n)),U32.or(U32.shln(hi,14n),U32.shrn(lo,18n))}

def rol15(a: T.Lane) -> T.Lane:
  match a:
    case T.W{+lo,+hi}:
      T.W{U32.or(U32.shln(lo,15n),U32.shrn(hi,17n)),U32.or(U32.shln(hi,15n),U32.shrn(lo,17n))}

def rol18(a: T.Lane) -> T.Lane:
  match a:
    case T.W{+lo,+hi}:
      T.W{U32.or(U32.shln(lo,18n),U32.shrn(hi,14n)),U32.or(U32.shln(hi,18n),U32.shrn(lo,14n))}

def rol20(a: T.Lane) -> T.Lane:
  match a:
    case T.W{+lo,+hi}:
      T.W{U32.or(U32.shln(lo,20n),U32.shrn(hi,12n)),U32.or(U32.shln(hi,20n),U32.shrn(lo,12n))}

def rol21(a: T.Lane) -> T.Lane:
  match a:
    case T.W{+lo,+hi}:
      T.W{U32.or(U32.shln(lo,21n),U32.shrn(hi,11n)),U32.or(U32.shln(hi,21n),U32.shrn(lo,11n))}

def rol25(a: T.Lane) -> T.Lane:
  match a:
    case T.W{+lo,+hi}:
      T.W{U32.or(U32.shln(lo,25n),U32.shrn(hi,7n)),U32.or(U32.shln(hi,25n),U32.shrn(lo,7n))}

def rol27(a: T.Lane) -> T.Lane:
  match a:
    case T.W{+lo,+hi}:
      T.W{U32.or(U32.shln(lo,27n),U32.shrn(hi,5n)),U32.or(U32.shln(hi,27n),U32.shrn(lo,5n))}

def rol28(a: T.Lane) -> T.Lane:
  match a:
    case T.W{+lo,+hi}:
      T.W{U32.or(U32.shln(lo,28n),U32.shrn(hi,4n)),U32.or(U32.shln(hi,28n),U32.shrn(lo,4n))}

def rol36(a: T.Lane) -> T.Lane:
  match a:
    case T.W{+lo,+hi}:
      T.W{U32.or(U32.shln(hi,4n),U32.shrn(lo,28n)),U32.or(U32.shln(lo,4n),U32.shrn(hi,28n))}

def rol39(a: T.Lane) -> T.Lane:
  match a:
    case T.W{+lo,+hi}:
      T.W{U32.or(U32.shln(hi,7n),U32.shrn(lo,25n)),U32.or(U32.shln(lo,7n),U32.shrn(hi,25n))}

def rol41(a: T.Lane) -> T.Lane:
  match a:
    case T.W{+lo,+hi}:
      T.W{U32.or(U32.shln(hi,9n),U32.shrn(lo,23n)),U32.or(U32.shln(lo,9n),U32.shrn(hi,23n))}

def rol43(a: T.Lane) -> T.Lane:
  match a:
    case T.W{+lo,+hi}:
      T.W{U32.or(U32.shln(hi,11n),U32.shrn(lo,21n)),U32.or(U32.shln(lo,11n),U32.shrn(hi,21n))}

def rol44(a: T.Lane) -> T.Lane:
  match a:
    case T.W{+lo,+hi}:
      T.W{U32.or(U32.shln(hi,12n),U32.shrn(lo,20n)),U32.or(U32.shln(lo,12n),U32.shrn(hi,20n))}

def rol45(a: T.Lane) -> T.Lane:
  match a:
    case T.W{+lo,+hi}:
      T.W{U32.or(U32.shln(hi,13n),U32.shrn(lo,19n)),U32.or(U32.shln(lo,13n),U32.shrn(hi,19n))}

def rol55(a: T.Lane) -> T.Lane:
  match a:
    case T.W{+lo,+hi}:
      T.W{U32.or(U32.shln(hi,23n),U32.shrn(lo,9n)),U32.or(U32.shln(lo,23n),U32.shrn(hi,9n))}

def rol56(a: T.Lane) -> T.Lane:
  match a:
    case T.W{+lo,+hi}:
      T.W{U32.or(U32.shln(hi,24n),U32.shrn(lo,8n)),U32.or(U32.shln(lo,24n),U32.shrn(hi,8n))}

def rol61(a: T.Lane) -> T.Lane:
  match a:
    case T.W{+lo,+hi}:
      T.W{U32.or(U32.shln(hi,29n),U32.shrn(lo,3n)),U32.or(U32.shln(lo,29n),U32.shrn(hi,3n))}

def rol62(a: T.Lane) -> T.Lane:
  match a:
    case T.W{+lo,+hi}:
      T.W{U32.or(U32.shln(hi,30n),U32.shrn(lo,2n)),U32.or(U32.shln(lo,30n),U32.shrn(hi,2n))}

