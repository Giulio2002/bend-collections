import Base
import ../../src/lru/fast.bend as F

def fin_ok(+s: U32, +head: U32, +tail: U32, +free: U32, prevs: Array<U32>, nexts: Array<U32>, +p: U32, +q: U32) -> {F.promote_fin(s,head,tail,free,prevs,nexts,p,q) == F.link_tail(F.ul_fin(head,tail,free,prevs,nexts,p,q),s) : F.Chain}:
  {==}

def q_ok(+s: U32, +head: U32, +tail: U32, +free: U32, prevs: Array<U32>, +p: U32, r: Array<U32> & U32) -> {F.promote_q(s,head,tail,free,prevs,p,r) == F.link_tail(F.ul_q(head,tail,free,prevs,p,r),s) : F.Chain}:
  match r:
    case Tuple{nexts,+q}:
      fin_ok(s,head,tail,free,prevs,nexts,p,q)

def p_ok(+s: U32, +head: U32, +tail: U32, +free: U32, nexts: Array<U32>, r: Array<U32> & U32) -> {F.promote_p(s,head,tail,free,nexts,r) == F.link_tail(F.ul_p(s,head,tail,free,nexts,r),s) : F.Chain}:
  match r:
    case Tuple{prevs,+p}:
      q_ok(s,head,tail,free,prevs,p,Array.get(U32,nexts,s))

def promote_ok(c: F.Chain, +s: U32) -> {F.promote(c,s) == F.link_tail(F.unlink(c,s),s) : F.Chain}:
  match c:
    case F.CH{+head,+tail,+free,prevs,nexts}:
      p_ok(s,head,tail,free,nexts,Array.get(U32,prevs,s))

def original_go(c: F.Chain, +s: U32, newest: Bool) -> F.Chain:
  match newest:
    case True{}: c
    case False{}: F.link_tail(F.unlink(c,s),s)

def touch_go_ok(c: F.Chain, +s: U32, +newest: Bool) -> {F.touch_go(c,s,newest) == original_go(c,s,newest) : F.Chain}:
  match newest:
    case True{}: {==}
    case False{}: promote_ok(c,s)

def original(c: F.Chain, +s: U32) -> F.Chain:
  F.CH{head,+tail,free,prevs,nexts} = c
  original_go(F.CH{head,tail,free,prevs,nexts},s,U32.is_eq(F.link(s),tail))

def touch_ok(c: F.Chain, +s: U32) -> {F.touch(c,s) == original(c,s) : F.Chain}:
  match c:
    case F.CH{head,+tail,free,prevs,nexts}:
      touch_go_ok(F.CH{head,tail,free,prevs,nexts},s,U32.is_eq(F.link(s),tail))


def result(c: F.Chain, +s: U32, out: F.Chain, e: {F.link_tail(F.unlink(c,s),s) == out : F.Chain}) -> {F.promote(c,s) == out : F.Chain}:
  Equal.trans(F.Chain,F.promote(c,s),F.link_tail(F.unlink(c,s),s),out,promote_ok(c,s),e)
