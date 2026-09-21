import Base
import ./model.bend as T
import ./wide.bend as W

def add(a: T.Int64, b: T.Int64) -> T.Int64:
  match a b:
    case T.I64{x} T.I64{y}:
      T.I64{W.add(x, y)}

def milliseconds(ns: T.Int64) -> T.Int64:
  T.I64{w} = ns
  T.I64{W.milliseconds(w)}

def is_zero(t: T.Int64) -> Bool:
  T.I64{w} = t
  W.is_zero(64n, w)

def deadline_choose(now: T.Int64, ns: T.Int64, immortal: Bool) -> T.Int64:
  match immortal:
    case True{}:
      T.I64{W.zero()}
    case False{}:
      add(now, milliseconds(ns))

def deadline(now: T.Int64, +ns: T.Int64) -> T.Int64:
  deadline_choose(now, ns, is_zero(ns))

def le(a: T.Int64, b: T.Int64) -> Bool:
  match a b:
    case T.I64{x} T.I64{y}:
      W.le(x, y)

def expired_choose(d: T.Int64, now: T.Int64, immortal: Bool) -> Bool:
  match immortal:
    case True{}:
      False{}
    case False{}:
      le(d, now)

def expired(+deadline: T.Int64, now: T.Int64) -> Bool:
  expired_choose(deadline, now, is_zero(deadline))
