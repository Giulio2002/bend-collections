import Base

# Micro-benchmark behind the heap's slot representation (see WORK_LOG): what
# does wrapping every slot in `Maybe` cost per native array access?
#   op 0: Array<U32>           get + set per iteration
#   op 1: Array<Maybe<U32>>    get + set per iteration
#   op 2: Array<U32>           get only
#   op 3: Array<Maybe<U32>>    get only
#   op 4: Array<Maybe<U32>>    get + set, writing back the cell that was read
# argv = [op, depth, count]; prints the elapsed milliseconds.

def pow2(d: Nat) -> Nat:
  match d:
    case 0n:
      1n
    case 1n+p:
      Nat.double(pow2(p))

def mask(+d: Nat) -> U32:
  U32.sub(U32.from_nat(pow2(d)), 1)

def lcg(s: U32) -> U32:
  U32.add(U32.mul(s, 1664525), 1013904223)

def unwrap(mv: Maybe<&2, U32>) -> U32:
  match mv:
    case None{}:
      7
    case Some{v}:
      v

# A get result has to be carried in a constructor: a def body may not
# destructure a tuple and then match, and definitions may not be mutually
# recursive, so the loop matches on its own state parameter.
type RCell is Type:
  RC{arr: Array<U32>, v: U32}

type MCell is Type:
  MC{arr: Array<Maybe<&2, U32>>, v: Maybe<&2, U32>}

def rcell(g: Array<U32> & U32) -> RCell:
  (arr, v) = g
  RC{arr, v}

def mcell(g: Array<Maybe<&2, U32>> & Maybe<&2, U32>) -> MCell:
  (arr, v) = g
  MC{arr, v}

def raw_rw(k: Nat, +m: U32, +r: U32, c: U32, st: RCell) -> Array<U32> & U32:
  match k st:
    case 0n RC{arr, v}:
      (arr, U32.add(c, v))
    case 1n+p RC{arr, +v}:
      raw_rw(p, m, lcg(r), U32.add(c, v), rcell(Array.get(U32, Array.set(U32, arr, U32.and(r, m), v), U32.and(lcg(r), m))))

def mb_rw(k: Nat, +m: U32, +r: U32, c: U32, st: MCell) -> Array<Maybe<&2, U32>> & U32:
  match k st:
    case 0n MC{arr, v}:
      (arr, U32.add(c, unwrap(v)))
    case 1n+p MC{arr, +v}:
      mb_rw(p, m, lcg(r), U32.add(c, unwrap(v)), mcell(Array.get(Maybe<&2, U32>, Array.set(Maybe<&2, U32>, arr, U32.and(r, m), Some{unwrap(v)}), U32.and(lcg(r), m))))

# the same, writing the cell that was read back instead of a fresh Some
def mb_rw_cell(k: Nat, +m: U32, +r: U32, c: U32, st: MCell) -> Array<Maybe<&2, U32>> & U32:
  match k st:
    case 0n MC{arr, v}:
      (arr, U32.add(c, unwrap(v)))
    case 1n+p MC{arr, +v}:
      mb_rw_cell(p, m, lcg(r), U32.add(c, unwrap(v)), mcell(Array.get(Maybe<&2, U32>, Array.set(Maybe<&2, U32>, arr, U32.and(r, m), v), U32.and(lcg(r), m))))

def raw_ro(k: Nat, +m: U32, +r: U32, c: U32, st: RCell) -> Array<U32> & U32:
  match k st:
    case 0n RC{arr, v}:
      (arr, U32.add(c, v))
    case 1n+p RC{arr, v}:
      raw_ro(p, m, lcg(r), U32.add(c, v), rcell(Array.get(U32, arr, U32.and(lcg(r), m))))

def mb_ro(k: Nat, +m: U32, +r: U32, c: U32, st: MCell) -> Array<Maybe<&2, U32>> & U32:
  match k st:
    case 0n MC{arr, v}:
      (arr, U32.add(c, unwrap(v)))
    case 1n+p MC{arr, v}:
      mb_ro(p, m, lcg(r), U32.add(c, unwrap(v)), mcell(Array.get(Maybe<&2, U32>, arr, U32.and(lcg(r), m))))

def bit(b: Bool) -> U32:
  match b:
    case True{}:
      1
    case False{}:
      0

def cmp_add(c: U32, a: Bool, b: Bool) -> U32:
  U32.add(c, U32.add(bit(a), bit(b)))

# op 5: the comparator path the heap uses, twice per iteration
def cmp_loop(k: Nat, +r: U32, +c: U32) -> U32:
  match k:
    case 0n:
      c
    case 1n+p:
      cmp_loop(p, lcg(r), cmp_add(c, Cmp.is_le(U32.cmp(r, c)), Cmp.is_le(U32.cmp(c, r))))

# op 6: the same loop without the comparisons (the loop's own cost)
def base_loop(k: Nat, +r: U32, c: U32) -> U32:
  match k:
    case 0n:
      c
    case 1n+p:
      base_loop(p, lcg(r), U32.add(c, 1))

def with_n(+n: U32, r: Array<U32> & U32) -> Array<U32> & U32:
  (a2, old) = r
  (a2, n)

def set_at(arr: Array<U32>, +n: U32, i: U32, v: U32) -> Array<U32> & U32:
  with_n(n, Array.swap.at(U32, i, v, (arr, n)))

# op 7: raw get+set through Array.get.at / Array.swap.at with a CACHED size,
# i.e. without the Array.size walk that Array.get/Array.set do first
def cached_rw(k: Nat, +m: U32, +n: U32, +r: U32, c: U32, st: RCell) -> Array<U32> & U32:
  match k st:
    case 0n RC{arr, v}:
      (arr, U32.add(c, v))
    case 1n+p RC{arr, +v}:
      cached_rw(p, m, n, lcg(r), U32.add(c, v), rcell(Array.get.at(U32, U32.and(lcg(r), m), set_at(arr, n, U32.and(r, m), v))))

def fin_raw(p: Array<U32> & U32) -> U32:
  (arr, c) = p
  c

def fin_mb(p: Array<Maybe<&2, U32>> & U32) -> U32:
  (arr, c) = p
  c

def go(+op: U32, +d: Nat, k: Nat) -> U32:
  match op:
    case 0:
      fin_raw(raw_rw(k, mask(d), 12345, 0, rcell(Array.get(U32, Array.new(U32, d, 3), 0))))
    case 1:
      fin_mb(mb_rw(k, mask(d), 12345, 0, mcell(Array.get(Maybe<&2, U32>, Array.new(Maybe<&2, U32>, d, Some{3}), 0))))
    case 2:
      fin_raw(raw_ro(k, mask(d), 12345, 0, rcell(Array.get(U32, Array.new(U32, d, 3), 0))))
    case 3:
      fin_mb(mb_ro(k, mask(d), 12345, 0, mcell(Array.get(Maybe<&2, U32>, Array.new(Maybe<&2, U32>, d, Some{3}), 0))))
    case 7:
      fin_raw(cached_rw(k, mask(d), U32.from_nat(pow2(d)), 12345, 0, rcell(Array.get(U32, Array.new(U32, d, 3), 0))))
    case 5:
      cmp_loop(k, 12345, 0)
    case 6:
      base_loop(k, 12345, 0)
    case _:
      fin_mb(mb_rw_cell(k, mask(d), 12345, 0, mcell(Array.get(Maybe<&2, U32>, Array.new(Maybe<&2, U32>, d, Some{3}), 0))))

def arg(s: String) -> U32:
  Maybe.default(&2, U32, U32.read(s), 0)

def field(parts: List<&2, String>, i: Nat) -> String:
  match parts i:
    case Nil{} _:
      SNil{}
    case Con{s, t} 0n:
      s
    case Con{s, t} 1n+p:
      field(t, p)

def run(+args: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    IO.print_err(U32.show(go(arg(field(args, 0n)), U32.to_nat(arg(field(args, 1n))), U32.to_nat(arg(field(args, 2n))))))
    t1 : Nat <- IO.now()
    IO.print(Nat.show(Nat.sub(t1, t0)))

def shared(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{h, shared(t)}

def main() -> IO(Unit):
  do IO<Unit>:
    raw : List<&1, String> <- IO.args()
    run(shared(raw))
