# Shared body of the HashMap vs Base.Map drivers: the operations of
# benchmarks/bend/hash_table.bend over the adapter T (see *.head).
# argv = [op, size, count, reps, seed, order]; ops 0 set, 1 get, 2 has,
# 3 pop+set, 4 size, 5 keys, 6 build.

type St is Type:
  S{rng: U32, chk: U32, t: T}

def key(+i: U32) -> String:
  SCon{Chr{U32.add(i, 65536)}, SNil{}}

def bit(b: Bool) -> U32:
  match b:
    case True{}:
      1
    case False{}:
      0

def draw(+r: U32, +size: U32) -> U32:
  U32.mod(r, U32.inc(size))

def build_go(k: Nat, t: T, +i: U32) -> T:
  match k:
    case 0n:
      t
    case 1n+p:
      build_go(p, t_set(t, key(i), U32.inc(i)), U32.inc(i))

def build(+size: U32) -> T:
  build_go(U32.to_nat(size), t_new(), 0)

def fin_num(+r: U32, c: U32, p: T & U32) -> St:
  (t, x) = p
  S{r, B.mix(c, x), t}

def fin_bit(+r: U32, c: U32, p: T & Bool) -> St:
  (t, b) = p
  S{r, B.mix(c, bit(b)), t}

def op_set(st: St, +size: U32) -> St:
  S{r0, c, t} = st
  +r = B.lcg(r0)
  S{r, B.mix(c, r), t_set(t, key(draw(r, size)), r)}

def op_get(st: St, +size: U32) -> St:
  S{r0, c, t} = st
  +r = B.lcg(r0)
  fin_num(r, c, t_get(t, key(draw(r, size))))

def op_has(st: St, +size: U32) -> St:
  S{r0, c, t} = st
  +r = B.lcg(r0)
  fin_bit(r, c, t_has(t, key(draw(r, size))))

def val_or0(m: Maybe<&2, U32>) -> U32:
  match m:
    case None{}:
      0
    case Some{v}:
      v

def ps_fin(+r: U32, c: U32, +i: U32, p: T & Maybe<&2, U32>) -> St:
  (t, m) = p
  S{r, B.mix(c, val_or0(m)), t_set(t, key(i), U32.inc(i))}

def op_pop_set(st: St, +size: U32) -> St:
  S{r0, c, t} = st
  +r = B.lcg(r0)
  +i = draw(r, size)
  ps_fin(r, c, i, t_pop(t, key(i)))

def op_size(st: St) -> St:
  S{r0, c, t} = st
  fin_num(B.lcg(r0), c, t_size(t))

def code_of(s: String) -> U32:
  match s:
    case SNil{}:
      0
    case SCon{Chr{x}, t}:
      x

def fold_ks(ks: List<&2, String>, +cnt: U32, +sum: U32, c: U32) -> U32:
  match ks:
    case Nil{}:
      B.mix(B.mix(c, cnt), sum)
    case Con{k, t}:
      fold_ks(t, U32.inc(cnt), U32.add(sum, code_of(k)), c)

def keys_fin(+r: U32, c: U32, p: T & List<&2, String>) -> St:
  (t, ks) = p
  S{r, fold_ks(ks, 0, 0, c), t}

def op_keys(st: St) -> St:
  S{r0, c, t} = st
  keys_fin(B.lcg(r0), c, t_keys(t))

def size_only(p: T & U32) -> U32:
  (g, n) = p
  n

def op_build(st: St, +size: U32) -> St:
  S{r0, c, t} = st
  S{B.lcg(r0), B.mix(c, size_only(t_get(build(size), key(0)))), t}

def op_null(st: St) -> St:
  S{r0, c, t} = st
  +r = B.lcg(r0)
  S{r, B.mix(c, r), t}

def loop_set(k: Nat, +n: U32, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_set(p, n, op_set(st, n))

def loop_get(k: Nat, +n: U32, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_get(p, n, op_get(st, n))

def loop_has(k: Nat, +n: U32, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_has(p, n, op_has(st, n))

def loop_pop_set(k: Nat, +n: U32, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_pop_set(p, n, op_pop_set(st, n))

def loop_size(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_size(p, op_size(st))

def loop_keys(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_keys(p, op_keys(st))

def loop_build(k: Nat, +n: U32, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_build(p, n, op_build(st, n))

def loop_null(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_null(p, op_null(st))

def measured(+op: U32, +k: Nat, +n: U32, st: St) -> St:
  match op:
    case 0:
      loop_set(k, n, st)
    case 1:
      loop_get(k, n, st)
    case 2:
      loop_has(k, n, st)
    case 3:
      loop_pop_set(k, n, st)
    case 4:
      loop_size(k, st)
    case 5:
      loop_keys(k, st)
    case 6:
      loop_build(k, n, st)
    case _:
      loop_null(k, st)

def settle_fin(+seed: U32, p: T & U32) -> St:
  (t, n) = p
  S{seed, B.mix(0, n), t}

def init(+seed: U32, +size: U32) -> St:
  settle_fin(seed, t_size(build(size)))

def drain_end(p: T & U32, c: U32) -> U32:
  (t, n) = p
  B.mix(c, n)

def drain_fin(st: St) -> U32:
  S{r, c, t} = st
  drain_end(t_size(t), c)

def drain_loop(k: Nat, +n: U32, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      drain_loop(p, n, op_get(st, n))

def drain(+size: U32, st: St) -> U32:
  S{+r, c, t} = st
  drain_fin(drain_loop(16n, size, S{r, B.mix(c, r), t}))

def round(+op: U32, +size: U32, +k: Nat, +seed: U32) -> U32:
  drain(size, measured(op, k, size, init(seed, size)))

def reps_go(reps: Nat, +op: U32, +size: U32, +k: Nat, +seed: U32, acc: U32) -> U32:
  match reps:
    case 0n:
      acc
    case 1n+ +p:
      reps_go(p, op, size, k, seed, B.mix(acc, round(op, size, k, U32.add(seed, U32.from_nat(p)))))

def regions(+g: B.Args, +k: Nat) -> U32:
  reps_go(U32.to_nat(B.a_reps(g)), B.a_op(g), B.a_size(g), k, B.a_seed(g), 0)

def kof(+g: B.Args) -> Nat:
  U32.to_nat(B.a_count(g))

def run_a(+g: B.Args) -> U32:
  regions(g, Nat.add(kof(g), kof(g)))

def run_b(+g: B.Args) -> U32:
  regions(g, kof(g))

def run_c(+g: B.Args) -> U32:
  regions(g, 0n)

def go_abc(+g: B.Args) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    IO.print_err(U32.show(run_a(g)))
    t1 : Nat <- IO.now()
    d1 : Nat = Nat.sub(t1, t0)
    t2 : Nat <- IO.now()
    IO.print_err(U32.show(run_b(g)))
    t3 : Nat <- IO.now()
    d2 : Nat = Nat.sub(t3, t2)
    t4 : Nat <- IO.now()
    IO.print_err(U32.show(run_c(g)))
    t5 : Nat <- IO.now()
    IO.print(B.times(d1, d2, Nat.sub(t5, t4)))

def go_cba(+g: B.Args) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    IO.print_err(U32.show(run_c(g)))
    t1 : Nat <- IO.now()
    d3 : Nat = Nat.sub(t1, t0)
    t2 : Nat <- IO.now()
    IO.print_err(U32.show(run_b(g)))
    t3 : Nat <- IO.now()
    d2 : Nat = Nat.sub(t3, t2)
    t4 : Nat <- IO.now()
    IO.print_err(U32.show(run_a(g)))
    t5 : Nat <- IO.now()
    IO.print(B.times(Nat.sub(t5, t4), d2, d3))

def pick(+o: U32, +g: B.Args) -> IO(Unit):
  match o:
    case 0:
      go_abc(g)
    case _:
      go_cba(g)

def go(+g: B.Args) -> IO(Unit):
  pick(B.a_order(g), g)

def main() -> IO(Unit):
  do IO<Unit>:
    raw : List<String> <- IO.args()
    go(B.parse(raw))
