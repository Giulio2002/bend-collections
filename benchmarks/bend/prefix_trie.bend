import Base
import ./common.bend as B
import ../../src/prefix_trie.bend as PT
import ../../types/balanced_search_tree.bend as BE
import ../../types/prefix_trie.bend as E

# Native benchmark driver for src/prefix_trie.bend (U32 values).
# argv = [op, size, count, reps, seed]; benchmarks/native/prefix_trie.c performs the
# identical work. Keys are ten characters drawn from a four-letter alphabet
# ('a'..'d'), two bits of the value stream per character (the bit positions
# wrap at 30, so ten characters fit in one U32 draw), giving about a million
# distinct keys with heavy prefix sharing; `size` is the number of keys
# inserted while building.
# Op selectors: 0 insert, 1 lookup, 2 remove, 3 contains, 4 prefix_entries,
# 5 longest_prefix, 6 new, anything else = value-stream only.

type St is Data:
  S{rng: U32, chk: U32, t: PT.PrefixTrie<U32>}

def init(+seed: U32) -> St:
  S{seed, 0, PT.new(U32)}

def klen() -> Nat:
  10n

# Character i of the key spelled by r: two bits of the stream, 'a' = 97.
# Position i always reads the same bits, so key_of(2, r) really is a prefix of
# key_of(6, r).
def char_at(+i: Nat, +r: U32) -> U32:
  U32.add(97, U32.mod(U32.shrn(r, Nat.mod(Nat.add(16n, Nat.mul(2n, i)), 30n)), 4))

def key_go(m: Nat, +i: Nat, +r: U32) -> String:
  match m:
    case 0n:
      SNil{}
    case 1n+p:
      SCon{Chr{char_at(i, r)}, key_go(p, 1n+i, r)}

def key_of(m: Nat, +r: U32) -> String:
  key_go(m, 0n, r)

def val_code(x: Result<&2, &2, E.Error, U32>) -> U32:
  match x:
    case Fail{e}:
      9
    case Done{v}:
      v

def fold_key(k: String, c: U32) -> U32:
  match k:
    case SNil{}:
      c
    case SCon{Chr{x}, t}:
      fold_key(t, B.mix(c, x))

def entry_code(c: U32, x: Result<&2, &2, E.Error, BE.Entry<String, U32>>) -> U32:
  match x:
    case Fail{e}:
      B.mix(c, 9)
    case Done{BE.Entry{k, v}}:
      B.mix(fold_key(k, c), v)

def fold_entries(xs: List<&2, BE.Entry<String, U32>>, c: U32) -> U32:
  match xs:
    case Nil{}:
      c
    case Con{BE.Entry{k, v}, t}:
      fold_entries(t, B.mix(fold_key(k, c), v))

def fin_val(r: U32, c: U32, p: PT.PrefixTrie<U32> & Result<&2, &2, E.Error, U32>) -> St:
  (t, x) = p
  S{r, B.mix(c, val_code(x)), t}

def ins_with(+r: U32, c: U32, t: PT.PrefixTrie<U32>, +m: Nat) -> St:
  S{r, B.mix(c, 1), PT.insert(U32, t, key_of(m, r), r)}

def do_ins(st: St) -> St:
  S{r, c, t} = st
  ins_with(B.lcg(r), c, t, klen())

def rm_with(+r: U32, c: U32, t: PT.PrefixTrie<U32>, +m: Nat) -> St:
  fin_val(r, c, PT.remove(U32, t, key_of(m, r)))

def do_rm(st: St) -> St:
  S{r, c, t} = st
  rm_with(B.lcg(r), c, t, klen())

# ---- restoring pair ----
#
# `remove` cannot be measured on its own: a round can only remove what it
# built, so the measured batch is at most `size` operations while the round
# also pays for building those `size` keys, and the difference A - B never
# rises above the clock noise of the build (benchmarks/run.py documents the
# rule). `remove` is therefore measured inside a pair that inserts the SAME
# key first, so the trie keeps its size and the batch can be made as long as
# needed. The reported nanoseconds are the PAIR's, charged to `remove`: this
# over-charges the Bend side by one insert, it never flatters it, and the C
# reference runs the identical pair. Both sides spell the key twice, once per
# operation, exactly as the two operations do on their own.

def pair_rm_with(+r: U32, c: U32, t: PT.PrefixTrie<U32>, +m: Nat) -> St:
  fin_val(r, B.mix(c, 1), PT.remove(U32, PT.insert(U32, t, key_of(m, r), r), key_of(m, r)))

def do_pair_rm(st: St) -> St:
  S{r, c, t} = st
  pair_rm_with(B.lcg(r), c, t, klen())

def look_with(+r: U32, c: U32, +t: PT.PrefixTrie<U32>, +m: Nat) -> St:
  S{r, B.mix(c, val_code(PT.lookup(U32, t, key_of(m, r)))), t}

def do_look(st: St) -> St:
  S{r, c, +t} = st
  look_with(B.lcg(r), c, t, klen())

def bool_bit(b: Bool) -> U32:
  match b:
    case True{}:
      1
    case False{}:
      0

def has_with(+r: U32, c: U32, +t: PT.PrefixTrie<U32>, +m: Nat) -> St:
  S{r, B.mix(c, bool_bit(PT.contains(U32, t, key_of(m, r)))), t}

def do_has(st: St) -> St:
  S{r, c, +t} = st
  has_with(B.lcg(r), c, t, klen())

# a two-character prefix
def pre_with(+r: U32, c: U32, +t: PT.PrefixTrie<U32>) -> St:
  S{r, fold_entries(PT.prefix_entries(U32, t, key_of(2n, r)), c), t}

def do_pre(st: St) -> St:
  S{r, c, +t} = st
  pre_with(B.lcg(r), c, t)

def lp_with(+r: U32, c: U32, +t: PT.PrefixTrie<U32>, +m: Nat) -> St:
  S{r, entry_code(c, PT.longest_prefix(U32, t, key_of(m, r))), t}

def do_lp(st: St) -> St:
  S{r, c, +t} = st
  lp_with(B.lcg(r), c, t, klen())

def new_code(m: Maybe<&2, U32>) -> U32:
  match m:
    case None{}:
      0
    case Some{v}:
      v

def do_new(st: St) -> St:
  S{r, c, t} = st
  S{B.lcg(r), B.mix(c, new_code(PT.get(U32, PT.new(U32), SNil{}))), t}

def do_null(st: St) -> St:
  S{r, c, t} = st
  +r2 = B.lcg(r)
  S{r2, B.mix(c, r2), t}

# ---- loops ----

def loop_null(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_null(p, do_null(st))

def loop_ins(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_ins(p, do_ins(st))

def loop_rm(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_rm(p, do_rm(st))

def loop_pair_rm(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_pair_rm(p, do_pair_rm(st))

def loop_look(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_look(p, do_look(st))

def loop_has(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_has(p, do_has(st))

def loop_pre(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_pre(p, do_pre(st))

def loop_lp(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_lp(p, do_lp(st))

def loop_new(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_new(p, do_new(st))

def measured(+op: U32, +k: Nat, st: St) -> St:
  match op:
    case 0:
      loop_ins(k, st)
    case 1:
      loop_look(k, st)
    case 2:
      loop_rm(k, st)
    case 3:
      loop_has(k, st)
    case 4:
      loop_pre(k, st)
    case 5:
      loop_lp(k, st)
    case 6:
      loop_new(k, st)
    case 7:
      loop_pair_rm(k, st)
    case _:
      loop_null(k, st)

# ---- settle / drain ----

def settle(st: St) -> St:
  S{r, c, +t} = st
  S{r, fold_entries(PT.prefix_entries(U32, t, SNil{}), c), t}

# The drain is deliberately independent of how many elements the measured
# operation added or removed, so region A and region B pay the same
# observation cost and the difference is the measured operation alone. Every
# measured operation folds its own result into the checksum inside the loop,
# and `settle` forces the built structure before the loop starts.
def drain_loop(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      drain_loop(p, do_look(st))

def drain_end(st: St) -> U32:
  S{r, c, t} = st
  c

def drain(st: St) -> U32:
  S{+r, c, t} = st
  drain_end(drain_loop(16n, S{r, B.mix(c, r), t}))

# One round: build a structure of `size`, settle it, run `k` measured
# operations, then `kn` value-stream steps, then destroy it. The three timed
# regions below run this same round with the SAME total number of loop
# iterations, so the build, the settle, the loop barrier, the argument
# generation and the destruction all cancel in the differences.
def round(+op: U32, +size: Nat, +k: Nat, +kn: Nat, +seed: U32) -> U32:
  drain(loop_null(kn, measured(op, k, settle(loop_ins(size, init(seed))))))

def reps_go(reps: Nat, +op: U32, +size: Nat, +k: Nat, +kn: Nat, +seed: U32, acc: U32) -> U32:
  match reps:
    case 0n:
      acc
    case 1n+ +p:
      reps_go(p, op, size, k, kn, seed, B.mix(acc, round(op, size, k, kn, U32.add(seed, U32.from_nat(p)))))

def regions(+args: List<&2, String>, +k: Nat, +kn: Nat) -> U32:
  reps_go(U32.to_nat(B.arg(B.field(args, 3n))), B.arg(B.field(args, 0n)),
          U32.to_nat(B.arg(B.field(args, 1n))), k, kn,
          B.arg(B.field(args, 4n)), 0)

def kof(+args: List<&2, String>) -> Nat:
  U32.to_nat(B.arg(B.field(args, 2n)))

# A = 2k measured operations, B = k measured operations, C = none at all (the
# build-and-destroy control). A - B is exactly k x reps measured operations:
# the build, the settle and the destruction cancel, and -- unlike a two-region
# "operations against no operations" difference -- BOTH regions end in a state
# the operation has been applied to, so a size-changing operation can no
# longer move deallocation work out of the difference. C is reported next to
# every row: it is what one region costs with no measured operation at all,
# so a difference that is small beside its own build is visible as such.
def run_a(+args: List<&2, String>) -> U32:
  regions(args, Nat.add(kof(args), kof(args)), 0n)

def run_b(+args: List<&2, String>) -> U32:
  regions(args, kof(args), 0n)

def run_c(+args: List<&2, String>) -> U32:
  regions(args, 0n, 0n)

# Checksums go to stderr (printing them is what forces each region), the three
# elapsed millisecond counts to stdout. argv[5] picks the ORDER in which the
# three regions run: a machine that drifts (frequency scaling, thermal) makes
# whatever runs last look slower, which is a systematic bias of exactly the
# shape the A - B difference measures. The runner alternates the order over
# the samples and reports the median, so a monotone drift cancels.
def go_abc(+args: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    IO.print_err(U32.show(run_a(args)))
    t1 : Nat <- IO.now()
    d1 : Nat = Nat.sub(t1, t0)
    t2 : Nat <- IO.now()
    IO.print_err(U32.show(run_b(args)))
    t3 : Nat <- IO.now()
    d2 : Nat = Nat.sub(t3, t2)
    t4 : Nat <- IO.now()
    IO.print_err(U32.show(run_c(args)))
    t5 : Nat <- IO.now()
    IO.print(B.times(d1, d2, Nat.sub(t5, t4)))

def go_cba(+args: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    IO.print_err(U32.show(run_c(args)))
    t1 : Nat <- IO.now()
    d3 : Nat = Nat.sub(t1, t0)
    t2 : Nat <- IO.now()
    IO.print_err(U32.show(run_b(args)))
    t3 : Nat <- IO.now()
    d2 : Nat = Nat.sub(t3, t2)
    t4 : Nat <- IO.now()
    IO.print_err(U32.show(run_a(args)))
    t5 : Nat <- IO.now()
    IO.print(B.times(Nat.sub(t5, t4), d2, d3))

def pick(+o: U32, +args: List<&2, String>) -> IO(Unit):
  match o:
    case 0:
      go_abc(args)
    case _:
      go_cba(args)

def go(+args: List<&2, String>) -> IO(Unit):
  pick(B.arg(B.field(args, 5n)), args)

def main() -> IO(Unit):
  do IO<Unit>:
    raw : List<String> <- IO.args()
    go(B.shared(raw))
