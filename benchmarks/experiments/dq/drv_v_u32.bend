import Base
import ../../bend/common.bend as B
import ./v_u32.bend as DQ

type St is Type:
  S{rng: U32, chk: U32, dq: DQ.Deque<U32>}

def init(+seed: U32) -> St:
  S{seed, 0, DQ.new(~U32)}

def pb_with(+r: U32, c: U32, d: DQ.Deque<U32>) -> St:
  S{r, B.mix(c, 1), DQ.push_back(~U32, d, r)}

def do_pb(st: St) -> St:
  S{r, c, d} = st
  pb_with(B.lcg(r), c, d)

def null_with(+r: U32, c: U32, d: DQ.Deque<U32>) -> St:
  S{r, B.mix(c, r), d}

def do_null(st: St) -> St:
  S{r, c, d} = st
  null_with(B.lcg(r), c, d)

def loop_null(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_null(p, do_null(st))

def loop_pb(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_pb(p, do_pb(st))

def measured(+op: U32, +k: Nat, st: St) -> St:
  match op:
    case 1:
      loop_pb(k, st)
    case _:
      loop_null(k, st)

def drain(st: St) -> U32:
  S{+r, c, d} = st
  B.mix(c, r)

def round(+op: U32, +size: Nat, +k: Nat, +kn: Nat, +seed: U32) -> U32:
  drain(loop_null(kn, measured(op, k, loop_pb(size, init(seed)))))

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
