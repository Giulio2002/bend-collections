import Base

# docs/BACKEND_BUGS.md, "recursion-depth". A recursion that is not a tail call
# is bounded by the machine stack on the JavaScript lanes and by the heap on
# the native one: the native build prints 1000000, `bend recursion_depth.bend`
# and the JavaScript build stop with "memory fault (machine stack overflow?)".

def deep(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      1n+deep(p)

# the depth: the first argument, or 1000000
def depth(args: List<String>) -> Nat:
  match args:
    case Con{program, Con{n, rest}}:
      Maybe.default(&2, Nat, Nat.read(n), 1000000n)
    case _:
      1000000n

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    IO.print(Nat.show(deep(depth(args))))
