import Base
import ../../../src/crypto/subtle.bend as Subtle

def show(b: Bool) -> String:
  match b:
    case True{}:
      "1"
    case False{}:
      "0"

# Expected: 1 1 0 0 0 0 1 0
def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(show(Subtle.eq([], [])))
    IO.print(show(Subtle.eq([1, 2, 3], [1, 2, 3])))
    IO.print(show(Subtle.eq([1, 2, 3], [1, 2, 4])))
    IO.print(show(Subtle.eq([0, 2, 3], [1, 2, 3])))
    IO.print(show(Subtle.eq([1, 2], [1, 2, 3])))
    IO.print(show(Subtle.eq([1, 2, 3], [])))
    IO.print(show(Subtle.eq([255, 0, 128], [255, 0, 128])))
    IO.print(show(Subtle.eq([255, 0, 128], [255, 0, 129])))
