import Base
import ../../src/lru.bend as LRU
import ../../reference/lru/src/cache.bend as C
import ../../reference/lru/src/driver.bend as D
import ../../reference/lru/src/public.bend as Pub
import ../../reference/lru/spec/clock.bend as Clock
import ../../reference/lru/types/model.bend as T
import ../support/text.bend as X

# Smoke driver for the reused LRU (through the src/lru.bend entry only).
# argv = [capacity, op tokens...]; String keys, Nat values; every clock read
# is answered with time 0 (entries use the default lifetime).
# Tokens: add:k:v | get:k | peek:k | has:k | rm:k | len | keys | oldest | rmold
# Output: "BOOL true/false" | "VAL v" | "MISS" | "OLD k=v" | "NONE" |
# "LEN n" | "KEYS a,b" | "OK" | "FAIL" (clock failure) | "CTOR error".

def bool_text(b: Bool) -> String:
  match b:
    case True{}:
      "BOOL true"
    case False{}:
      "BOOL false"

def value_text(v: Nat, found: Bool) -> String:
  match found:
    case True{}:
      "VAL " ++ Nat.show(v)
    case False{}:
      "MISS"

def oldest_text(k: String, v: Nat, found: Bool) -> String:
  match found:
    case True{}:
      "OLD " ++ k ++ "=" ++ Nat.show(v)
    case False{}:
      "NONE"

def answer(a: Pub.Answer<String, Nat>) -> String:
  match a:
    case Pub.Boolean{b}:
      bool_text(b)
    case Pub.Value{v, found}:
      value_text(v, found)
    case Pub.Oldest{k, v, found}:
      oldest_text(k, v, found)
    case Pub.KeyList{ks}:
      "KEYS " ++ String.join(ks, ",")
    case Pub.Length{n}:
      "LEN " ++ Nat.show(n)
    case _:
      "OK"

def outcome(o: D.Outcome<String, Nat>) -> String:
  match o:
    case D.Returned{c, a, events, n}:
      answer(a)
    case D.Failed{c, e, events, n}:
      "FAIL"

def outs(xs: List<&2, D.Outcome<String, Nat>>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{outcome(h), outs(t)}

def try_rmold(hit: Bool) -> Pub.Request<String, Nat>:
  match hit:
    case True{}:
      Pub.RemoveOldest{}
    case False{}:
      Pub.Len{}

def try_oldest(hit: Bool, +n: String) -> Pub.Request<String, Nat>:
  match hit:
    case True{}:
      Pub.GetOldest{}
    case False{}:
      try_rmold(String.eq(n, "rmold"))

def try_keys(hit: Bool, +n: String) -> Pub.Request<String, Nat>:
  match hit:
    case True{}:
      Pub.Keys{}
    case False{}:
      try_oldest(String.eq(n, "oldest"), n)

def try_rm(hit: Bool, +n: String, +p: List<&2, String>) -> Pub.Request<String, Nat>:
  match hit:
    case True{}:
      Pub.Remove{X.field(p, 1n)}
    case False{}:
      try_keys(String.eq(n, "keys"), n)

def try_has(hit: Bool, +n: String, +p: List<&2, String>) -> Pub.Request<String, Nat>:
  match hit:
    case True{}:
      Pub.Contains{X.field(p, 1n)}
    case False{}:
      try_rm(String.eq(n, "rm"), n, p)

def try_peek(hit: Bool, +n: String, +p: List<&2, String>) -> Pub.Request<String, Nat>:
  match hit:
    case True{}:
      Pub.Peek{X.field(p, 1n)}
    case False{}:
      try_has(String.eq(n, "has"), n, p)

def try_get(hit: Bool, +n: String, +p: List<&2, String>) -> Pub.Request<String, Nat>:
  match hit:
    case True{}:
      Pub.Get{X.field(p, 1n)}
    case False{}:
      try_peek(String.eq(n, "peek"), n, p)

def try_add(hit: Bool, +n: String, +p: List<&2, String>) -> Pub.Request<String, Nat>:
  match hit:
    case True{}:
      Pub.Add{X.field(p, 1n), X.nat_field(p, 2n)}
    case False{}:
      try_get(String.eq(n, "get"), n, p)

def parse(t: String) -> Pub.Request<String, Nat>:
  +p = X.fields(t)
  +n = X.field(p, 0n)
  try_add(String.eq(n, "add"), n, p)

def parse_all(xs: List<&2, String>) -> List<&2, Pub.Request<String, Nat>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{parse(h), parse_all(t)}

# Enough zero-time clock samples for every request.
def zeros(n: Nat) -> List<&2, Clock.Event>:
  match n:
    case 0n:
      Nil{}
    case 1n+k:
      Con{Clock.Sample{T.I64{Word.zero(64n)}}, zeros(k)}

def trace_lines(t: D.Trace<String, Nat>) -> List<&2, String>:
  match t:
    case D.Ran{c, events, outcomes, n}:
      outs(outcomes)

def run_with(r: Result<&2, &2, String, C.Cache<String, Nat>>, +reqs: List<&2, Pub.Request<String, Nat>>) -> List<&2, String>:
  match r:
    case Fail{e}:
      Con{"CTOR " ++ e, Nil{}}
    case Done{c}:
      trace_lines(LRU.run(Nat, reqs, c, "", 0n, zeros(Nat.mul(8n, 1n+List.length(&2, Pub.Request<String, Nat>, reqs)))))

def start(args: List<&2, String>) -> List<&2, String>:
  match args:
    case Nil{}:
      Nil{}
    case Con{cap, ops}:
      run_with(LRU.new(Nat, X.u32_of(cap)), parse_all(ops))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    X.print_lines(start(X.shared(args)))
