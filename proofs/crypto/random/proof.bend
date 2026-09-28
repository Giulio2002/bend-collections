import Base
import ../../../src/math/u64.bend as W
import ../../../src/math/w64.bend as X
import ../../../src/math/random/chacha8.bend as C8
import ../../../src/math/random/chacha8/block.bend as B
import ../../../src/crypto/random.bend as CR
import ../../../spec/math/random/source.bend as SRC
import ../../../spec/math/random/chacha8rand.bend as SC
import ../../../spec/math/random.bend as SRM
import ../../../spec/crypto/random.bend as SCR
import ../../math/random/proof.bend as MR
import ./bytes.bend as BY

# Entry point: `bend proofs/crypto/random/proof.bend` checks every clause of
# spec/crypto/random.bend under its name, for every input.

def kp_fst(+p: List<&2, U32>, q: W.U64 & C8.ChaCha8) -> {SRC.fst64(CR.Gen, CR.keep_pending(p, q)) == SRC.fst64(C8.ChaCha8, q) : W.U64}:
  match q:
    case Tuple{x, c}:
      {==}

def kp_snd(+p: List<&2, U32>, q: W.U64 & C8.ChaCha8) -> {SRC.snd64(CR.Gen, CR.keep_pending(p, q)) == CR.G{SRC.snd64(C8.ChaCha8, q), p} : CR.Gen}:
  match q:
    case Tuple{x, c}:
      {==}

# the generator's outputs are its ChaCha8's; pending bytes are only for bytes
def gen_outputs(+n: Nat, +c: C8.ChaCha8, +p: List<&2, U32>) -> {SRC.outputs(~CR.Gen, ~CR.next, n, CR.G{c, p}) == SRC.outputs(~C8.ChaCha8, ~C8.next, n, c) : List<&2, W.U64>}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      %Equal.sym(W.U64, SRC.fst64(CR.Gen, CR.keep_pending(p, C8.next(c))), SRC.fst64(C8.ChaCha8, C8.next(c)), kp_fst(p, C8.next(c))) : {Con{_, SRC.outputs(~CR.Gen, ~CR.next, m, SRC.snd64(CR.Gen, CR.keep_pending(p, C8.next(c))))} == SRC.outputs(~C8.ChaCha8, ~C8.next, 1n+m, c) : List<&2, W.U64>}
      %Equal.sym(CR.Gen, SRC.snd64(CR.Gen, CR.keep_pending(p, C8.next(c))), CR.G{SRC.snd64(C8.ChaCha8, C8.next(c)), p}, kp_snd(p, C8.next(c))) : {Con{SRC.fst64(C8.ChaCha8, C8.next(c)), SRC.outputs(~CR.Gen, ~CR.next, m, _)} == SRC.outputs(~C8.ChaCha8, ~C8.next, 1n+m, c) : List<&2, W.U64>}
      Equal.cong(List<&2, W.U64>, List<&2, W.U64>, l => Con{SRC.fst64(C8.ChaCha8, C8.next(c)), l}, SRC.outputs(~CR.Gen, ~CR.next, m, CR.G{SRC.snd64(C8.ChaCha8, C8.next(c)), p}), SRC.outputs(~C8.ChaCha8, ~C8.next, m, SRC.snd64(C8.ChaCha8, C8.next(c))), gen_outputs(m, SRC.snd64(C8.ChaCha8, C8.next(c)), p))

def Random.stream(+n: Nat, +k0: U32, +k1: U32, +k2: U32, +k3: U32, +k4: U32, +k5: U32, +k6: U32, +k7: U32) -> SCR.Random.stream(n, k0, k1, k2, k3, k4, k5, k6, k7):
  +k = {B.K{k0, k1, k2, k3, k4, k5, k6, k7} : B.Key}
  Equal.trans(List<&2, W.U64>, SRC.outputs(~CR.Gen, ~CR.next, n, CR.G{C8.of_key(k), []}), SRC.outputs(~C8.ChaCha8, ~C8.next, n, C8.of_key(k)), SC.stream(n, SC.key_list(k)),
    gen_outputs(n, C8.of_key(k), []),
    MR.ChaCha8.stream(n, k))

def wrap_map(+n: Nat, m: Maybe<&2, C8.ChaCha8>) -> {SCR.map_outputs(n, CR.wrap(m)) == SRM.map_outputs(n, m) : Maybe<&2, List<&2, W.U64>>}:
  match m:
    case None{}:
      {==}
    case Some{+c}:
      Equal.cong(List<&2, W.U64>, Maybe<&2, List<&2, W.U64>>, l => Some{l}, SRC.outputs(~CR.Gen, ~CR.next, n, CR.G{c, []}), SRC.outputs(~C8.ChaCha8, ~C8.next, n, c), gen_outputs(n, c, []))

def Random.seeded(+n: Nat, +seed: List<&2, U32>) -> SCR.Random.seeded(n, seed):
  Equal.trans(Maybe<&2, List<&2, W.U64>>, SCR.map_outputs(n, CR.wrap(C8.new(seed))), SRM.map_outputs(n, C8.new(seed)), SRM.map_stream(n, SC.key_of_seed(seed)),
    wrap_map(n, C8.new(seed)),
    MR.ChaCha8.seeded(n, seed))

def Random.bytes(+n: Nat, +c: C8.ChaCha8, +p: List<&2, U32>) -> SCR.Random.bytes(n, c, p):
  BY.bytes(n, c, p)

def Random.bytes_lt(+n: Nat, +c: C8.ChaCha8, +p: List<&2, U32>, +hp: {SCR.below256(p) == True{} : Bool}) -> SCR.Random.bytes_lt(n, c, p, hp):
  BY.bytes_lt(n, c, p, hp)

def Random.uint_below(+g: CR.Gen, +n: W.U64, +hn: {X.is_zero(n) == False{} : Bool}) -> SCR.Random.uint_below(g, n, hn):
  MR.Uint64n.lt(~CR.Gen, ~CR.next, g, n, hn)

def Random.shuffle(~A: Data, ~V: Data, ~rel: A -> V -> Bool, +g: CR.Gen, +items: List<&2, A>, +v: V) -> SCR.Random.shuffle(~A, ~V, ~rel, g, items, v):
  MR.Shuffle.permutation(~A, ~V, ~rel, ~CR.Gen, ~CR.next, g, items, v)
