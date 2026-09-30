import Base
import ../../../../src/math/u64.bend as W
import ../../../../src/math/random/chacha8/block.bend as B
import ../../../../src/math/random/chacha8.bend as C8
import ../../../../spec/math/random/chacha8rand.bend as S
import ../../../../spec/math/random/source.bend as SRC
import ./block.bend as PB

# The ChaCha8 generator of src/math/random/chacha8.bend produces C2SP's
# stream (spec/math/random/chacha8rand.bend) for every key: its state (key,
# next group, unread words of the current group) stands for the words left
# of the current iteration and the key of the next one.

def app(xs: List<&2, W.U64>, ys: List<&2, W.U64>) -> List<&2, W.U64>:
  match xs:
    case Nil{}:
      ys
    case Con{x, rest}:
      Con{x, app(rest, ys)}

def drop64(n: Nat, xs: List<&2, W.U64>) -> List<&2, W.U64>:
  match n xs:
    case 0n _:
      xs
    case 1n+p Nil{}:
      []
    case 1n+p Con{x, rest}:
      drop64(p, rest)

# the outputs of the current iteration after the groups already produced
def rest(+kl: List<&2, U32>, p: C8.Phase) -> List<&2, W.U64>:
  match p:
    case C8.G0{}:
      []
    case C8.G1{}:
      drop64(32n, S.words64(S.output(kl)))
    case C8.G2{}:
      drop64(64n, S.words64(S.output(kl)))
    case C8.G3{}:
      drop64(96n, S.words64(S.output(kl)))

# the key of the iteration after them
def nk(+kl: List<&2, U32>, p: C8.Phase) -> List<&2, U32>:
  match p:
    case C8.G0{}:
      kl
    case C8.G1{}:
      S.next_key(kl)
    case C8.G2{}:
      S.next_key(kl)
    case C8.G3{}:
      S.next_key(kl)

def gw(+k: B.Key, +c: U32) -> List<&2, W.U64>:
  S.words64(S.group(S.key_list(k), c))

# the invariant: from state C{k, p, buf} the generator outputs buf, the rest
# of the iteration keyed by k, then C2SP's stream from the next key
def inv(+n: Nat, +k: B.Key, +buf: List<&2, W.U64>, +p: C8.Phase) -> {SRC.outputs(~C8.ChaCha8, ~C8.next, n, C8.C{k, p, buf}) == S.stream_go(n, app(buf, rest(S.key_list(k), p)), nk(S.key_list(k), p)) : List<&2, W.U64>}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      match buf:
        case Con{x, t}:
          Equal.cong(List<&2, W.U64>, List<&2, W.U64>, l => Con{x, l}, SRC.outputs(~C8.ChaCha8, ~C8.next, m, C8.C{k, p, t}), S.stream_go(m, app(t, rest(S.key_list(k), p)), nk(S.key_list(k), p)), inv(m, k, t, p))
        case Nil{}:
          match p:
            case C8.G0{}:
              %Equal.sym(List<&2, W.U64>, B.group(k, 0), gw(k, 0), PB.group_correct(k, 0)) : {Con{SRC.fst64(C8.ChaCha8, C8.pop(C8.C{k, C8.G1{}, _})), SRC.outputs(~C8.ChaCha8, ~C8.next, m, SRC.snd64(C8.ChaCha8, C8.pop(C8.C{k, C8.G1{}, _})))} == S.stream_go(1n+m, [], S.key_list(k)) : List<&2, W.U64>}
              Equal.cong(List<&2, W.U64>, List<&2, W.U64>, l => Con{S.head(gw(k, 0)), l}, SRC.outputs(~C8.ChaCha8, ~C8.next, m, C8.C{k, C8.G1{}, S.tail(gw(k, 0))}), S.stream_go(m, app(S.tail(gw(k, 0)), rest(S.key_list(k), C8.G1{})), S.next_key(S.key_list(k))), inv(m, k, S.tail(gw(k, 0)), C8.G1{}))
            case C8.G1{}:
              %Equal.sym(List<&2, W.U64>, B.group(k, 4), gw(k, 4), PB.group_correct(k, 4)) : {Con{SRC.fst64(C8.ChaCha8, C8.pop(C8.C{k, C8.G2{}, _})), SRC.outputs(~C8.ChaCha8, ~C8.next, m, SRC.snd64(C8.ChaCha8, C8.pop(C8.C{k, C8.G2{}, _})))} == S.stream_go(1n+m, rest(S.key_list(k), C8.G1{}), S.next_key(S.key_list(k))) : List<&2, W.U64>}
              Equal.cong(List<&2, W.U64>, List<&2, W.U64>, l => Con{S.head(gw(k, 4)), l}, SRC.outputs(~C8.ChaCha8, ~C8.next, m, C8.C{k, C8.G2{}, S.tail(gw(k, 4))}), S.stream_go(m, app(S.tail(gw(k, 4)), rest(S.key_list(k), C8.G2{})), S.next_key(S.key_list(k))), inv(m, k, S.tail(gw(k, 4)), C8.G2{}))
            case C8.G2{}:
              %Equal.sym(List<&2, W.U64>, B.group(k, 8), gw(k, 8), PB.group_correct(k, 8)) : {Con{SRC.fst64(C8.ChaCha8, C8.pop(C8.C{k, C8.G3{}, _})), SRC.outputs(~C8.ChaCha8, ~C8.next, m, SRC.snd64(C8.ChaCha8, C8.pop(C8.C{k, C8.G3{}, _})))} == S.stream_go(1n+m, rest(S.key_list(k), C8.G2{}), S.next_key(S.key_list(k))) : List<&2, W.U64>}
              Equal.cong(List<&2, W.U64>, List<&2, W.U64>, l => Con{S.head(gw(k, 8)), l}, SRC.outputs(~C8.ChaCha8, ~C8.next, m, C8.C{k, C8.G3{}, S.tail(gw(k, 8))}), S.stream_go(m, app(S.tail(gw(k, 8)), rest(S.key_list(k), C8.G3{})), S.next_key(S.key_list(k))), inv(m, k, S.tail(gw(k, 8)), C8.G3{}))
            case C8.G3{}:
              %Equal.sym(List<&2, W.U64>, B.group(k, 12), gw(k, 12), PB.group_correct(k, 12)) : {Con{SRC.fst64(C8.ChaCha8, C8.pop(C8.last(_))), SRC.outputs(~C8.ChaCha8, ~C8.next, m, SRC.snd64(C8.ChaCha8, C8.pop(C8.last(_))))} == S.stream_go(1n+m, rest(S.key_list(k), C8.G3{}), S.next_key(S.key_list(k))) : List<&2, W.U64>}
              Equal.cong(List<&2, W.U64>, List<&2, W.U64>, l => Con{S.head(gw(k, 12)), l}, SRC.outputs(~C8.ChaCha8, ~C8.next, m, C8.C{C8.rekey(List.drop(&2, W.U64, gw(k, 12), 28n)), C8.G0{}, S.tail(List.take(&2, W.U64, gw(k, 12), 28n))}), S.stream_go(m, app(S.tail(List.take(&2, W.U64, gw(k, 12), 28n)), []), S.key_list(C8.rekey(List.drop(&2, W.U64, gw(k, 12), 28n)))), inv(m, C8.rekey(List.drop(&2, W.U64, gw(k, 12), 28n)), S.tail(List.take(&2, W.U64, gw(k, 12), 28n)), C8.G0{}))

# THEOREM: the generator keyed by k outputs C2SP's ChaCha8Rand stream keyed
# by k's eight words, for every key and every number of outputs
def stream(+n: Nat, +k: B.Key) -> {SRC.outputs(~C8.ChaCha8, ~C8.next, n, C8.of_key(k)) == S.stream(n, S.key_list(k)) : List<&2, W.U64>}:
  inv(n, k, [], C8.G0{})
