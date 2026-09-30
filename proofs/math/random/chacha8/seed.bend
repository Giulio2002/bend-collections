import Base
import ../../../../src/math/u64.bend as W
import ../../../../src/math/random/chacha8.bend as C8
import ../../../../src/math/random/chacha8/block.bend as B
import ../../../../spec/math/random/chacha8rand.bend as S
import ../../../../spec/math/random.bend as SRM
import ./stream.bend as CS
import ../../../../spec/math/random/source.bend as SRC

# A seed is 32 bytes below 256, read as eight little-endian words; any other
# list is rejected.

def bytes_eq(+bs: List<&2, U32>) -> {C8.all_bytes(bs) == S.bytes_ok(bs) : Bool}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +rest}:
      Equal.cong(Bool, Bool, z => Bool.and(U32.is_lt(b, 256), z), C8.all_bytes(rest), S.bytes_ok(rest), bytes_eq(rest))

def seeded_ok(+n: Nat, +seed: List<&2, U32>) -> {SRM.map_outputs(n, C8.lift(C8.key_of(seed))) == SRM.map_stream(n, S.key_if(seed, Nat.is_eq(S.length(seed), 32n))) : Maybe<&2, List<&2, W.U64>>}:
  match seed:
    case Nil{}:
      {==}
    case Con{+a0, +r0}:
      match r0:
        case Nil{}:
          {==}
        case Con{+a1, +r1}:
          match r1:
            case Nil{}:
              {==}
            case Con{+a2, +r2}:
              match r2:
                case Nil{}:
                  {==}
                case Con{+a3, +r3}:
                  match r3:
                    case Nil{}:
                      {==}
                    case Con{+b0, +r4}:
                      match r4:
                        case Nil{}:
                          {==}
                        case Con{+b1, +r5}:
                          match r5:
                            case Nil{}:
                              {==}
                            case Con{+b2, +r6}:
                              match r6:
                                case Nil{}:
                                  {==}
                                case Con{+b3, +r7}:
                                  match r7:
                                    case Nil{}:
                                      {==}
                                    case Con{+c0, +r8}:
                                      match r8:
                                        case Nil{}:
                                          {==}
                                        case Con{+c1, +r9}:
                                          match r9:
                                            case Nil{}:
                                              {==}
                                            case Con{+c2, +r10}:
                                              match r10:
                                                case Nil{}:
                                                  {==}
                                                case Con{+c3, +r11}:
                                                  match r11:
                                                    case Nil{}:
                                                      {==}
                                                    case Con{+d0, +r12}:
                                                      match r12:
                                                        case Nil{}:
                                                          {==}
                                                        case Con{+d1, +r13}:
                                                          match r13:
                                                            case Nil{}:
                                                              {==}
                                                            case Con{+d2, +r14}:
                                                              match r14:
                                                                case Nil{}:
                                                                  {==}
                                                                case Con{+d3, +r15}:
                                                                  match r15:
                                                                    case Nil{}:
                                                                      {==}
                                                                    case Con{+e0, +r16}:
                                                                      match r16:
                                                                        case Nil{}:
                                                                          {==}
                                                                        case Con{+e1, +r17}:
                                                                          match r17:
                                                                            case Nil{}:
                                                                              {==}
                                                                            case Con{+e2, +r18}:
                                                                              match r18:
                                                                                case Nil{}:
                                                                                  {==}
                                                                                case Con{+e3, +r19}:
                                                                                  match r19:
                                                                                    case Nil{}:
                                                                                      {==}
                                                                                    case Con{+f0, +r20}:
                                                                                      match r20:
                                                                                        case Nil{}:
                                                                                          {==}
                                                                                        case Con{+f1, +r21}:
                                                                                          match r21:
                                                                                            case Nil{}:
                                                                                              {==}
                                                                                            case Con{+f2, +r22}:
                                                                                              match r22:
                                                                                                case Nil{}:
                                                                                                  {==}
                                                                                                case Con{+f3, +r23}:
                                                                                                  match r23:
                                                                                                    case Nil{}:
                                                                                                      {==}
                                                                                                    case Con{+g0, +r24}:
                                                                                                      match r24:
                                                                                                        case Nil{}:
                                                                                                          {==}
                                                                                                        case Con{+g1, +r25}:
                                                                                                          match r25:
                                                                                                            case Nil{}:
                                                                                                              {==}
                                                                                                            case Con{+g2, +r26}:
                                                                                                              match r26:
                                                                                                                case Nil{}:
                                                                                                                  {==}
                                                                                                                case Con{+g3, +r27}:
                                                                                                                  match r27:
                                                                                                                    case Nil{}:
                                                                                                                      {==}
                                                                                                                    case Con{+h0, +r28}:
                                                                                                                      match r28:
                                                                                                                        case Nil{}:
                                                                                                                          {==}
                                                                                                                        case Con{+h1, +r29}:
                                                                                                                          match r29:
                                                                                                                            case Nil{}:
                                                                                                                              {==}
                                                                                                                            case Con{+h2, +r30}:
                                                                                                                              match r30:
                                                                                                                                case Nil{}:
                                                                                                                                  {==}
                                                                                                                                case Con{+h3, +r31}:
                                                                                                                                  match r31:
                                                                                                                                    case Nil{}:
                                                                                                                                      +k = {B.K{C8.le32(a0, a1, a2, a3), C8.le32(b0, b1, b2, b3), C8.le32(c0, c1, c2, c3), C8.le32(d0, d1, d2, d3), C8.le32(e0, e1, e2, e3), C8.le32(f0, f1, f2, f3), C8.le32(g0, g1, g2, g3), C8.le32(h0, h1, h2, h3)} : B.Key}
                                                                                                                                      Equal.cong(List<&2, W.U64>, Maybe<&2, List<&2, W.U64>>, l => Some{l}, SRC.outputs(~C8.ChaCha8, ~C8.next, n, C8.of_key(k)), S.stream(n, S.key_list(k)), CS.stream(n, k))
                                                                                                                                    case Con{x, rr}:
                                                                                                                                      {==}

def seeded_c(+n: Nat, +seed: List<&2, U32>, +b: Bool) -> {SRM.map_outputs(n, C8.seed_ok(seed, b)) == SRM.map_stream(n, S.key_if(seed, Bool.and(b, Nat.is_eq(S.length(seed), 32n)))) : Maybe<&2, List<&2, W.U64>>}:
  match b:
    case False{}:
      {==}
    case True{}:
      seeded_ok(n, seed)

# THEOREM (ChaCha8.seeded)
def seeded(+n: Nat, +seed: List<&2, U32>) -> SRM.ChaCha8.seeded(n, seed):
  %Equal.sym(Bool, C8.all_bytes(seed), S.bytes_ok(seed), bytes_eq(seed)) : {SRM.map_outputs(n, C8.seed_ok(seed, _)) == SRM.map_stream(n, S.key_if(seed, Bool.and(S.bytes_ok(seed), Nat.is_eq(S.length(seed), 32n)))) : Maybe<&2, List<&2, W.U64>>}
  seeded_c(n, seed, S.bytes_ok(seed))
