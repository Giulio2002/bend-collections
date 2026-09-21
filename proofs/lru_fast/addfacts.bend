import Base
import ../lib/logic.bend as L
import ../../spec/lru_fast.bend as S
import ../../spec/lru_numeric.bend as NS
import ../../src/lru/fast.bend as F
import ../../src/lru/time.bend as Time
import ../../types/lru_model.bend as T
import ./num/duration_refinement.bend as DR
import ./state.bend as ST
import ./readfacts.bend as RF

# The entry add stores: immortal (Live) for a zero lifetime, else Timed with the
# retained deadline; either way it is occupied and carries the spec's deadline.

def entry(~V: Data, +life: T.Int64, v: V, +now: T.Int64) -> F.Slot<V>:
  F.entry_of(~V, Bool.not(Time.is_zero(life)), F.int_stamp(life), v, F.int_stamp(now))

def occ_c(~V: Data, +life: T.Int64, v: V, +now: T.Int64, c: Bool) -> {ST.is_occ(V, F.entry_of(~V, Bool.not(c), F.int_stamp(life), v, F.int_stamp(now))) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def entry_occ(~V: Data, +life: T.Int64, v: V, +now: T.Int64) -> {ST.is_occ(V, entry(~V, life, v, now)) == True{} : Bool}:
  occ_c(~V, life, v, now, Time.is_zero(life))

def ent_c(~V: Data, +k: String, +v: V, +life: T.Int64, +now: T.Int64, c: Bool, +ec: {Time.is_zero(life) == c : Bool}) -> {ST.ent_at(V, k, F.entry_of(~V, Bool.not(c), F.int_stamp(life), v, F.int_stamp(now)), Nil{}) == Con{S.En{k, v, NS.deadline(now, life)}, Nil{}} : List<&2, S.Ent<V>>}:
  match c:
    case True{}:
      +ed = Equal.trans(T.Int64, NS.deadline(now, life), Time.deadline(now, life), Time.deadline_choose(now, life, True{}),
        Equal.sym(T.Int64, Time.deadline(now, life), NS.deadline(now, life), DR.deadline(now, life)),
        Equal.cong(Bool, T.Int64, z => Time.deadline_choose(now, life, z), Time.is_zero(life), True{}, ec))
      Equal.cong(T.Int64, List<&2, S.Ent<V>>, z => Con{S.En{k, v, z}, Nil{}}, S.zero_time(), NS.deadline(now, life), Equal.sym(T.Int64, NS.deadline(now, life), S.zero_time(), ed))
    case False{}:
      +d0 = Time.deadline(F.stamp_int(F.int_stamp(now)), F.stamp_int(F.int_stamp(life)))
      +e1 = Equal.trans(T.Int64, F.stamp_int(F.int_stamp(d0)), d0, NS.deadline(now, life),
        RF.stamp_iso(d0),
        Equal.trans(T.Int64, d0, Time.deadline(now, F.stamp_int(F.int_stamp(life))), NS.deadline(now, life),
          Equal.cong(T.Int64, T.Int64, z => Time.deadline(z, F.stamp_int(F.int_stamp(life))), F.stamp_int(F.int_stamp(now)), now, RF.stamp_iso(now)),
          Equal.trans(T.Int64, Time.deadline(now, F.stamp_int(F.int_stamp(life))), Time.deadline(now, life), NS.deadline(now, life),
            Equal.cong(T.Int64, T.Int64, z => Time.deadline(now, z), F.stamp_int(F.int_stamp(life)), life, RF.stamp_iso(life)),
            DR.deadline(now, life))))
      Equal.cong(T.Int64, List<&2, S.Ent<V>>, z => Con{S.En{k, v, z}, Nil{}}, F.stamp_int(F.int_stamp(d0)), NS.deadline(now, life), e1)

def entry_ent(~V: Data, +k: String, +v: V, +life: T.Int64, +now: T.Int64) -> {ST.ent_at(V, k, entry(~V, life, v, now), Nil{}) == Con{S.En{k, v, NS.deadline(now, life)}, Nil{}} : List<&2, S.Ent<V>>}:
  ent_c(~V, k, v, life, now, Time.is_zero(life), {==})
