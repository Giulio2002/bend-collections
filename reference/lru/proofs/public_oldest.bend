import Base
import ../types/model.bend as T
import ../spec/cache.bend as S
import ../spec/operations.bend as O
import ../spec/public_oldest.bend as P

# Specification properties, not yet implementation-refinement claims.
def same(a: String) -> String -> Bool:
  b => String.eq(a, b)

def observation(-K: Data, -V: Data, reply: P.Reply<K, V>) -> K & V & Bool & List<&2, T.Int64>:
  P.Returned{s, key, value, found, unused} = reply
  (key, value, found, unused)

law empty_no_clock:
  for -V: Data
  for cap: Nat
  for zero_key: String
  for zero_value: V
  for times: List<&2, T.Int64>
  {P.get_oldest(~String, ~same, V, S.initial(String, V, cap), zero_key, zero_value, times) == Done{P.Returned{S.initial(String, V, cap), zero_key, zero_value, False{}, times}} : Result<&2, &2, String, P.Reply<String, V>>}
def empty_no_clock(V, cap, zero_key, zero_value, times):
  {==}

law expired_retains_original_key:
  for -V: Data
  for s: S.Model<String, V>
  for key: String
  for value: V
  for zero_value: V
  for times: List<&2, T.Int64>
  {observation(String, V, P.decide(~String, ~same, V, s, key, value, zero_value, times, True{})) == (key, zero_value, False{}, times) : String & V & Bool & List<&2, T.Int64>}
def expired_retains_original_key(V, s, key, value, zero_value, times):
  {==}

law live_unchanged:
  for -V: Data
  for s: S.Model<String, V>
  for key: String
  for value: V
  for zero_value: V
  for times: List<&2, T.Int64>
  {P.decide(~String, ~same, V, s, key, value, zero_value, times, False{}) == P.Returned{s, key, value, True{}, times} : P.Reply<String, V>}
def live_unchanged(V, s, key, value, zero_value, times):
  {==}

law finite_missing_clock_fails:
  for -V: Data
  for s: S.Model<String, V>
  for key: String
  for value: V
  for deadline: T.Int64
  for zero_value: V
  {P.lifetime(~String, ~same, V, s, key, value, deadline, zero_value, Nil{}, False{}) == Fail{"clock sample required"} : Result<&2, &2, String, P.Reply<String, V>>}
def finite_missing_clock_fails(V, s, key, value, deadline, zero_value):
  {==}

law immortal_no_clock:
  for -V: Data
  for s: S.Model<String, V>
  for key: String
  for value: V
  for zero_value: V
  for times: List<&2, T.Int64>
  {P.binding(~String, ~same, V, s, "", zero_value, times, Some{T.Item{key, value, T.I64{Word.zero(64n)}}}) == Done{P.Returned{s, key, value, True{}, times}} : Result<&2, &2, String, P.Reply<String, V>>}
def immortal_no_clock(V, s, key, value, zero_value, times):
  {==}
