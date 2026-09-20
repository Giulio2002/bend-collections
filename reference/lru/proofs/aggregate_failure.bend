import Base
import ../types/model.bend as T
import ../spec/cache.bend as S
import ../spec/operations.bend as O

# Independent specification laws only; host composition remains an obligation.
def same(a: String) -> String -> Bool:
  b => String.eq(a, b)

law failed_prefix_keeps_completed_removal:
  for -K: Data
  for -V: Data
  for entry: T.Entry<K, V>
  for error: String
  for removed: List<&2, T.Entry<K, V>>
  for retained: List<&2, T.Entry<K, V>>
  for times: List<&2, T.Int64>
  {S.prefix_prepend(K, V, entry, Fail{S.PrefixFailed{error, removed, retained, times}}) == Fail{S.PrefixFailed{error, Con{entry, removed}, retained, times}} : Result<&2, &2, S.PrefixFailure<K, V>, S.ExpiredPrefix<K, V>>}
def failed_prefix_keeps_completed_removal(K, V, entry, error, removed, retained, times):
  {==}

law missing_sample_keeps_pending_entry:
  for -K: Data
  for -V: Data
  for entry: T.Entry<K, V>
  for tail: List<&2, T.Entry<K, V>>
  {S.prefix_missing(K, V, entry, tail, False{}) == Fail{S.PrefixFailed{"clock sample missing", Nil{}, Con{entry, tail}, Nil{}}} : Result<&2, &2, S.PrefixFailure<K, V>, S.ExpiredPrefix<K, V>>}
def missing_sample_keeps_pending_entry(K, V, entry, tail):
  {==}

law failed_aggregate_applies_completed_prefix:
  for -V: Data
  for s: S.Model<String, V>
  for enabled: Bool
  for error: String
  for removed: List<&2, T.Entry<String, V>>
  for retained: List<&2, T.Entry<String, V>>
  for times: List<&2, T.Int64>
  {O.prefix_result(~String, ~same, V, s, enabled, Fail{S.PrefixFailed{error, removed, retained, times}}) == Fail{O.AggregateFailed{error, O.remove_entries(~String, ~same, V, removed, s), times}} : Result<&2, &2, O.AggregateFailure<String, V>, O.AggregateResult<String, V>>}
def failed_aggregate_applies_completed_prefix(V, s, enabled, error, removed, retained, times):
  {==}
