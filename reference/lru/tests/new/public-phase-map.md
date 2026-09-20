# Public assignment map (partial proof linkage)

> Historical (superseded in iteration 0022): the adapter now steps only via
> `D.advance`, and the composed public/trace/host laws are in END_TO_END.bend.
> See README.md and PROOF_STATUS.md for the current claims.

This table records the actual assignments in `src/adapter.ts` and the checked
Bend phase laws. It is an audit map, not a formal proof of TypeScript execution,
validation, allocation failure, or output conversion. All laws named below are
in `proofs/public_phase_safety.bend` unless qualified otherwise.

| Actual assignment or branch | Checked state obligation | Remaining connection |
| --- | --- | --- |
| Constructor adopts `C.new_with_size` result | `constructor_safety.new_with_size` derives joint safety of every native successful constructor result from the actual U32 zero test | Host BigInt validation, conversion and result dispatch remain unproved |
| `commit(step)` adopts `step.cache` after checking callback/events | `safe_step` contains representation, disabled cache flag and exact empty event list; `committed` projects cache safety | Actual tag checks, list conversion, rejection and assignment semantics |
| Add commits `P.prepare_add` | `prepare_add` | Actual encoded-key conversion and commit bridge |
| Add conditionally assigns `P.finish_removal(..., true)` | `finish_detached`, `counted_preparation`, and separate `finish_removal` law | Relate the TypeScript conditional to the existing Bend conditional; retain each intermediate assignment on execution failure |
| Add commits `C.add_with_lifetime` after the sample | `insertion`, `add_after_preparation` | Clock classification, exact sample consumption, observable return and host continuation |
| Get/Peek commits `P.read(...).step` | `read` and `read_pack` | Host clock/lookup dispatch and public value/boolean conversion |
| Expired read assigns removal count then miss count | `finish_removal`, `finish_miss`, `expired_read_counters` | Actual `pending.removed` branch and both assignment boundaries |
| Refresh commits `P.refresh_prepare` | `prepare_refresh` | Host miss return and clock-failure propagation |
| Successful refresh assigns `P.refresh_at` | `refresh_after_preparation` derives the lookup premise from the actual prepared item | Derive item presence from actual host flag/tag access; prove return and clock behavior |
| Remove/RemoveOldest commits detach, then counts successful removal | `detach`, `detach_oldest`, and `finish_detached` combine the actual removal phases | Actual public dispatch, branch and return conversion |
| Aggregate adopts `Complete.cache` or `NeedClock.cache` | `safe_aggregate` certifies the projected cache in both constructors | Actual host loop, completed return and failed clock preservation |
| Aggregate commits `RemovalReady.step` | `safe_aggregate` includes exact empty events for this constructor | Actual commit and continuation bridge |
| Aggregate produces next signal after sample/removal | `aggregate_next`, `after_clock`, `after_removal` | Exact signal/control-flow, request counts, returned lists and arbitrary host loop refinement |
| SetLifetime assigns `C.set_lifetime` | `set_lifetime` | Validated nanosecond conversion |
| ResetMetrics assigns `C.clear_metrics` | `clear_metrics` | `configuration_observations.reset` proves exact native old metrics and abstract reset state; BigInt conversion and host control flow remain open |

Every generic phase above is instantiated for String, mathematical Integer and
Word64. These proofs establish structural safety, not operation observations or
whole public reachability. The separate `full_scope` gate remains failed.
