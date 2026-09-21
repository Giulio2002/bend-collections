# Operator: capacity-premise audit

The independently checked native-LRU add wrappers carry an explicit q<=31 and
cap<=2^q premise. That is legitimate partial proof evidence, not yet proof of
all states accepted by the public API. During final integration, connect these
premises to actual constructor/resize behavior or explicit public preconditions
that match the agreed API. Do not silently drop supported capacities/traces,
weaken the retained specification, or call unconstrained APIs fully proven just
because bounded helper theorems check. If an actual runtime representability
limit is needed, expose/check it in the API and record compatibility implications
for review. Preserve existing valid proof components.

Likewise, U32 template instantiation verifies that instance; generic value-type
coverage and all operation/trace compositions need their explicit final review.
