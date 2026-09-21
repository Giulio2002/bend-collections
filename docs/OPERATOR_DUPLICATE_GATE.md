# Duplicate gate resolved

The background subshell DID NOT die. Orphan zsh79764 (parent1) and newer sequence79872 both ran acceptance against the same build/bin paths and /tmp/acceptance8b.log, then the orphan began benchmarks while the newer validator was still running. This is the supported explanation for the missing test binary; unrelated SSZ load does not delete DSA files.

Operator preserved mixed/partial logs at control/duplicate-gate-20260921-1154 and killed ONLY orphan79764 and its descendants (benchmark81594 and descendants), leaving newer sequence79872 and the worker intact. Do not treat old mixed logs or interrupted benchmark as acceptance. Ensure the surviving validation/benchmark sequence completes and rerun any contaminated validation stage against stable sources. Use a per-workspace lock or actual tracked PIDs to prevent duplicate writers; absence of a shell job from one session does not establish process death.
