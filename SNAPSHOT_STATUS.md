# Work in progress

WIP: one-descent red-black tree updates, proven equivalent to prior implementation. Complete tree proof module and 11,109 differential/structural observations pass; mutation controls reject incorrect old-binding results. Insertion 2.07–2.33x faster; remove/reinsert 2.00–2.10x faster; still 4.91–6.54x C. C unchanged. DLL iterator prior calibrated gate passes 33/33. Quick screen: 84 within target, 28 slow, 7 unresolved out of 119; 39.931 seconds. Full library proof and cursor invariant/trace proof remain incomplete. DSA worker stopped.

See BENCHMARKS.md and docs/TREE_OPTIMIZATION.md for measurements, proof scope, and reproducible commands.
