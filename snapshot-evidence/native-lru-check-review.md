# Native LRU proof components, independent check

The operator froze the candidate before checking. After restoring the exact
pinned compiler (see local-toolchain-recovery.json), stock Bend2.0.16 checked
native-lru-all-inst.bend, importing inst,inst_rs,inst_add,inst_addop:
exit0,6s,0.86GB sampled peak physical footprint under a6.9GB watchdog cap.
The source and full checker output are preserved alongside this note.

These concrete U32 wrappers exercise constructor and native removal/read/add
proof components, including replacement, eviction and allocation paths.
Explicit invariant/capacity premises remain in the statements (including a
capacity bound via q<=31). This is not arbitrary unbounded machine capacity,
not a universal claim for every type, and not complete LRU trace acceptance.
The independent specification and parity with the retained LRU need final
semantic audit. Other operations and performance acceptance remain unfinished.

The checker reports390unsafe annotations. The pinned parser classifies all390
as template instances and none as explicit @unsafe declarations; this refines
the count's meaning but does not establish template soundness. See
template-annotation-audit/lru-inst.json. No warnings were suppressed.

The initial operator wrapper invocation used the executable as a log path and
truncated the installed compiler. It was restored from the official2.0.16
release with the exact original SHA256. The worker noticed the empty binary
and deferred checks. No result from that interval is used here: these checks
ran after restoration and hash verification. The remote BLS toolchain was
unaffected. The retained SSZ spectests used Bun during this interval.
