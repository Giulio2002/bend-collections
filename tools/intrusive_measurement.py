"""Bracket the emitted churn loop; fail closed if lowering changes its shape.

Allocator calls mean Bend heap_alloc requests (including allocator reuse),
not OS malloc calls or peak bytes. Timing-only builds contain no counter.
"""
import re


def instrument(source, allocations=True, memory=False):
    markers = list(re.finditer(
        r'INLINE Term spin_\d+\([^\n]+\) \{\n(?:(?!\n\}).)*?Term _churn_iterations_0 = r0;',
        source, re.S))
    if len(markers) != 1:
        raise RuntimeError('expected exactly one compiled churn marker')
    start = source.index('{', markers[0].start()) + 1
    end = source.index('\n}', markers[0].end())
    body = source[start:end]
    if body.count('return 1;') != 1:
        raise RuntimeError('unexpected compiled churn exit')
    before = '\n  struct timespec il_start, il_end; clock_gettime(CLOCK_MONOTONIC, &il_start);\n'
    after = 'clock_gettime(CLOCK_MONOTONIC, &il_end);\n'
    if allocations:
        before += '  il_active = 1;\n'
        after = 'il_active = 0; ' + after
    if memory:
        before += '  long long il_entry_bytes = il_live_bytes; il_peak_bytes = il_live_bytes;\n'
        after += '  fprintf(stderr, "IL_BYTES %lld %lld %lld\\n", il_entry_bytes, il_live_bytes, il_peak_bytes);\n'
    after += '  unsigned long long il_ns = (il_end.tv_sec-il_start.tv_sec)*1000000000ull + il_end.tv_nsec-il_start.tv_nsec;\n'
    after += ('  fprintf(stderr, "IL_ALLOC %llu IL_NS %llu\\n", (unsigned long long)il_allocations, il_ns);\n'
              if allocations else '  fprintf(stderr, "IL_NS %llu\\n", il_ns);\n')
    source = source[:start] + before + body.replace('return 1;', after + '  return 1;') + source[end:]
    if allocations:
        marker = 'INLINE Loc heap_alloc(Env e, Cls cls) {'
        if source.count(marker) != 1:
            raise RuntimeError('allocator instrumentation point changed')
        source = source.replace(marker,
            'static unsigned long long il_allocations = 0;\nstatic int il_active = 0;\n' +
            marker + '\n  il_allocations += il_active;')
    if memory:
        # The runtime size class is a power of two in 64-bit corpus words.
        # Account from process start so prewarmed arenas remain in the total;
        # reset only the high-water mark at the hot-loop boundary. Single CPU
        # worker only. This excludes stacks, allocator free lists and RSS.
        alloc = 'INLINE Loc heap_alloc(Env e, Cls cls) {'
        free = 'INLINE void heap_free(Env e, Cls cls, Loc loc) {'
        for marker in (alloc, free):
            if source.count(marker) != 1:
                raise RuntimeError('live-block instrumentation point changed')
        if 'ALC_LEN(e, cls) += 1ull << cls;' not in source:
            raise RuntimeError('allocator size-class representation changed')
        source = source.replace(alloc,
            'static long long il_live_bytes = 0, il_peak_bytes = 0;\n' + alloc +
            '\n  il_live_bytes += (1ull << cls) * sizeof(u64);' +
            '\n  if (il_live_bytes > il_peak_bytes) il_peak_bytes = il_live_bytes;')
        source = source.replace(free, free +
            '\n  il_live_bytes -= (1ull << cls) * sizeof(u64);' +
            '\n  if (il_live_bytes < 0) { fprintf(stderr, "invalid live-block accounting\\n"); abort(); }')
    return source
