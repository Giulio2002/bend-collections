"""Workload table for benchmarks/run.py.

One row per (operation, workload). `op` is the numeric selector that both
benchmarks/bend/<id>.bend and benchmarks/native/<id>.c understand, `size` is the
number of elements the structure is built with before the measured operations
run, `count` is the number of measured operations per round and `reps` the
number of rounds. benchmarks/run.py raises `reps` until the measured region is
long enough to time reliably, so the `count`/`reps` here are starting points
chosen so that a round is neither trivial nor minutes long.

Every scalable operation gets a small, a medium and a large nonempty workload;
`edge-*` rows are the empty, out-of-range and limit cases (an empty structure
still has to reject the operation, and that rejection is what is measured).
"""

TABLE = []

# How benchmarks/run.py is allowed to lengthen the measured region.
#
#   'count' - the operation leaves the structure the same size, so running it
#             more times inside one round measures exactly the same thing.
#             The build is then paid once per round instead of once per
#             operation batch, which is what makes build-dominated rows
#             (large structures, cheap operations) measurable at all.
#   'reps'  - the operation changes the size of the structure (it pushes,
#             pops, inserts, removes, clears or reserves), so a longer batch
#             would no longer be "this operation at this size". Only whole
#             rounds may be repeated, and each round rebuilds.
#
# Classified by full operation name where the same verb means different
# things in different structures (`bitset.clear` clears one bit and preserves
# the size; `dynamic_array.clear` empties the array).
SIZE_CHANGING = {
    'push', 'push_front', 'push_back', 'pop', 'pop_front', 'pop_back',
    'enqueue', 'dequeue', 'insert', 'insert_after', 'insert_before',
    'remove', 'remove_edge', 'remove_vertex', 'add_vertex', 'add_edge',
}
SIZE_CHANGING_FULL = {
    'dynamic_array.clear',      # empties the array
    'union_find.union',         # merges classes: the partition collapses
    'prefix_trie.remove',
    'balanced_search_tree.remove',
    'doubly_linked_list.remove',
}
SIZE_PRESERVING_FULL = {
    'bitset.clear',             # clears one bit
    'dynamic_array.reserve',    # the driver reserves a capacity the array
                                # already has (the argument is drawn from
                                # 0 .. size and the round built `size`
                                # elements), so the measured call is the
                                # "already large enough" path and leaves the
                                # array untouched: repeating it inside one
                                # round measures exactly the same thing. The
                                # growing path of reserve is what the push
                                # rows pay for and what `reserve edge-empty`
                                # exercises from a fresh array.
}


# Operations that REMOVE elements. A round can only remove what it built, so
# a sweep of removals is bounded by `size` while the round also pays for
# building those `size` elements: the measured difference stays a small
# fraction of the round and drowns in its noise (benchmarks/run.py documents
# the rule and the earlier reports show exactly this failure). Every removal
# below is therefore measured as a RESTORING PAIR -- the operation together
# with the insertion that puts the element back -- so the structure keeps its
# size, the batch can be lengthened freely, and both sides run the identical
# pair. The nanoseconds of the pair are charged to the removal, which
# over-charges the Bend side by one insertion and never flatters it.
REMOVING = {
    'pop', 'pop_front', 'pop_back', 'dequeue', 'remove', 'remove_edge',
    'remove_vertex',
}


def removing(operation):
    return operation.split('.', 1)[1] in REMOVING


def growth(operation):
    if operation in SIZE_PRESERVING_FULL:
        return 'count'
    if operation in SIZE_CHANGING_FULL:
        return 'reps'
    if operation.split('.', 1)[1] in SIZE_CHANGING:
        return 'reps'
    return 'count'


def add(structure, op, selector, workload, size, count, reps=1, method='batch'):
    operation = '%s.%s' % (structure, op)
    grow = 'count' if method == 'pair' else growth(operation)
    # How far benchmarks/run.py may lengthen the batch inside one round of a
    # size-changing row: a removal may not run out of elements (size / 2, so
    # that the doubled region A is exactly the full sweep), an insertion may
    # at most treble the structure (region A adds 2 x size), which keeps the
    # row "this operation at this size" within a factor of three.
    cap = max(1, size // 2 if removing(operation) else size)
    TABLE.append({
        'structure': structure,
        'operation': operation,
        'workload': workload,
        'op': selector,
        'size': size,
        'count': count,
        'reps': reps,
        'grow': grow,
        'cap': cap,
        'method': method,
    })


def three(structure, op, selector, sizes, counts, method='batch'):
    for label, size, count in zip(('small', 'medium', 'large'), sizes, counts):
        add(structure, op, selector, label, size, count, method=method)


def pair(structure, op, selector, sizes, counts):
    """a removal measured inside the restoring pair `selector` runs.

    The structure keeps its size, so the batch grows by `count` like any
    size-preserving row and the build is paid once per round.
    """
    three(structure, op, selector, sizes, counts, method='pair')


def sized(structure, op, selector, sizes):
    """a destructive sweep.

    `count` is half the size, because benchmarks/run.py's region A runs the
    loop `2 x count` times and region B `count` times: region A is then
    exactly the full sweep of the structure and region B its first half, so
    the `count` operations the difference isolates are the second half of the
    sweep and neither region ever runs the operation on an exhausted
    structure (which would make the difference negative -- it measures no-ops
    against real work).
    """
    for label, size in zip(('small', 'medium', 'large'), sizes):
        add(structure, op, selector, label, size, max(1, size // 2))


def empties(structure, ops, count=200000):
    for op, selector in ops:
        add(structure, op, selector, 'edge-empty', 0, count)


# ------------------------------------------------------------ dynamic_array
DA = (64, 4096, 262144)
FAST = (200000, 100000, 50000)
SCAN = (20000, 1000, 50)
three('dynamic_array', 'push', 0, DA, FAST)
three('dynamic_array', 'get', 2, DA, FAST)
three('dynamic_array', 'set', 3, DA, FAST)
three('dynamic_array', 'length', 4, DA, FAST)
three('dynamic_array', 'capacity', 5, DA, FAST)
three('dynamic_array', 'reserve', 8, DA, FAST)
three('dynamic_array', 'to_list', 6, DA, SCAN)
three('dynamic_array', 'clear', 7, DA, (50000, 20000, 500))
pair('dynamic_array', 'pop', 9, DA, FAST)
add('dynamic_array', 'new', 10, 'small', 64, 200000)
add('dynamic_array', 'new', 10, 'medium', 4096, 200000)
add('dynamic_array', 'new', 10, 'large', 262144, 50000)
empties('dynamic_array', [('new', 10), ('length', 4), ('capacity', 5), ('get', 2),
                          ('set', 3), ('push', 0), ('pop', 1), ('reserve', 8),
                          ('clear', 7), ('to_list', 6)])

# -------------------------------------------------------------------- deque
DQ = (64, 4096, 262144)
three('deque', 'push_front', 0, DQ, FAST)
three('deque', 'push_back', 1, DQ, FAST)
three('deque', 'peek_front', 4, DQ, FAST)
three('deque', 'peek_back', 5, DQ, FAST)
three('deque', 'length', 6, DQ, FAST)
three('deque', 'to_list', 7, DQ, SCAN)
pair('deque', 'pop_front', 9, DQ, FAST)
pair('deque', 'pop_back', 10, DQ, FAST)
add('deque', 'new', 8, 'small', 64, 200000)
add('deque', 'new', 8, 'medium', 4096, 200000)
add('deque', 'new', 8, 'large', 262144, 50000)
empties('deque', [('new', 8), ('length', 6), ('push_front', 0), ('push_back', 1),
                  ('pop_front', 2), ('pop_back', 3), ('peek_front', 4),
                  ('peek_back', 5), ('to_list', 7)])

# -------------------------------------------------------------------- queue
three('queue', 'enqueue', 0, DQ, FAST)
three('queue', 'peek', 2, DQ, FAST)
three('queue', 'length', 3, DQ, FAST)
three('queue', 'to_list', 5, DQ, SCAN)
pair('queue', 'dequeue', 6, DQ, FAST)
add('queue', 'new', 4, 'small', 64, 200000)
add('queue', 'new', 4, 'medium', 4096, 200000)
add('queue', 'new', 4, 'large', 262144, 50000)
empties('queue', [('new', 4), ('length', 3), ('enqueue', 0), ('dequeue', 1),
                  ('peek', 2), ('to_list', 5)])

# ------------------------------------------------------- doubly_linked_list
DL = (64, 2048, 32768)
DLF = (100000, 50000, 20000)
three('doubly_linked_list', 'push_front', 0, DL, DLF)
three('doubly_linked_list', 'push_back', 1, DL, DLF)
three('doubly_linked_list', 'insert_before', 2, DL, DLF)
three('doubly_linked_list', 'insert_after', 3, DL, DLF)
three('doubly_linked_list', 'get', 5, DL, DLF)
three('doubly_linked_list', 'set', 6, DL, DLF)
three('doubly_linked_list', 'next', 7, DL, DLF)
three('doubly_linked_list', 'prev', 8, DL, DLF)
three('doubly_linked_list', 'length', 9, DL, DLF)
three('doubly_linked_list', 'to_list', 10, DL, (5000, 300, 20))
sized('doubly_linked_list', 'remove', 4, DL)
add('doubly_linked_list', 'new', 11, 'small', 64, 100000)
add('doubly_linked_list', 'new', 11, 'medium', 2048, 100000)
add('doubly_linked_list', 'new', 11, 'large', 32768, 50000)
empties('doubly_linked_list',
        [('new', 11), ('length', 9), ('push_front', 0), ('push_back', 1),
         ('insert_before', 2), ('insert_after', 3), ('remove', 4), ('get', 5),
         ('set', 6), ('next', 7), ('prev', 8), ('to_list', 10)], 100000)

# -------------------------------------------------------------- binary_heap
BH = (64, 4096, 131072)
BHF = (100000, 50000, 20000)
three('binary_heap', 'push', 0, BH, BHF)
three('binary_heap', 'peek', 2, BH, FAST)
three('binary_heap', 'length', 3, BH, FAST)
three('binary_heap', 'from_list', 4, BH, (50000, 50000, 20000))
three('binary_heap', 'to_sorted_list', 5, BH, (2000, 100, 5))
pair('binary_heap', 'pop', 7, BH, BHF)
add('binary_heap', 'new', 6, 'small', 64, 200000)
add('binary_heap', 'new', 6, 'medium', 4096, 200000)
add('binary_heap', 'new', 6, 'large', 131072, 50000)
empties('binary_heap', [('new', 6), ('length', 3), ('push', 0), ('peek', 2),
                        ('pop', 1), ('from_list', 4), ('to_sorted_list', 5)],
        100000)

# ----------------------------------------------------- balanced_search_tree
BT = (64, 4096, 131072)
BTF = (100000, 50000, 20000)
three('balanced_search_tree', 'insert', 0, BT, BTF)
pair('balanced_search_tree', 'remove', 11, BT, BTF)
three('balanced_search_tree', 'lookup', 2, BT, BTF)
three('balanced_search_tree', 'contains', 3, BT, BTF)
three('balanced_search_tree', 'min', 4, BT, FAST)
three('balanced_search_tree', 'max', 5, BT, FAST)
three('balanced_search_tree', 'lower_bound', 6, BT, BTF)
three('balanced_search_tree', 'range', 7, BT, (2000, 300, 20))
three('balanced_search_tree', 'to_list', 8, BT, (2000, 100, 5))
three('balanced_search_tree', 'length', 9, BT, FAST)
add('balanced_search_tree', 'new', 10, 'small', 64, 200000)
add('balanced_search_tree', 'new', 10, 'medium', 4096, 200000)
add('balanced_search_tree', 'new', 10, 'large', 131072, 50000)
empties('balanced_search_tree',
        [('new', 10), ('length', 9), ('insert', 0), ('remove', 1), ('lookup', 2),
         ('contains', 3), ('min', 4), ('max', 5), ('lower_bound', 6),
         ('range', 7), ('to_list', 8)], 100000)

# ------------------------------------------------------------------- bitset
BI = (64, 4096, 262144)
BIW = (50000, 20000, 500)
three('bitset', 'set', 0, BI, FAST)
three('bitset', 'clear', 1, BI, FAST)
three('bitset', 'get', 2, BI, FAST)
three('bitset', 'count', 3, BI, BIW)
three('bitset', 'length', 4, BI, FAST)
three('bitset', 'to_list', 5, BI, (20000, 2000, 50))
three('bitset', 'union', 6, BI, BIW)
three('bitset', 'intersection', 7, BI, BIW)
three('bitset', 'difference', 8, BI, BIW)
three('bitset', 'xor', 9, BI, BIW)
add('bitset', 'new', 10, 'small', 64, 200000)
add('bitset', 'new', 10, 'medium', 4096, 200000)
add('bitset', 'new', 10, 'large', 262144, 50000)
empties('bitset', [('new', 10), ('length', 4), ('get', 2), ('set', 0),
                   ('clear', 1), ('count', 3), ('union', 6), ('intersection', 7),
                   ('difference', 8), ('xor', 9), ('to_list', 5)])

# --------------------------------------------------------------- union_find
UF = (64, 4096, 65536)
UFF = (100000, 50000, 20000)
three('union_find', 'find', 0, UF, UFF)
three('union_find', 'union', 1, UF, UFF)
three('union_find', 'connected', 2, UF, UFF)
three('union_find', 'component_size', 3, UF, UFF)
three('union_find', 'component_count', 4, UF, FAST)
add('union_find', 'new', 5, 'small', 64, 200000)
add('union_find', 'new', 5, 'medium', 4096, 200000)
add('union_find', 'new', 5, 'large', 65536, 50000)
empties('union_find', [('new', 5), ('find', 0), ('union', 1), ('connected', 2),
                       ('component_size', 3), ('component_count', 4)], 100000)

# -------------------------------------------------------------- fenwick_tree
FW = (64, 4096, 262144)
FWF = (100000, 50000, 20000)
three('fenwick_tree', 'add', 0, FW, FWF)
three('fenwick_tree', 'prefix_sum', 1, FW, FWF)
three('fenwick_tree', 'range_sum', 2, FW, FWF)
three('fenwick_tree', 'length', 3, FW, FAST)
three('fenwick_tree', 'from_list', 5, FW, (50000, 50000, 20000))
add('fenwick_tree', 'new', 4, 'small', 64, 200000)
add('fenwick_tree', 'new', 4, 'medium', 4096, 200000)
add('fenwick_tree', 'new', 4, 'large', 262144, 50000)
empties('fenwick_tree', [('new', 4), ('from_list', 5), ('length', 3), ('add', 0),
                         ('prefix_sum', 1), ('range_sum', 2)], 100000)

# -------------------------------------------------------------- segment_tree
SG = (64, 4096, 262144)
SGF = (50000, 20000, 10000)
three('segment_tree', 'range_add', 0, SG, SGF)
three('segment_tree', 'get', 1, SG, SGF)
three('segment_tree', 'range_query', 2, SG, SGF)
three('segment_tree', 'length', 3, SG, FAST)
three('segment_tree', 'set', 6, SG, SGF)
three('segment_tree', 'from_list', 5, SG, (50000, 50000, 20000))
add('segment_tree', 'new', 4, 'small', 64, 200000)
add('segment_tree', 'new', 4, 'medium', 4096, 200000)
add('segment_tree', 'new', 4, 'large', 262144, 50000)
empties('segment_tree', [('new', 4), ('from_list', 5), ('length', 3), ('get', 1),
                         ('set', 6), ('range_query', 2), ('range_add', 0)], 100000)

# --------------------------------------------------------------- prefix_trie
PT = (64, 2048, 32768)
PTF = (50000, 20000, 10000)
three('prefix_trie', 'insert', 0, PT, PTF)
three('prefix_trie', 'lookup', 1, PT, PTF)
pair('prefix_trie', 'remove', 7, PT, PTF)
three('prefix_trie', 'contains', 3, PT, PTF)
three('prefix_trie', 'prefix_entries', 4, PT, (5000, 500, 40))
three('prefix_trie', 'longest_prefix', 5, PT, PTF)
add('prefix_trie', 'new', 6, 'small', 64, 100000)
add('prefix_trie', 'new', 6, 'medium', 2048, 100000)
add('prefix_trie', 'new', 6, 'large', 32768, 50000)
empties('prefix_trie', [('new', 6), ('insert', 0), ('lookup', 1), ('remove', 2),
                        ('contains', 3), ('prefix_entries', 4),
                        ('longest_prefix', 5)], 100000)

# --------------------------------------------------------------------- graph
GR = (32, 512, 4096)
GRF = (50000, 20000, 10000)
three('graph', 'add_vertex', 0, GR, GRF)
three('graph', 'remove_vertex', 1, GR, (2000, 500, 200))
three('graph', 'add_edge', 2, GR, GRF)
three('graph', 'remove_edge', 3, GR, GRF)
three('graph', 'has_vertex', 4, GR, GRF)
three('graph', 'has_edge', 5, GR, GRF)
three('graph', 'neighbors', 6, GR, GRF)
three('graph', 'vertices', 7, GR, (5000, 500, 50))
three('graph', 'edges', 8, GR, (5000, 500, 50))
add('graph', 'new', 9, 'small', 32, 100000)
add('graph', 'new', 9, 'medium', 512, 100000)
add('graph', 'new', 9, 'large', 4096, 50000)
empties('graph', [('new', 9), ('add_vertex', 0), ('remove_vertex', 1),
                  ('add_edge', 2), ('remove_edge', 3), ('has_vertex', 4),
                  ('has_edge', 5), ('neighbors', 6), ('vertices', 7),
                  ('edges', 8)], 100000)
