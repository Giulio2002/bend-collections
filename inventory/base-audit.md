# Installed Base audit

Inspected installed Bend 2.0.16 via `bend --help`, `bend base --types`, and `/Users/monkeair/.bend/bend2/base.bend`. The exact binary/Base hashes are in toolchain.json.

- Base.List: lines 756 onward; Nil/Con and structural matching already implement stack operations. Excluded.
- Base.Array: lines 2142–2272; fixed full binary tree, new(depth, default), get/set/swap; size is a U32 and indexing is masked modulo size. No logical-length, checked bounds or grow/push/pop/reserve API. Reuse this backing array; implement missing dynamic behavior. Do not claim contiguous memory or O(1) indexing: this representation follows a tree. Guard representable capacity/depth and reject overflow before Base indexing.
- Base.Map: lines 2274–2712; crit-bit keyed map with lookup, insertion, deletion, enumeration and size. Exclude a new hash map; reuse native Map.
- Base.Set: lines 2714–2746; native string set over Map. Exclude a new hash set.
- No public queue/deque, doubly linked list, heap, ordered balanced tree, packed bitset, prefix-search trie, DSU, graph, Fenwick or segment-tree family found in the installed Base type/function inventory.
- Native Map is a trie internally but does not supply the requested prefix-search/longest-prefix API. Prefix trie functionality remains in scope; reuse native storage if appropriate.
- An LRU already exists in this workspace: reuse the immutable reference snapshot. Its original evidence was for Bend 2.0.5, not automatically valid for 2.0.16.

This is an audit of the installed distribution, not a claim about every third-party Bend package.
