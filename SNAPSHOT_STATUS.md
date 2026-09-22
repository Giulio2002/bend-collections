# Work in progress

WIP: dynamic-array representation now supports owning Type elements through _owned APIs. 26,795 nested-array observations, closure storage/replacement, 107 Data histories, affine rejection and proof mutation checks pass. Existing Data trace proofs preserved. Owning fixed-size swap traversal roundtrip proved for arbitrary Type; component templates checked at three owning types. Full owning public-operation/trace proofs and owning performance acceptance remain open. Owning empty-buffer initialization currently O(capacity log capacity). Existing Data push/get/set unchanged within about 1%. Indexed red-black tree migration pending; prior proven tree retained. Latest quick screen: 80 within target, 32 slow, 7 unresolved out of 119. DSA worker remains stopped.

See docs/DYNAMIC_ARRAY_OWNERSHIP.md for the public API, source compatibility change, validation and exact proof/performance limits.
