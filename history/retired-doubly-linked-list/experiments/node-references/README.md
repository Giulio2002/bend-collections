# Stock Bend shared-node capability probe

Tested on installed stock Bend 2.0.16, native C backend:

```
bend experiments/node-references/chan_sentinel.bend -o build/chan-sentinel
build/chan-sentinel
```

Passes a finite example covering circular sentinel, stored length, insertion at both ends, forward/backward traversal, removal, empty-list reuse. No custom effects, FFI files, unsafe declarations or compiler changes were added. Operations use the existing Base Chan effects and IO.

This disproves the blanket assertion that shared mutable node identity necessarily requires a compiler extension. It does NOT demonstrate ordinary C-pointer representation, performance acceptance or formal correctness. The inspected Bend runtime implements channels using an indexed generation-tagged table and per-channel message buffers; using them would hide that machinery in the runtime, not eliminate it. It is not a recommended production replacement under the user's simple-storage and performance requirements. Nodes must be drained before closing, since channel close retains queued messages until read.

The production list, deque and queue have not been replaced by this experiment. Existing incomplete proof status remains unchanged.
