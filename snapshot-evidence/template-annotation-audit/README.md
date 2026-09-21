# Classification of the pinned checker's annotation count

Inspected upstream tag v2.0.16 (981899d6b2fb2c109ed83545cffed9d20910a025), specifically bend2/main.ts
cli_report. It counts a Def when `t.u === true || k.includes("~")`.
The parser creates names containing `~` for template instantiations.
The tag's Base SHA256 matches installed Base exactly:
e149828ca05581f61d1b06cf2a7d1a744e394d29a4c8e1942e5062ecbf30f5b8.

Using that tag's unmodified parser to list the loaded definitions:

* proofs/graph.bend:94template instances,0explicitly unsafe definitions.
* proofs/lib/array.bend:2template instances,0explicitly unsafe definitions.
  Both flags are imported LRU invariant template instances.

JSON lists every flagged name. The inspection script parses declarations; it
does not replace the independent stock CLI proof checks recorded elsewhere.
These counts are therefore not evidence of94explicit unsafe declarations.
Equally, this classification is NOT a proof of template soundness, a removal
of a trust boundary, or permission to suppress the CLI warning. Full semantic
review remains required; SSZ's zero-warning acceptance remains unchanged.
