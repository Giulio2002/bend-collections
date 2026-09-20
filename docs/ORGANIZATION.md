# Project organization

Use one small public entry module per structure, with matching specifications and proofs. Keep the frozen src/<id>.bend, spec/<id>.bend and proofs/<id>.bend paths as entry points; put larger internals in subdirectories. Do not rename protected acceptance paths or rewrite checked work just for appearance.

```text
src/<structure>.bend            public API and documented behavior
src/<structure>/               private implementation helpers, if needed
src/internal/                  genuinely shared runtime helpers
spec/<structure>.bend          independent mathematical model
spec/<structure>/              supporting independent definitions
proofs/<structure>.bend        complete public-operation and trace entry point
proofs/<structure>/            invariants, lemmas and composition
proofs/lib/                    reusable checked Base/word/array/map facts
types/                         neutral shared datatypes only
tests/<structure>/             public behavior, errors, differential histories
tests/support/                 independent oracles and transport helpers
tools/generators/              deterministic proof/code generators
build/                         ignored experiments, transient logs and binaries
docs/ARCHITECTURE.md            module/dependency map and design decisions
docs/API.md                    API index with examples and error semantics
docs/PROOF_MAP.md              public operation -> spec -> theorem -> tests
docs/VALIDATION.md             reproducible commands, tool pins and evidence
reference/lru/                 immutable completed LRU reference
inventory/                     protected scope/toolchain manifests
automation/                    protected objective, policies and acceptance
PROOF.bend                     one checked proof root
END_TO_END.bend                 public correctness and trace theorems
```

Use domain names, not milestone names such as final2/fixed/new. Do not make a framework or a deep folder tree for trivial modules. Shared helpers must have real multiple callers or a clear boundary. Runtime must not import proofs, tests or generators; specifications must remain independent of implementation. Keep proof templates and their concrete checked instances explicit.

Document a short usage example, empty/error behavior and actual cost for each public structure. Generated modules identify their generator and exact regeneration command. Put scratch experiments outside the proof root and source tree. Archive meaningful final validation evidence with source hashes; distinguish checked proofs from pending candidates in one current proof map. Preserve historical logs separately rather than letting old status paragraphs contradict current status.

Organize incrementally while implementing the complete objective. Existing sound proofs and pinned reference material must be preserved. Check imports, public API, all proof instances and tests after moves; a tidy tree does not replace verification. Final self-audit, orchestrator review and auditor review must assess this layout and documentation alongside the original correctness requirements.
