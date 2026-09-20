# Published snapshot

This repository preserves the completed LRU auto-implementer iteration 24, including the independent audit and orchestrator completion review in `evidence/`. `VALIDATION.json` is the original source-fingerprinted completion record. The source and proof files are unchanged from that accepted workspace.

The pinned go-freelru reference is included under `vendor/go_freelru`, with its license and notice. Every included upstream file must match `upstream.lock.json`. Callbacks, concurrency variants, AESENC and custom hashing are excluded as documented in README.

A fresh publication acceptance run is retained in `evidence/publication/`. This runs the actual proof checker, upstream groups, differential checks, boundary checks and mutation gates.

## Reproduction

The preserved runner uses the original local tool paths: Bend 2.0.5 at `/Users/monkeair/.bend/bin/bend`, Bend preload at `/Users/monkeair/.bend/current/bend2/main.ts`, Bun at `/Users/monkeair/.bun/bin/bun`, and Go at `/opt/homebrew/bin/go`. In that environment run `python3 automation/acceptance.py`. On a different installation, adapt these tool paths in the acceptance/validation scripts before running; do not alter their acceptance conditions. `VALIDATION.json` includes the Base hash used for the recorded proofs.

## Formal-verification boundary

The universal Bend theorems cover the cache, supported key types, arbitrary finite request traces and Bend host-boundary functions. The compiler/runtime/hardware and the small TypeScript adapter residue remain trusted, as detailed in README and PROOF_STATUS. Completion under this boundary does not mean the TypeScript program or compiler has been formally verified.
