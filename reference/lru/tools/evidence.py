#!/usr/bin/env python3
"""Snapshot existing validation evidence; this does not run or certify proofs."""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE = Path('/Users/monkeair/.bend/current/bend2/base.bend')

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--acceptance-exit', type=int, required=True)
    args = parser.parse_args()
    report = json.loads((ROOT / 'build/validation.json').read_text())
    lock = json.loads((ROOT / 'upstream.lock.json').read_text())
    for name, expected in lock['files'].items():
        if digest(ROOT / 'vendor/go_freelru' / name) != expected:
            raise RuntimeError('upstream mismatch: ' + name)
    paths = [p for folder in ['src', 'types', 'spec', 'proofs', 'tools', 'tests/new']
             for p in (ROOT / folder).glob('*') if p.is_file() and p.suffix != '.pyc']
    paths += [ROOT / name for name in ['PROOF.bend', 'END_TO_END.bend', 'README.md',
                                     'WORK_LOG.md', 'PROOF_STATUS.md']]
    report.update({
        'status': 'done' if report['complete'] and args.acceptance_exit == 0 else 'needs_work',
        'run': ROOT.parents[2].name, 'iteration': int(ROOT.parent.name),
        'scope': 'callback-free public API; user callback assertions individually excluded',
        'frozen_acceptance': {
            'command': '/Users/monkeair/auto-implementer/.venv/bin/python automation/acceptance.py',
            'exit_code': args.acceptance_exit,
            'log': 'build/acceptance.log',
            'upstream_integrity': f"all {len(lock['files'])} pinned hashes verified",
        },
        'source_sha256': {str(p.relative_to(ROOT)): digest(p) for p in sorted(paths)},
        'installed_base_sha256': digest(BASE),
        'evidence_sha256': {name: digest(ROOT / name) for name in
                            ['build/validation.json', 'build/acceptance.log']},
        'proved_scope': [
            'END_TO_END.bend (imported by PROOF.bend), universally quantified over the actual src/public.bend machine and D.drive/D.run with the actual Base Map',
            'construction: public_initialization, constructor errors and the rejection branch of every public_*_trace',
            'every public request from every represented callback-disabled String state and every provider-event list refines PublicSpec.execute (public_string_request and per-operation instances): exact reply/error, unused events, request count, canonically equal abstract state with exact recency, lifetime and metrics',
            'reachability: every outcome state (returned or retained on failure) keeps the full representation invariant and disabled callback metadata (public_string_request_safe)',
            'arbitrary finite traces from construction for String, T.Integer and Word(64) keys refine Traces.run (public_string_trace, public_integer_trace, public_word64_trace); K-typed replies compared exactly',
            'generic keys: machine and specification key-renaming commutation (rename_map, rename_machine, rename_spec) and PublicKeys.from_construction under stated inj/agree contracts, discharged for all built-in codecs',
            'independent spec key equalities for Integer/Word64 are sound and reflexive and agree with code equality',
            'host boundary (src/host.bend, the only Bend code the adapter calls besides codecs): uint64/int64/uint32 text readers exact with rejection, decimal rendering read-back and key round trips, time/sample/construction/string-key functions, against independent spec/host.bend',
            'host step functions: HostLoop.loop over H.begin/H.answer equals D.drive and D.execute (host_loop_drive/string/word64); drive_finished/drive_advance are driver unfolding lemmas',
            'Base Map get/set/del/size/keys/to_list laws against the installed definitions; codec round-trip/injectivity; modular arithmetic, signed duration division, deadline and limb packing/decoding',
        ],
        'trusted_boundary': [
            'unmodified Bend 2.0.5 checker and primitive Base semantics',
            'Bun/JS runtime, compiler and hardware, including String(bigint)/BigInt(text) decimal conversion at the adapter boundary (compiled Bend Nat holds at most 2^48-1)',
            'src/adapter.ts residue: clock provider call and exception capture, the loop passing values between H.begin/H.answer unchanged, constructor-tag checks (loop modelled by HostLoop.loop = D.drive)',
        ],
        'self_audit': 'tests/new/self_audit.md; not independent auditor approval',
    })
    (ROOT / 'VALIDATION.json').write_text(json.dumps(report, indent=2) + '\n')

if __name__ == '__main__':
    main()
