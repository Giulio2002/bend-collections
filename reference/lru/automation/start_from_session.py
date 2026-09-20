"""Start revised frozen authority while retaining the previous worker conversation.

Candidate preservation is a separate, scope-checked step recorded in provenance.
No previous completion/validation status is imported into the new run.
"""
import json
import os
from pathlib import Path
import sys
import uuid

from autoimplementer.engine import atomic_json, load_state, new_run
from autoimplementer.objective import Objective

ROOT = Path(__file__).resolve().parents[1]


def main():
    if len(sys.argv) != 2:
        raise SystemExit('usage: start_from_session.py PREVIOUS_RUN')
    previous = Path(sys.argv[1]).resolve()
    state = load_state(previous)
    if state['status'] not in ('interrupted', 'error'):
        raise SystemExit('Previous runner must be stopped before continuing its worker session')
    session = state.get('worker_session_id')
    uuid.UUID(session)  # Fail rather than silently start a different conversation.
    objective = Objective.load(ROOT / 'automation/OBJECTIVE.md')
    if Path(state['objective']['project']).resolve() != ROOT:
        raise SystemExit('Previous session belongs to a different source project')
    provenance = json.loads((ROOT / 'automation/restart-provenance.json').read_text())
    if provenance['prior_run'] != str(previous) or provenance['worker_session_id'] != session:
        raise SystemExit('Preserved candidate/session provenance mismatch')
    run = new_run(objective, ROOT / 'automation/ORCHESTRATOR.MD', previous.parent,
                  ROOT / 'automation/AUDITOR.md')
    fresh = load_state(run)
    fresh['worker_session_id'] = session
    fresh['continued_worker_from'] = str(previous)
    atomic_json(run / 'state.json', fresh)
    print(f'Run: {run}\nContinuing worker session: {session}', flush=True)
    executable = '/Users/monkeair/auto-implementer/.venv/bin/auto-implementer'
    os.execv(executable, [executable, 'resume', str(run), '--color', 'always'])


if __name__ == '__main__':
    main()
