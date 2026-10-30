#!/usr/bin/env python3
"""Record CI step outcomes without conflating them with the FC draft."""
import datetime
import json
import os
from pathlib import Path

out = Path('ci-results')
out.mkdir(exist_ok=True)
config = json.loads(Path('lean/comparator.json').read_text())
steps = {key.lower().removesuffix('_outcome'): os.environ.get(key, 'not_run')
         for key in ['SOURCE_OUTCOME','SETUP_OUTCOME','CACHE_OUTCOME','BUILD_OUTCOME','AXIOMS_OUTCOME','COMPARATOR_OUTCOME']}
record = {
    'recorded_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'repository':os.environ.get('GITHUB_REPOSITORY'),
    'commit':os.environ.get('GITHUB_SHA'),
    'run_id':os.environ.get('GITHUB_RUN_ID'),
    'run_attempt':os.environ.get('GITHUB_RUN_ATTEMPT'),
    'project':os.environ['PROJECT'],
    'targets':config['theorem_names'],
    'steps':steps,
    'comparator_sandbox_disabled':False,
    'fc_representation_to_library_dictionary':'not established',
    'fc_statement_proof_completed':False,
    'scope':'library-backed proof; separate standalone FC representation excluded',
}
(out / 'result.json').write_text(json.dumps(record,indent=2)+'\n')
summary = os.environ.get('GITHUB_STEP_SUMMARY')
if summary:
    with open(summary,'a') as stream:
        stream.write('## Library-backed proof verification\n\n')
        stream.write('Project: `' + record['project'] + '`; commit: `' + record['commit'] + '`.\n\n')
        stream.write('| Check | Outcome |\n|---|---|\n')
        for name, outcome in steps.items():
            stream.write('| ' + name + ' | ' + outcome + ' |\n')
        stream.write('\nThe standalone FC problem file is not a completed proof. Its dictionary to the proof-library definitions remains unimplemented.\n')
print(json.dumps(record,indent=2))
