#!/usr/bin/env python3
"""Reject proof holes and axioms outside the Comparator whitelist."""
import json
from pathlib import Path
import re
import sys

root = Path(__file__).resolve().parents[1]
config = json.loads((root / 'lean/comparator.json').read_text())
text = Path(sys.argv[1]).read_text()
found = {name: set(filter(None, (x.strip() for x in axioms.split(','))))
         for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text)}
allowed = set(config['permitted_axioms'])
result = {}
for target in config['theorem_names']:
    if target not in found:
        raise SystemExit('Missing axiom report: ' + target)
    if not found[target] <= allowed:
        raise SystemExit('Forbidden axioms for ' + target + ': ' + ', '.join(sorted(found[target] - allowed)))
    result[target] = sorted(found[target])
Path(sys.argv[2]).write_text(json.dumps({'status':'pass','targets':result},indent=2)+'\n')
print(json.dumps({'status':'pass','targets':result},indent=2))
