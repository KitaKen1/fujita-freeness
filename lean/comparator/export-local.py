#!/usr/bin/env python3
"""Export the roots required by the pinned Lake Comparator (Check.lean)."""
import json
import os
from pathlib import Path
import subprocess
import sys

module = sys.argv[1]
assert module in ['Challenge', 'FCSolution']
root = Path(__file__).resolve().parents[1]
config = json.loads((root / 'comparator.json').read_text())
primitives = ['Nat.add', 'Nat.sub', 'Nat.mul', 'Nat.pow', 'Nat.gcd', 'Nat.div', 'Nat.mod',
              'Nat.beq', 'Nat.ble', 'Nat.land', 'Nat.lor', 'Nat.xor', 'Nat.shiftLeft',
              'Nat.shiftRight', 'String.ofList', 'Char.ofNat', 'List', 'eagerReduce',
              'Nat', 'String', 'String.mk', 'Char', 'optParam', 'autoParam', 'semiOutParam', 'outParam']
roots = ['Quot', 'Quot.mk', 'Quot.lift', 'Quot.ind'] + config['theorem_names'] + config['permitted_axioms'] + primitives
out = root / '.lake/exports' / ('challenge-comparator.ndjson' if module == 'Challenge' else 'solution-comparator.ndjson')
out.parent.mkdir(parents=True, exist_ok=True)
part = out.with_suffix('.partial')
with part.open('wb') as f:
    subprocess.run(['lake', 'env', 'leanexport', module, '--', *roots], cwd=root, stdout=f, check=True)
os.replace(part, out)
print(json.dumps({'module': module, 'export': out.name, 'roots': roots, 'bytes': out.stat().st_size}))
