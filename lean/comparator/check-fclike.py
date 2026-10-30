#!/usr/bin/env python3
"""Check the standalone statement in pinned FC, including the short-header limitation."""
import argparse
import datetime
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
FC_COMMIT = 'c83a94d785d0fb3b9b9a2a94e8ffff8cce76a346'
MATHLIB_COMMIT = '0df444a360eaa60ab8c11dca51a86af692955474'
MODULE = 'FormalConjectures.Paper.Fujita'
MATHLIB_IMPORTS = [
    'Mathlib.AlgebraicGeometry.OrderOfVanishing',
    'Mathlib.AlgebraicGeometry.Morphisms.Smooth',
    'Mathlib.AlgebraicGeometry.Morphisms.Proper',
    'Mathlib.RingTheory.Kaehler.Basic',
    'Mathlib.LinearAlgebra.FreeModule.Determinant',
    'Mathlib.Analysis.Complex.Basic',
    'Mathlib.Algebra.Order.Ring.Cast',
]
FC_HEADER = '''/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
'''


def git_output(args, cwd):
    return subprocess.check_output(['git', *args], cwd=cwd, text=True).strip()


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(command, cwd, log):
    with log.open('w') as stream:
        return subprocess.run(command, cwd=cwd, stdout=stream,
                              stderr=subprocess.STDOUT).returncode


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--fc-root', type=Path, default=ROOT.parent / 'fc-local-check')
args = parser.parse_args()
fc = args.fc_root.resolve()
assert git_output(['rev-parse', 'HEAD'], fc) == FC_COMMIT
subprocess.run(['git', 'diff', '--exit-code', 'HEAD', '--'], cwd=fc, check=True)
for name in ['lakefile.toml', 'lake-manifest.json', 'lean-toolchain']:
    assert (fc / name).read_bytes() == subprocess.check_output(
        ['git', 'show', f'{FC_COMMIT}:{name}'], cwd=fc), name
lock = json.loads((fc / 'lake-manifest.json').read_text())
assert next(p['rev'] for p in lock['packages'] if p['name'] == 'mathlib') == MATHLIB_COMMIT
for package in lock['packages']:
    assert git_output(['rev-parse', 'HEAD'], fc / '.lake/packages' / package['name']) == package['rev']

source_path = ROOT / 'FClikelean/Fujita.lean'
source = source_path.read_text()
assert re.findall(r'^public import (.+)$', source, re.M) == ['FormalConjecturesUtil']
assert not re.search(r'set_option\s+(?:linter\.|warn\.sorry)', source)
destination = fc / 'FormalConjectures/Paper/Fujita.lean'
if destination.exists():
    assert destination.read_text() == source, 'Refusing to overwrite an unrelated FC file'
verification = ROOT / 'verification'
verification.mkdir(exist_ok=True)
destination.write_text(source)
short_exit = run(['lake', '--wfail', 'build', MODULE], fc, verification / 'fc-short-header.log')
long_source = FC_HEADER + source[source.index('module\n'):]
try:
    destination.write_text(long_source)
    header_audit_exit = run(['lake', '--wfail', 'build', MODULE], fc,
                            verification / 'fc-header-audit.log')
finally:
    destination.write_text(source)

mathlib_source = source.replace('public import FormalConjecturesUtil',
    '\n'.join('public import ' + module for module in MATHLIB_IMPORTS))
mathlib_source = mathlib_source.replace('@[category research open, AMS 14]\n', '')
with tempfile.TemporaryDirectory(prefix='fujita-mathlib-') as directory:
    path = Path(directory) / 'Fujita.lean'
    path.write_text(mathlib_source)
    mathlib_exit = run(['lake', 'env', 'lean', '-Dwarn.sorry=false', str(path)], fc,
                       verification / 'fc-mathlib-only.log')
result = {
    'checked_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'source': 'FClikelean/Fujita.lean', 'source_sha256': sha(source_path),
    'line_count': len(source.splitlines()),
    'definition_count': len(re.findall(r'\bdef\s+\w+', source)),
    'instance_count': len(re.findall(r'\binstance\s+\w+', source)),
    'variable_declarations': len(re.findall(r'^variable\b', source, re.M)),
    'intentional_statement_holes': 2, 'custom_library_imports': [],
    'fc_commit': FC_COMMIT, 'mathlib_commit': MATHLIB_COMMIT,
    'fc_toolchain': (fc / 'lean-toolchain').read_text().strip(),
    'canonical_status': 'pass' if short_exit == 0 else 'fail',
    'canonical_short_header_build_exit_code': short_exit,
    'temporary_fc_header_audit_exit_code': header_audit_exit,
    'mathlib_only_exit_code': mathlib_exit,
    'canonical_header_preserved': source_path.read_text() == source == destination.read_text(),
    'temporary_header_only_change': True,
    'temporary_header_source_sha256': hashlib.sha256(long_source.encode()).hexdigest(),
    'official_configuration_unmodified': True,
    'fclike_to_library_kernel_dictionary': 'not established',
    'ci_run': False, 'published': False,
}
(verification / 'fc-local-result.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
raise SystemExit(0 if short_exit == 0 and header_audit_exit == 0 and mathlib_exit == 0 else 1)
