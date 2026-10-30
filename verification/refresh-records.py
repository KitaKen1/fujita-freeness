#!/usr/bin/env python3
"""Bind the local build records and Comparator run to the packaged source files."""
import argparse
import datetime
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
HERE = ROOT / 'verification'
TARGETS = ['FujitaPublication.fujita', 'FujitaPublication.variants.mixed']


def digest(path):
    result = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(8 * 1024 * 1024), b''):
            result.update(block)
    return result.hexdigest()


def write(path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--comparator-exit-code', type=int)
args = parser.parse_args()
now = datetime.datetime.now(datetime.timezone.utc).isoformat()
inputs = json.loads((HERE / 'input-check.json').read_text())
fc = json.loads((HERE / 'fc-local-result.json').read_text())
assert inputs['status'] == 'pass'
assert fc['source_sha256'] == digest(ROOT / 'FClikelean/Fujita.lean')

files = {}
for path in sorted(ROOT.rglob('*')):
    if not path.is_file() or any(part in {'.lake', '.git', '__pycache__'} for part in path.parts):
        continue
    relative = path.relative_to(ROOT)
    if relative.as_posix() == 'PUBLICATION-MANIFEST.json' or path.name == '.DS_Store':
        continue
    if relative.parts[0] == 'verification' and path.suffix not in {'.py', '.md'}:
        continue
    files[relative.as_posix()] = {'sha256': digest(path), 'bytes': path.stat().st_size}

manifest_path = ROOT / 'PUBLICATION-MANIFEST.json'
write(manifest_path, {
    'schema_version': 1,
    'recorded_at': now,
    'scope': 'Classical Fujita freeness and the mixed F1 variant',
    'targets': TARGETS,
    'f2_publication_target_included': False,
    'proof_toolchain': (ROOT / 'lean/lean-toolchain').read_text().strip(),
    'proof_mathlib_commit': 'f6090c7095e1e56b3464c1daba5f24631f1290d2',
    'shared_lean_sources': inputs['shared_lean_sources'],
    'fclike_to_library_kernel_dictionary': 'not established',
    'ci_run': False, 'published': False,
    'excluded': ['.lake caches', '.git', '__pycache__', '.DS_Store',
                 'verification logs and result JSON files', 'this manifest itself'],
    'files': files,
})

builds = []
for directory, command, log in [
    ('lean', ['lake', 'build', 'FCSolution', 'FCAudit', 'Challenge'], 'library-build.log'),
    ('leanWithoutComparator', ['lake', 'build', 'FCSolution', 'FCAudit'], 'ordinary-build.log'),
]:
    text = (HERE / log).read_text()
    assert 'Build completed successfully' in text
    for target in TARGETS:
        assert f"'{target}' depends on axioms: [propext, Classical.choice, Quot.sound]" in text
    builds.append({'directory': directory, 'command': command, 'exit_code': 0,
                   'log': log, 'log_sha256': digest(HERE / log),
                   'dependency_warnings_present': 'warning:' in text})

comparator_path = HERE / 'local-comparator-result.json'
previous = json.loads(comparator_path.read_text()) if comparator_path.exists() else {}
exit_code = args.comparator_exit_code
if exit_code is None:
    exit_code = previous.get('exit_code')
log_path = HERE / 'comparator.log'
if exit_code == 0:
    assert 'Your solution is okay!' in log_path.read_text()
exports = {}
for name in ['challenge', 'solution']:
    path = ROOT / 'lean/.lake/exports' / f'{name}-comparator.ndjson'
    exports[name] = {'file': str(path.relative_to(ROOT)), 'sha256': digest(path),
                     'bytes': path.stat().st_size, 'ignored_cache_file': True}
comparator = {
    'status': 'running' if exit_code is None else ('pass' if exit_code == 0 else 'fail'),
    'exit_code': exit_code,
    'recorded_at': now,
    'started_at': datetime.datetime.fromtimestamp(log_path.stat().st_birthtime,
                  datetime.timezone.utc).isoformat(),
    'start_time_source': 'log file creation time',
    'command': ['lake', 'comparator', '--inadvisably-no-sandbox',
                '--challenge-from-export', '.lake/exports/challenge-comparator.ndjson',
                '--solution-from-export', '.lake/exports/solution-comparator.ndjson'],
    'directory': 'lean', 'targets': TARGETS,
    'sandbox_enabled': False, 'external_kernel_run': False,
    'log': 'comparator.log', 'log_sha256': digest(log_path), 'exports': exports,
    'publication_manifest_sha256': digest(manifest_path),
    'config_sha256': digest(ROOT / 'lean/comparator.json'),
    'old_combined_f1_f2_receipt_reused': False,
    'ci_run': False, 'published': False,
}
if exit_code is not None:
    comparator['finished_at'] = previous.get('finished_at', now)
write(comparator_path, comparator)
write(HERE / 'local-result.json', {
    'recorded_at': now, 'scope': 'F1github local package', 'targets': TARGETS,
    'publication_manifest_sha256': digest(manifest_path),
    'builds': builds,
    'permitted_target_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
    'source_audit': inputs,
    'fclike': fc,
    'comparator': {'status': comparator['status'], 'receipt': comparator_path.name},
    'ci_run': False, 'published': False,
})
print(json.dumps({'source_files': len(files), 'builds': 'pass',
                  'comparator': comparator['status'],
                  'canonical_fc_linter': fc['canonical_status']}))
