#!/usr/bin/env python3
"""Check the two proof copies, reference signatures, pins and statement scope."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
LEAN = ROOT / 'lean'


def uncomment(source):
    out, i, depth = [], 0, 0
    while i < len(source):
        if source.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and source.startswith('-/', i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif source.startswith('--', i):
            end = source.find('\n', i)
            i = len(source) if end < 0 else end
        elif source[i] == '"':
            out.append('""')
            i += 1
            while i < len(source):
                if source[i] == '\\':
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        else:
            out.append(source[i])
            i += 1
    assert depth == 0
    return ''.join(out)


def statements(path):
    return {m[1]: ' '.join(m[2].split()) for m in re.finditer(
        r'\btheorem\s+(\w+)\s+(.+?)\s*:=\s*by\b', uncomment(path.read_text()), re.S)}


reference = statements(LEAN / 'Challenge.lean')
assert set(reference) == {'fujita', 'mixed'}
assert statements(LEAN / 'FCSolution.lean') == reference
assert statements(ROOT / 'leanWithoutComparator/FCSolution.lean') == reference
manifest = json.loads((LEAN / 'comparator/shared-proof-sources.json').read_text())
actual = {str(p.relative_to(LEAN)) for p in LEAN.rglob('*.lean')
          if '.lake' not in p.parts and p.name != 'Challenge.lean'}
assert actual == set(manifest)
for relative, expected in manifest.items():
    data = (LEAN / relative).read_bytes()
    assert hashlib.sha256(data).hexdigest() == expected, relative
    assert data == (ROOT / 'leanWithoutComparator' / relative).read_bytes(), relative
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by)\b|#eval|\brun_cmd\b',
                         uncomment(data.decode())), relative

fc = ROOT / 'FClikelean/Fujita.lean'
code = uncomment(fc.read_text())
assert set(statements(fc)) == {'fujita', 'mixed'}
assert re.findall(r'^public import (.+)$', code, re.M) == ['FormalConjecturesUtil']
assert not re.search(r'\b(?:TauCeti|FCTargetDefinitions|EffectiveKlt|mixedDifference|relativeJacobian)\b', code)
assert len(re.findall(r'\bsorry\b', code)) == 2
assert len(re.findall(r'\bsorry\b', uncomment((LEAN / 'Challenge.lean').read_text()))) == 2
assert not re.search(r'\b(?:axiom|opaque|admit|unsafe|sorryAx)\b', code)
assert set(re.findall(r'\bdef\s+(\w+)', code)) == {
    'CartierDivisor', 'sectionSpace', 'GloballyGenerated', 'Ample', 'Nef', 'IsCanonical'}
assert 'namespace variants' in code
for tree in ['lean', 'leanWithoutComparator']:
    root = ROOT / tree
    assert (root / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.35.0-rc3'
    lock = json.loads((root / 'lake-manifest.json').read_text())
    assert next(p['rev'] for p in lock['packages'] if p['name'] == 'mathlib') == \
        'f6090c7095e1e56b3464c1daba5f24631f1290d2'
assert (LEAN / 'lake-manifest.json').read_bytes() == \
    (ROOT / 'leanWithoutComparator/lake-manifest.json').read_bytes()

seen = set()


def visit(module):
    if module in seen:
        return
    path = LEAN / (module.replace('.', '/') + '.lean')
    if not path.exists():
        return
    seen.add(module)
    for line in re.findall(r'^\s*(?:public\s+)?import\s+([^\n]+)', uncomment(path.read_text()), re.M):
        for dependency in line.split():
            visit(dependency)


visit('Challenge')
assert not seen.intersection({'FCSolution', 'MixedFujita.ComplexFujitaFreeness',
                              'MixedFujita.KawamataViehwegCharZero'})
assert not (LEAN / 'MixedFujita/LinearEffectiveFreenessNumerical.lean').exists()
result = {'status': 'pass', 'shared_lean_sources': len(manifest),
          'targets': ['FujitaPublication.fujita', 'FujitaPublication.variants.mixed'],
          'reference_import_closure': len(seen), 'fclike_definition_count': 6,
          'fclike_statement_holes': 2, 'f2_target_included': False,
          'fclike_to_library_kernel_dictionary': 'not established'}
print(json.dumps(result, indent=2))
