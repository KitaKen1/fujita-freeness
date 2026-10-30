# Comparator checks

`comparator.json` compares these two declarations in `Challenge` and `FCSolution`:

- `FujitaPublication.fujita`
- `FujitaPublication.variants.mixed`

The pinned Lean version provides `lake comparator`. It checks theorem types,
definition dependencies, permitted axioms and the exported solution's kernel proof.
The permitted axioms are `propext`, `Classical.choice` and `Quot.sound`.

The reference imports `FCTargetDefinitions`, whose local import closure excludes the
solution and mixed-freeness proof. `check-inputs.py` checks that separation, exact
reference/solution signatures, source hashes, identical ordinary-build sources,
pins and the absence of proof holes in the shared sources.

## Linux

With bubblewrap installed:

```sh
lake exe cache get
lake comparator
```

## Local macOS

Build the two modules and export each separately:

```sh
lake build Challenge FCSolution FCAudit
python3 comparator/export-local.py Challenge
python3 comparator/export-local.py FCSolution
lake comparator --inadvisably-no-sandbox \
  --challenge-from-export .lake/exports/challenge-comparator.ndjson \
  --solution-from-export .lake/exports/solution-comparator.ndjson
```

The macOS command explicitly disables the Linux-only sandbox. The local result is
not a Linux CI or sandbox result. Exports are generated from the built package,
and their hashes are recorded with the result.

`FCAudit.lean` prints the axioms of both solution targets. The shared source manifest
binds the proof sources to their hashes. No old F1/F2 Comparator receipt is reused as
a result for these newly named targets.

## Standalone FC file

`check-fclike.py` checks the separate one-file statement in a pinned FC checkout.
It records the canonical short-header build, an otherwise identical temporary
FC-header audit, and Mathlib-only elaboration. The short source is restored and no
official configuration or linter is changed.

This checks statement elaboration and style. It does not establish a Lean dictionary
between the FC file's local-equation definitions and the library's sheaf definitions.
