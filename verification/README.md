# Local verification

This directory records checks of this F1-only package. It does not reuse the older
combined F1/F2 package's Comparator result.

| Check | Result | Record |
|---|---|---|
| Classical and mixed proof entries | Pass | `library-build.log` |
| Ordinary build without Comparator | Pass | `ordinary-build.log` |
| Target axioms | Only `propext`, `Classical.choice`, `Quot.sound` | Both build logs |
| Reference signatures and 2,310 identical shared sources | Pass | `input-check.json` |
| Native Comparator replay | Pass (macOS, sandbox disabled) | `comparator.log` |
| FC mathematical body with Mathlib only | Pass | `fc-mathlib-only.log` |
| Simplified definitions agree with their preceding version | Pass by `rfl` / `Iff.rfl` | `fc-simplification.log` |
| Official FC build/linter with its required header | Pass | `fc-header-audit.log` |
| Canonical FC file with the retained short header | Fails copyright linter | `fc-short-header.log` |
| FC representation to proof-library representation | Not implemented | `../lean/comparator/TARGET-CORRESPONDENCE.md` |

The proof projects use Lean `v4.35.0-rc3` and Mathlib
`f6090c7095e1e56b3464c1daba5f24631f1290d2`. The standalone FC audit uses official
commit `c83a94d785d0fb3b9b9a2a94e8ffff8cce76a346`, Lean `v4.33.1` and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`.

The macOS Comparator run disables its Linux-only sandbox. A local pass is not a
sandboxed Linux CI pass. Dependency style/deprecation warnings remain in the proof
build logs; a warning-free build of the entire proof library is not claimed.

The FC checker returns a nonzero exit code when the canonical short-header file
fails, even if the temporary standard-header audit passes. The temporary audit
changes only the copyright header and restores the canonical source. The FC file
contains two intentional statement holes; the library-backed solution has none.
The current statement has six definitions, no `variable` declarations and one
instance for relative differentials over the complex numbers.

These are historical local receipts. Public CI is recorded separately in
[CI.md](CI.md), with the tested commit and workflow run. No upstream issue,
comment or PR has been posted as part of this publication.

The two-page PDF is a statement and verification guide, not a full proof paper.
Its source is `make-guide.py` (ReportLab, using the named macOS system fonts).
