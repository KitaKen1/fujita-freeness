# Public CI

This is a tentative public version of the F1 proof package.

The [public Actions workflow](https://github.com/KitaKen1/fujita-freeness/actions)
builds the canonical and ordinary proof projects separately, verifies source
copies and target signatures, audits the target axioms, and runs the pinned
native Comparator with Linux bubblewrap and default kernel replay.

The initial public run is pending at packaging time. Its URL, tested commit,
job results, and downloaded verification evidence are recorded independently
after execution. Earlier local receipts are not presented as public CI results.

The standalone FC problem file retains two intentional `sorry` placeholders.
Its definitions are not yet connected by a Lean dictionary to the proof-library
definitions. Passing the proof CI does not complete that separate bridge or
resolve the retained short-header FC copyright-linter failure.

No upstream issue, comment, or PR is posted by this workflow.
