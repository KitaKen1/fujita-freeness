# Public CI

**Pass.** [Public workflow run 41022967640](https://github.com/KitaKen1/fujita-freeness/actions/runs/41022967640)
checked proof/source commit `f56699dc58a29c4bc19bef2f7a5db48800f6e7bf`.

| Check | Result |
|---|---|
| Source copies, reference signatures and import separation | Pass |
| Ordinary build without Comparator | Pass |
| Canonical solution and independent reference build | Pass |
| Target axioms | Only `propext`, `Classical.choice`, `Quot.sound` |
| Native Comparator with Linux bubblewrap | Pass |
| Default Lean kernel replay | Accepted |

The downloaded log contains both `Lean default kernel accepts the solution`
and `Your solution is okay!`, and no sandbox-disabled warning. The workflow
job conclusions and downloaded artifact hashes are retained in
[public-ci-evidence.json](public-ci-evidence.json). The run records the two
library-backed targets `FujitaPublication.fujita` and
`FujitaPublication.variants.mixed`.

This remains a tentative public version. The standalone FC problem file has two
intentional `sorry` placeholders. Its dictionary to the proof-library definitions
is not implemented; its retained short header also still fails FC's copyright
linter. The proof CI does not claim to complete these separate tasks.

Documentation-only result updates use `[skip ci]` and do not change the tested
Lean sources. No upstream issue, comment or PR was posted.
