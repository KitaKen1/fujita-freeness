# Statement correspondence

The primary target is Fujita's classical freeness statement. The mixed theorem is
a related variant. The scope is integral smooth complex projective varieties of
positive dimension, and global generation of line bundles.

| Natural-language clause | Library-backed reference and solution |
|---|---|
| Complex variety | Integral scheme over `Spec ℂ` |
| Dimension n ≥ 1 | `topologicalKrullDim X = n`, `1 ≤ n` |
| Smooth | `SmoothOfRelativeDimension n` |
| Projective and ample Cartier divisor | `CartierIsAmpleProj ℂ L` provides a projective embedding after a positive multiple. The same applies to every Lᵢ. |
| Canonical divisor | `smoothCanonicalDivisor c₀`, obtained from a reference étale chart. The library proves invariance under a change of chart. |
| Classical bound | `n + 1 ≤ m` |
| Mixed bound | `n + 1 ≤ s` |
| N nef | `CartierIsNef ℂ N`, tested on proper smooth curves |
| Global generation | Actual global sections of the invertible sheaf have a unit local coefficient at every scheme point |

The reference and solution theorem signatures agree exactly. In the solution,
`fujita` is proved from `variants.mixed` using `s = m`, constant `Lᵢ = L`, and `N = 0`.
The finite sum reduces to `m • L`. This is a Lean-checked specialization in the
library-backed representation.

## Separate FC representation

`FClikelean/Fujita.lean` uses compatible local Cartier equations, rational section
spaces and differential lattices. Its definitions are copied from the earlier
self-contained mathematical representation, with all F2-specific definitions removed.
Properness is explicit, and the ample divisor supplies projectivity.

The standalone file's main theorem is `Fujita.fujita`; its variant is
`Fujita.variants.mixed`. The new file has two intentional problem-statement holes,
no definition holes and no proof-project imports.

A mathematical interpretation of the local equations is available, but a Lean
dictionary from this representation to the sheaf-based library is not established.
Comparator checks the separate Challenge/solution representation, not this FC file.
No cross-representation proof link or `research solved` claim is made for the FC draft.

The two proof copies, FC elaboration, source correspondence and independent human
mathematical review are different checks. The records identify which were performed.
