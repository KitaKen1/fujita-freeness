> **Tentative version.** The official version will be released soon.

# Lean proofs of Fujita freeness and its mixed variant

Fujita's freeness conjecture concerns global generation of adjoint line bundles
on smooth projective varieties. The classical statement comes from
[Fujita (1987)](https://doi.org/10.2969/aspm/01010167).

> **Statement 1 — Classical Fujita freeness.** Let $`X`$ be a smooth complex
> projective variety of dimension $`n\ge1`$, and let $`L`$ be an ample Cartier
> divisor. For every integer $`m\ge n+1`$,
>
> ```math
> K_X+mL\quad\text{is globally generated}.
> ```

[OpenAI's *Fujita's freeness conjecture*, Theorem 1.1
(23 September 2026)](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Fujitas-freeness-conjecture-September-23-2026)
presents a proof for $`K_X+(n+1)L`$. Its all-adjoint-powers corollary gives
Statement 1 for every $`m\ge n+1`$. Its minimization, center-exclusion and
lifting strategy informed this Lean development.

This repository also treats a mixed formulation, allowing distinct ample
divisors and an additional nef summand.

> **Statement 2 — Mixed Fujita freeness (F1).** Let $`X`$ be a smooth complex
> projective variety of dimension $`n\ge1`$. For ample Cartier divisors
> $`L_1,\ldots,L_s`$ with $`s\ge n+1`$, and a nef Cartier divisor $`N`$,
>
> ```math
> K_X+L_1+\cdots+L_s+N\quad\text{is globally generated}.
> ```

The mixed problem is the bound on convex Fujita numbers asked in
[Chen–Küronya–Mustopa–Stix, §1.2](https://arxiv.org/html/2301.06367v2#S1.SS2).
The nef summand can be absorbed into $`L_1`$, since $`L_1+N`$ is ample.
Taking $`s=m`$, every $`L_i=L`$ and $`N=0`$ recovers Statement 1.

Here global generation means that every point admits a global section that
does not vanish there. This package concerns the freeness part of Fujita's
conjectures.

| Element | Statement 1: classical | Statement 2: mixed F1 |
|---|---|---|
| Variety | Smooth complex projective, $`n\ge1`$ | The same |
| Ample divisors | One $`L`$, repeated $`m`$ times | Distinct $`L_1,\ldots,L_s`$ allowed |
| Bound | $`m\ge n+1`$ | $`s\ge n+1`$ |
| Nef summand | $`0`$ | Any nef Cartier $`N`$ |
| Conclusion | $`K_X+mL`$ globally generated | $`K_X+\sum_iL_i+N`$ globally generated |
| Source | Fujita's classical conjecture; OpenAI's 2026 manuscript | The mixed problem in CKMS §1.2, with the nef summand explicit |
| Relation | Specialization of Statement 2 | Allows the ample summands to vary |

This repository presents Lean proofs of both statements, using Lean
4.35.0-rc3 and a pinned Mathlib revision. Both are independent Comparator
targets in [FCSolution.lean](lean/FCSolution.lean). The classical target is
proved from the mixed target by the specialization above.

The two main components are:

1. **A Formal Conjectures style statement.**
   [FClikelean/Fujita.lean](FClikelean/Fujita.lean) contains six definitions,
   the classical statement and its mixed variant in one file.
2. **The library-backed Lean proof.**
   [ComplexFujitaFreeness.lean](lean/MixedFujita/ComplexFujitaFreeness.lean)
   supplies the mixed theorem over $`\mathbb C`$.
   [FCSolution.lean](lean/FCSolution.lean) supplies the two publication targets.

The dictionary between the standalone FC definitions and the proof library's
definitions remains to be implemented. The current Comparator result covers
the library-backed reference and solution.

## Formal Conjectures like targets

### FClikelean

The proposed problem file is [Fujita.lean](FClikelean/Fujita.lean).
`Fujita.fujita` is the main statement and `Fujita.variants.mixed` is its variant.
The file has 120 lines, six definitions, no `variable` declarations and one
instance. Its only import is `FormalConjecturesUtil`; its mathematical body
also elaborates with only Mathlib imports.

Cartier divisors are specified by compatible local equations. Global sections
are represented by rational functions, and the canonical divisor by local
differential lattices. The single instance supplies the complex algebra
structure for relative differentials. The section space is a set, so it needs
no additional scalar-tower declarations. The
[simplification check](verification/fc-simplification-result.json) verifies
agreement with the preceding definitions.

Both problem statements have intentional `by sorry` placeholders and retain
`@[category research open, AMS 14]`. A `formal_proof` link awaits the dictionary
to the external proof. The short author header is retained; its strict FC
copyright-linter result is recorded separately below.

### Comparator target

[Challenge.lean](lean/Challenge.lean) supplies the reference statements and
[FCSolution.lean](lean/FCSolution.lean) proves them. The targets are:

| Statement | Comparator declaration |
|---|---|
| Classical freeness | `FujitaPublication.fujita` |
| Mixed F1 | `FujitaPublication.variants.mixed` |

The reference and solution use exactly the same theorem signatures. The
reference import closure excludes the solution and the mixed-freeness proof
module. The [correspondence table](lean/comparator/TARGET-CORRESPONDENCE.md)
identifies the natural-language hypotheses and distinguishes the standalone
FC representation from the checked Challenge/solution representation.

## Mathematical explanation (AI generated)

Write $`A=L_1+\cdots+L_s`$. The proof establishes the mixed statement first
and then specializes it to the classical one.

**1. Obtain the numerical lower bound.** For every integral subvariety
$`W\subseteq X`$ of positive dimension $`d`$, mixed intersections of ample
Cartier divisors are positive integers. Expanding $`A^d`$ gives

```math
A^d\cdot W
=\sum_{i_1,\ldots,i_d=1}^{s}L_{i_1}\cdots L_{i_d}\cdot W
\ge s^d\ge(n+1)^d.
```

The Lean development supplies the corresponding asymptotic lower bound for
dimensions of restricted section spaces in
[AmpleCoprimeBridgeProof.lean](lean/MixedFujita/AmpleCoprimeBridgeProof.lean).

**2. Reduce a minimizing center to a point.** Suppose the adjoint bundle is
not generated at a prescribed point. The minimization argument compares
orders of sections with discrepancy. Attainment supplies a minimizer;
uniform restriction-space growth and a tangential first variation exclude
positive-dimensional centers. The numerical bound above is the positivity
input to this argument.

**3. Lift a nonzero fiber value.** On a suitable birational model, the
point-centered data and Kawamata–Viehweg vanishing produce a section of
$`K_X+A+N`$ that generates the fiber. Applying this at every point gives F1.
[KawamataViehwegCharZero.lean](lean/MixedFujita/KawamataViehwegCharZero.lean)
supplies the vanishing theorem and the resulting mixed-freeness theorem.

**4. Recover classical freeness.** Set $`s=m`$, $`L_i=L`$ and $`N=0`$.
Then $`\sum_i L_i=mL`$, so F1 gives global generation of $`K_X+mL`$.
This final reduction is the short proof of `FujitaPublication.fujita` in
[FCSolution.lean](lean/FCSolution.lean).

The [two-page guide](PDF/fujita-freeness-guide.pdf) summarizes the statements,
proof route and verification scope. It is a guide rather than a full proof paper.

## Files

| Directory | Lean version | Purpose |
|---|---|---|
| [lean/](lean/) | `v4.35.0-rc3` | Canonical proof, pinned dependencies, Challenge and FCSolution. |
| [leanWithoutComparator/](leanWithoutComparator/) | `v4.35.0-rc3` | The same proof for browsing and building, with Comparator-only files removed. |
| [FClikelean/](FClikelean/) | `v4.33.1` | Minimal standalone FC problem file. |
| [lean/comparator/](lean/comparator/) | `v4.35.0-rc3` | Source checks, correspondence, export scripts and verification guide. |
| [verification/](verification/) | Both pinned environments | Local build, Comparator, FC and source-audit records. |
| [PDF/](PDF/) | — | Statement and verification guide. |

The 2,310 shared Lean sources in the canonical and supplementary projects are
byte-identical. The package vendors the 2,307 local library modules required
by the proof imports. [PUBLICATION-MANIFEST.json](PUBLICATION-MANIFEST.json)
records the source snapshot. Vendored dependencies retain their
[authorship and license notices](lean/vendor/).
[PR-DRAFT.md](PR-DRAFT.md) contains the local FC pull request draft.

## Verification

### Lean execution results

The proof and reference build on Lean 4.35.0-rc3 with Mathlib fixed at
`f6090c7095e1e56b3464c1daba5f24631f1290d2`.
[FCAudit.lean](lean/FCAudit.lean) audits both publication targets. Each depends
only on `[propext, Classical.choice, Quot.sound]`. The solution has no `sorry`
or custom axioms. Dependency style and deprecation warnings remain in the
build logs.

The [source audit](verification/input-check.json) checks the target signatures,
source hashes, matching proof copies, dependency pins and reference-import
separation. See the [local verification record](verification/local-result.json).

### Lean Comparator check

The reference, solution, exporter and native Comparator use the pinned
Lean 4.35.0-rc3 toolchain. Both target comparisons and the built-in kernel
replay passed locally. The macOS command used
`--inadvisably-no-sandbox`; the receipt records that the Linux-only sandbox
was disabled. See the [Comparator result](verification/local-comparator-result.json)
and [log](verification/comparator.log).

### Standalone FC check

The FC audit uses official commit
`c83a94d785d0fb3b9b9a2a94e8ffff8cce76a346`, Lean 4.33.1 and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`.

| Check | Result |
|---|---|
| Mathematical body with Mathlib only | Pass |
| Strict FC build/linter with the required FC header | Pass |
| Canonical file with the retained short author header | Copyright-linter failure |
| Dictionary to the proof-library definitions | Pending |

The standard-header audit temporarily changes only the header and restores
the canonical file. No FC linter is disabled. The
[FC receipt](verification/fc-local-result.json) records both outcomes, and
the checker returns nonzero for the canonical short-header failure.

The historical local receipts describe the earlier local experiment. The
public GitHub Actions workflow independently checks the current source; see
[the CI record](verification/CI.md) and [Actions](https://github.com/KitaKen1/fujita-freeness/actions).
No independent mathematical peer review is claimed.

## Appendix: timeline (AI generated)

Selected milestones in the classical and mixed problems:

| Date | Contributor | Contribution |
|---|---|---|
| 1987 | Takao Fujita | Published the adjoint-bundle conjectures in [On polarized manifolds whose adjoint bundles are not semipositive](https://doi.org/10.2969/aspm/01010167). |
| 30 June 2024 (v2) | Jiaming Chen, Alex Küronya, Yusuf Mustopa and Jakob Stix | Defined convex Fujita numbers and asked whether they are always at most $`\dim X+1`$; this is the mixed problem underlying F1 ([§1.2](https://arxiv.org/html/2301.06367v2#S1.SS2)). |
| 23 September 2026 | OpenAI | Released the [classical Fujita manuscript](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Fujitas-freeness-conjecture-September-23-2026), with Theorem 1.1 and the all-adjoint-powers corollary. |
| 23 October 2026 | This repository | Packaged the classical and mixed Lean targets and completed their [local Comparator and kernel check](verification/local-comparator-result.json). |

Fujita is the source of the classical conjecture; CKMS is the source of the
mixed problem. OpenAI's manuscript supplies a proof strategy for the classical
case. Adapted OpenAI modules for other foundational results, along with the
other vendored libraries, are identified in
[vendor/provenance.json](lean/vendor/provenance.json).

## Appendix: reproduce the local verification

Build the ordinary proof project:

```sh
cd leanWithoutComparator
lake exe cache get
lake build
```

From the repository root, check the source copies and target signatures:

```sh
python3 lean/comparator/check-inputs.py
```

On Linux with bubblewrap available:

```sh
cd lean
lake exe cache get
lake comparator
```

The [Comparator guide](lean/comparator/README.md) gives the macOS export and
replay commands. To repeat the standalone FC audit in the pinned official
checkout:

```sh
python3 lean/comparator/check-fclike.py --fc-root /path/to/formal-conjectures
```

Local `.lake` caches are ignored. The verification records distinguish the
canonical FC file from the temporary standard-header audit.

Kenta Kitamura developed this project with assistance from ChatGPT and OpenAI
Codex. Project code is Apache-2.0; vendored sources retain their notices and
licenses, including MIT for SGA. See [LICENSE](LICENSE) and [vendor](lean/vendor/).
