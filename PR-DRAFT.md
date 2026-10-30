# Draft: Fujita's freeness conjecture and its mixed variant

This is a local draft, not a submitted PR. The standalone FC statement still needs
its representation connected to the external proof before a formal proof link is added.

**Proposed title:** `feat(Paper): add Fujita's freeness conjecture and its mixed variant`

Formalizes Fujita's freeness conjecture for smooth complex projective varieties:
`K_X + mL` is globally generated for every integer `m ≥ dim X + 1`.
Includes the mixed problem from Chen–Küronya–Mustopa–Stix §1.2 as a related variant,
with distinct ample divisors and a nef summand. Taking equal ample divisors and
the nef summand zero recovers the classical statement.

Sources:

- [Fujita (1987)](https://doi.org/10.2969/aspm/01010167): original conjecture.
- [CKMS §1.2](https://arxiv.org/html/2301.06367v2#S1.SS2): mixed problem.
- [OpenAI (2026), Theorem 1.1](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Fujitas-freeness-conjecture-September-23-2026): claimed proof of the classical case and a methodological source for this proof development.

The proposed problem file contains its definitions and imports only
`FormalConjecturesUtil`. The external library-backed Lean proof uses the same
mathematical hypotheses, and its two target proofs have only the standard three
axioms. The dictionary to the standalone statement's different representation
remains to be supplied; the draft therefore has no `formal_proof` attribute.

Local validation is recorded in `verification/`. The mathematical body elaborates
with only Mathlib. The official FC audit passes with its standard copyright header;
the retained short project header fails the strict copyright linter. This draft
does not claim that the canonical short file passes all FC linters.

Related to issue #7012, restricted to its mixed-Fujita component. F2 is outside
this proposal. Mathematical exploration and formalization used ChatGPT and OpenAI Codex.
