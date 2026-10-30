/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierSectionBertini
public import MixedFujita.ProjectiveClosureSmooth

/-!
Simple normal crossing charts inside the standard charts of projective space (step 10, R4-3).

Let `X` be a closed subscheme of projective space over a field, with a simple normal crossing
family `ξ`. Every point lies in a simple normal crossing chart whose open is also a basic open of
a standard chart `D₊(X_k) ∩ X` (`exists_isSNCChart_basicOpen_standard`): restrict a chart through
the point to a basic open that is basic in both affine opens (Mathlib's
`exists_basicOpen_le_affine_inter`). For quasi-compact `X` finitely many of them cover `X`
(`exists_finite_snc_standard_atlas`).

The functions on such a chart are a localization of the functions on a standard chart, so they
spread out to the closure of `X` over a finitely generated subring (checks 507–512).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))] {d n : ℕ}
  (e : X ⟶ polynomialProjectiveScheme n K) {r : ℕ} {ξ : Fin r → X}

/-- **A simple normal crossing chart through a point inside a standard chart**, whose open is a
basic open of that standard chart. -/
theorem exists_isSNCChart_basicOpen_standard [IsClosedImmersion e] (hsnc : IsSNCFamily K d ξ)
    (x : X) :
    ∃ (c : EtaleChart K X d) (σ : Fin r → Option (Fin d)) (k : Fin n)
      (s : Γ(X, projectivePullbackCoordinateOpen e k)),
      x ∈ c.U ∧ IsSNCChart c ξ σ ∧ c.U = X.basicOpen s := by
  obtain ⟨c₀, σ, hx₀, hc₀⟩ := hsnc x
  have hx : x ∈ (⨆ k, projectivePullbackCoordinateOpen e k) := by
    rw [iSup_projectivePullbackCoordinateOpen]
    trivial
  obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hx
  obtain ⟨t, s, hts, hxt⟩ := exists_basicOpen_le_affine_inter c₀.isAffine
    (projectivePullbackCoordinateOpen_isAffineOpen_of_isClosedImmersion e k) x ⟨hx₀, hk⟩
  exact ⟨etaleChartBasicOpen c₀ t ⟨⟨x, hxt⟩⟩, σ, k, s, hxt,
    isSNCChart_basicOpen hc₀ t ⟨⟨x, hxt⟩⟩, hts⟩

/-- **A finite simple normal crossing atlas of basic opens of the standard charts.** -/
theorem exists_finite_snc_standard_atlas [IsClosedImmersion e] [CompactSpace X]
    (hsnc : IsSNCFamily K d ξ) :
    ∃ (N : ℕ) (c : Fin N → EtaleChart K X d) (σ : Fin N → Fin r → Option (Fin d))
      (k : Fin N → Fin n) (s : ∀ i, Γ(X, projectivePullbackCoordinateOpen e (k i))),
      (∀ i, IsSNCChart (c i) ξ (σ i)) ∧ (∀ i, (c i).U = X.basicOpen (s i)) ∧
        ⨆ i, (c i).U = ⊤ := by
  classical
  choose c σ k s hx hc hU using fun x => exists_isSNCChart_basicOpen_standard e hsnc x
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => ((c x).U : Set X))
    (fun x => (c x).U.isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hx x⟩)
  let f : Fin t.card → X := fun i => (t.equivFin.symm i : X)
  refine ⟨t.card, fun i => c (f i), fun i => σ (f i), fun i => k (f i), fun i => s (f i),
    fun i => hc (f i), fun i => hU (f i), ?_⟩
  rw [eq_top_iff]
  intro y _
  have hy := ht (Set.mem_univ y)
  simp only [Set.mem_iUnion] at hy
  obtain ⟨x, hxt, hyx⟩ := hy
  rw [Opens.mem_iSup]
  refine ⟨t.equivFin ⟨x, hxt⟩, ?_⟩
  simpa [f] using hyx

end MixedFujita
