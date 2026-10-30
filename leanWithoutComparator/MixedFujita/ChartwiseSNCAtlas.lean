/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCStandardAtlas

/-!
Simple normal crossing charts covering each standard chart (step 10, R4-3).

Let `X` be a closed subscheme of projective space over a field with a simple normal crossing family
`ξ`. Every point of a standard chart `D₊(X_k) ∩ X` lies in a simple normal crossing chart whose open
is a basic open of that standard chart (`exists_isSNCChart_basicOpen_of_mem_chart`). Since the
standard chart is affine, finitely many of them cover it, so their defining functions generate the
unit ideal of its ring (`exists_finite_snc_chart_span`, Mathlib's `iSup_basicOpen_eq_self_iff`).

Spread out to the closure `T_A`, the relation `Σ h_j g_j = 1` in each standard chart makes the
spread-out basic opens cover the closure `T_A`, which the transfer of check 493 needs.
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

/-- **A simple normal crossing chart through a point of a standard chart, basic in that chart.** -/
theorem exists_isSNCChart_basicOpen_of_mem_chart [IsClosedImmersion e] (hsnc : IsSNCFamily K d ξ)
    (k : Fin n) (x : X) (hx : x ∈ projectivePullbackCoordinateOpen e k) :
    ∃ (c : EtaleChart K X d) (σ : Fin r → Option (Fin d))
      (s : Γ(X, projectivePullbackCoordinateOpen e k)),
      x ∈ c.U ∧ IsSNCChart c ξ σ ∧ c.U = X.basicOpen s := by
  obtain ⟨c₀, σ, hx₀, hc₀⟩ := hsnc x
  obtain ⟨t, s, hts, hxt⟩ := exists_basicOpen_le_affine_inter c₀.isAffine
    (projectivePullbackCoordinateOpen_isAffineOpen_of_isClosedImmersion e k) x ⟨hx₀, hx⟩
  exact ⟨etaleChartBasicOpen c₀ t ⟨⟨x, hxt⟩⟩, σ, s, hxt, isSNCChart_basicOpen hc₀ t ⟨⟨x, hxt⟩⟩,
    hts⟩

/-- **Finitely many simple normal crossing charts basic in a standard chart cover it**: their
defining functions span the unit ideal of the chart. -/
theorem exists_finite_snc_chart_span [IsClosedImmersion e] (hsnc : IsSNCFamily K d ξ)
    (k : Fin n) :
    ∃ (m : ℕ) (c : Fin m → EtaleChart K X d) (σ : Fin m → Fin r → Option (Fin d))
      (s : Fin m → Γ(X, projectivePullbackCoordinateOpen e k)),
      (∀ j, IsSNCChart (c j) ξ (σ j)) ∧ (∀ j, (c j).U = X.basicOpen (s j)) ∧
        Ideal.span (Set.range s) = ⊤ := by
  classical
  let V := projectivePullbackCoordinateOpen e k
  have hV : IsAffineOpen V := projectivePullbackCoordinateOpen_isAffineOpen_of_isClosedImmersion e k
  choose c σ s hxc hc hU using fun x : V => exists_isSNCChart_basicOpen_of_mem_chart e hsnc k x x.2
  -- the basic opens cover the chart
  have hcov : ⨆ f : Set.range s, X.basicOpen (f : Γ(X, V)) = V := by
    apply le_antisymm
    · exact iSup_le fun f => X.basicOpen_le _
    · intro x hx
      rw [Opens.mem_iSup]
      refine ⟨⟨s ⟨x, hx⟩, ⟨_, rfl⟩⟩, ?_⟩
      have := hxc ⟨x, hx⟩
      rw [hU] at this
      exact this
  have hspan : Ideal.span (Set.range s) = ⊤ := (hV.iSup_basicOpen_eq_self_iff).1 hcov
  -- a finite subfamily spans
  obtain ⟨t, hts, ht⟩ := (Ideal.span_eq_top_iff_finite (Set.range s)).1 hspan
  choose x hx using fun f : t => hts f.2
  let f : Fin t.card → V := fun j => x (t.equivFin.symm j)
  refine ⟨t.card, fun j => c (f j), fun j => σ (f j), fun j => s (f j), fun j => hc (f j),
    fun j => hU (f j), ?_⟩
  rw [eq_top_iff, ← ht, Ideal.span_le]
  intro g hg
  apply Ideal.subset_span
  refine ⟨t.equivFin ⟨g, hg⟩, ?_⟩
  simp only [f, Equiv.symm_apply_apply]
  exact hx ⟨g, hg⟩

end MixedFujita
