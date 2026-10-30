/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ConormalDifferentials

/-!
Coordinates through a function with a nonzero differential (step 9, restriction theorem).

A linearly independent family of fewer than dim W vectors extends by a member of any spanning
family (`exists_linearIndependent_snoc_of_span_eq_top`); the differentials 1 ⊗ d r of the
elements span the differentials at a point (`span_tmul_D_eq_top`). Hence on a smooth scheme of
relative dimension N + 1, a function t on an affine open with a nonzero differential at a K-point
is the first of N + 1 functions with independent differentials there
(`exists_differentialsIndependentAt_cons`), which are étale coordinates on a basic open around the
point (check-318). For t in the ideal of a smooth closed subvariety this is the chart in which the
hypersurface t = 0 is a coordinate hyperplane, for the induction on the codimension in the
restriction theorem.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped TensorProduct
open KaehlerDifferential

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

universe u

section LinearAlgebra

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W]

/-- A linearly independent family of fewer than dim W vectors extends by a member of any spanning
family. -/
theorem exists_linearIndependent_snoc_of_span_eq_top {ι : Type*} (f : ι → W)
    (hf : Submodule.span K (Set.range f) = ⊤) {n : ℕ} {v : Fin n → W}
    (hv : LinearIndependent K v) (h : n < Module.finrank K W) :
    ∃ i, LinearIndependent K (Fin.snoc v (f i) : Fin (n + 1) → W) := by
  by_contra hno
  push Not at hno
  have hle : Submodule.span K (Set.range f) ≤ Submodule.span K (Set.range v) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    by_contra hi
    exact hno i (linearIndependent_finSnoc.mpr ⟨hv, hi⟩)
  rw [hf, top_le_iff] at hle
  have h2 : Module.finrank K (Submodule.span K (Set.range v)) ≤ n := by
    have h3 := finrank_range_le_card (R := K) v
    rw [Fintype.card_fin] at h3
    exact h3
  rw [hle, finrank_top] at h2
  omega

end LinearAlgebra

section Span

variable (K : Type*) [Field K] {R : Type*} [CommRing R] [Algebra K R] [Algebra R K]

/-- The differentials of the elements span the differentials at a point. -/
theorem span_tmul_D_eq_top :
    Submodule.span K (Set.range fun r : R => (1 : K) ⊗ₜ[R] D K R r) = ⊤ := by
  have h := Submodule.baseChange_span (R := R) (A := K) (Set.range (D K R))
  rw [KaehlerDifferential.span_range_derivation, Submodule.baseChange_top] at h
  have h1 : (Set.range fun r : R => (1 : K) ⊗ₜ[R] D K R r) =
      TensorProduct.mk R K Ω[R⁄K] 1 '' Set.range (D K R) := by
    rw [← Set.range_comp]
    rfl
  rw [h1, ← h]

end Span

section Extend

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  {N : ℕ} [SmoothOfRelativeDimension (N + 1) (X ↘ Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra

/-- A function on an affine open of a smooth scheme of relative dimension N + 1 with a nonzero
differential at a K-point is the first of N + 1 functions with independent differentials
there. -/
theorem exists_differentialsIndependentAt_cons {V : X.Opens} (hV : IsAffineOpen V) (x : X)
    (hx : x ∈ V) (χ : Γ(X, V) →ₐ[K] K)
    (hχ : ∀ a, χ a = 0 ↔ a ∈ (hV.primeIdealOf ⟨x, hx⟩).asIdeal) (t : Γ(X, V))
    (ht : DifferentialsIndependentAt K χ ![t]) :
    ∃ u : Fin N → Γ(X, V), DifferentialsIndependentAt K χ (Fin.cons t u) := by
  letI : Algebra Γ(X, V) K := χ.toRingHom.toAlgebra
  obtain ⟨-, hrank⟩ := finrank_tmul_kaehler_eq (N := N + 1) hV x hx χ hχ
  have hspan := span_tmul_D_eq_top K (R := Γ(X, V))
  have h0 : (1 : K) ⊗ₜ[Γ(X, V)] D K Γ(X, V) t ≠ 0 := by
    have h := ht
    dsimp only [DifferentialsIndependentAt] at h
    exact h.ne_zero 0
  have key : ∀ k ≤ N, ∃ u : Fin k → Γ(X, V), LinearIndependent K
      (Fin.cons ((1 : K) ⊗ₜ[Γ(X, V)] D K Γ(X, V) t)
        (fun l => (1 : K) ⊗ₜ[Γ(X, V)] D K Γ(X, V) (u l)) : Fin (k + 1) → _) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨Fin.elim0, ?_⟩
      rw [linearIndependent_finCons]
      refine ⟨linearIndependent_empty_type, ?_⟩
      rw [Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot]
      exact h0
    | succ k ih =>
      intro hk
      obtain ⟨u, hu⟩ := ih (by omega)
      obtain ⟨a, ha⟩ := exists_linearIndependent_snoc_of_span_eq_top
        (fun r : Γ(X, V) => (1 : K) ⊗ₜ[Γ(X, V)] D K Γ(X, V) r) hspan hu (by omega)
      refine ⟨Fin.snoc u a, ?_⟩
      have h1 : (fun l => (1 : K) ⊗ₜ[Γ(X, V)] D K Γ(X, V)
          ((Fin.snoc u a : Fin (k + 1) → Γ(X, V)) l)) =
          Fin.snoc (fun l => (1 : K) ⊗ₜ[Γ(X, V)] D K Γ(X, V) (u l))
            ((1 : K) ⊗ₜ[Γ(X, V)] D K Γ(X, V) a) :=
        Fin.comp_snoc (fun r => (1 : K) ⊗ₜ[Γ(X, V)] D K Γ(X, V) r) u a
      rw [h1, Fin.cons_snoc_eq_snoc_cons]
      exact ha
  obtain ⟨u, hu⟩ := key N le_rfl
  refine ⟨u, ?_⟩
  dsimp only [DifferentialsIndependentAt]
  have h2 : (fun l => (1 : K) ⊗ₜ[Γ(X, V)] D K Γ(X, V)
      ((Fin.cons t u : Fin (N + 1) → Γ(X, V)) l)) =
      Fin.cons ((1 : K) ⊗ₜ[Γ(X, V)] D K Γ(X, V) t)
        (fun l => (1 : K) ⊗ₜ[Γ(X, V)] D K Γ(X, V) (u l)) :=
    Fin.comp_cons (fun r => (1 : K) ⊗ₜ[Γ(X, V)] D K Γ(X, V) r) t u
  rw [h2]
  exact hu

end Extend

end MixedFujita
