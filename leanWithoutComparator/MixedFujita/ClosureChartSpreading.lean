/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ChartwiseSNCAtlas
public import MixedFujita.ProjectiveClosureSmooth

/-!
Functions on the standard charts spread out to the closure (step 10, R4-3).

Let `e : T → ℙ_K` be a closed immersion and `T_A` its closure over a subring `A ⊆ K` (check 507).
* `exists_fg_forall_mem_range_closureChartMap`: finitely many functions on a standard chart of `T`
  come from the closure `T_A` once `A` contains the coefficients of polynomials representing them
  (the chart ring of `T` is a quotient of `K[X/X_k]`, and `closureChartMap_projectiveChartRingMap`).
* `exists_fg_forall_iSup_basicOpen_eq_top`: if on each standard chart finitely many functions span
  the unit ideal (check 531), then for `A` large enough they come from functions on the charts of
  `T_A` whose basic opens cover `T_A`: the relations `Σ h_j g_j = 1` hold on `T_A` because the
  chart rings of `T_A` embed into those of `T` (`closureChartMap_injective`).
* `preimage_basicOpen_closureChartMap`: the basic open of a function on `T_A` pulls back to the
  basic open of its image.

These make the simple normal crossing atlas of `T` (check 531) an atlas of `T_A`, as needed for the
transfer of check 493.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {n : ℕ} {K : Type u} [Field K] {T : Scheme.{u}} (e : T ⟶ polynomialProjectiveScheme n K)

/-- **Finitely many functions on a standard chart come from the closure over a large subring.** -/
theorem exists_fg_forall_mem_range_closureChartMap [IsClosedImmersion e] (k : Fin n)
    (S : Finset Γ(T, projectivePullbackCoordinateOpen e k)) :
    ∃ A₀ : Subalgebra ℤ K, A₀.FG ∧ ∀ A : Subalgebra ℤ K, A₀ ≤ A → ∀ h ∈ S,
      h ∈ Set.range (closureChartMap (algebraMap A K) e k) := by
  classical
  choose P hP using fun h : Γ(T, projectivePullbackCoordinateOpen e k) =>
    projectiveChartRingMap_surjective e k h
  let C : Finset K := S.biUnion fun h => (P h).coeffs
  refine ⟨Algebra.adjoin ℤ (C : Set K), ⟨C, rfl⟩, fun A hA h hh => ?_⟩
  have hmem : P h ∈ Set.range (MvPolynomial.map (algebraMap A K)) := by
    refine MvPolynomial.mem_range_map_iff_coeffs_subset.2 fun z hz => ?_
    have hzC : z ∈ (C : Set K) := Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨h, hh, hz⟩)
    exact ⟨⟨z, hA (Algebra.subset_adjoin hzC)⟩, rfl⟩
  obtain ⟨P', hP'⟩ := hmem
  refine ⟨projectiveChartRingMap (projectiveClosureι (algebraMap A K) e) k P', ?_⟩
  rw [closureChartMap_projectiveChartRingMap, hP', hP]

/-- The basic open of a function on the closure pulls back to the basic open of its image. -/
theorem preimage_basicOpen_closureChartMap {A : Type u} [CommRing A] (c : A →+* K) (k : Fin n)
    (s : Γ(projectiveClosure c e, projectivePullbackCoordinateOpen (projectiveClosureι c e) k)) :
    projectiveClosureMap c e ⁻¹ᵁ (projectiveClosure c e).basicOpen s =
      T.basicOpen (closureChartMap c e k s) := by
  rw [closureChartMap, Scheme.basicOpen_appLE, ← projectiveClosureMap_preimage_chart c e k]
  apply le_antisymm
  · intro x hx
    exact ⟨Scheme.Hom.preimage_mono (projectiveClosureMap c e)
      ((projectiveClosure c e).basicOpen_le s) hx, hx⟩
  · exact inf_le_right

/-- **The spread-out charts cover the closure**: functions spanning the unit ideal on every
standard chart of `T` come from functions on the charts of `T_A` whose basic opens cover `T_A`. -/
theorem exists_fg_forall_iSup_basicOpen_eq_top [IsClosedImmersion e] {m : Fin n → ℕ}
    (s : ∀ k, Fin (m k) → Γ(T, projectivePullbackCoordinateOpen e k))
    (hs : ∀ k, Ideal.span (Set.range (s k)) = ⊤) :
    ∃ A₀ : Subalgebra ℤ K, A₀.FG ∧ ∀ A : Subalgebra ℤ K, A₀ ≤ A →
      ∃ sA : ∀ k, Fin (m k) → Γ(projectiveClosure (algebraMap A K) e,
          projectivePullbackCoordinateOpen (projectiveClosureι (algebraMap A K) e) k),
        (∀ k j, closureChartMap (algebraMap A K) e k (sA k j) = s k j) ∧
          ⨆ k, ⨆ j, (projectiveClosure (algebraMap A K) e).basicOpen (sA k j) = ⊤ := by
  classical
  -- the relations `Σ h_j s_j = 1`
  have hrel : ∀ k, ∃ h : Fin (m k) → Γ(T, projectivePullbackCoordinateOpen e k),
      ∑ j, h j * s k j = 1 := by
    intro k
    have h1 : (1 : Γ(T, projectivePullbackCoordinateOpen e k)) ∈ Ideal.span (Set.range (s k)) := by
      rw [hs k]
      trivial
    exact (Ideal.mem_span_range_iff_exists_fun).1 h1
  choose h hh using hrel
  -- spread the finitely many functions
  have hspread := fun k => exists_fg_forall_mem_range_closureChartMap e k
    ((Finset.univ.image (s k)) ∪ (Finset.univ.image (h k)))
  choose A₀ hA₀ hA₀' using hspread
  choose S hS using fun k => hA₀ k
  let C : Finset K := Finset.univ.biUnion S
  refine ⟨Algebra.adjoin ℤ (C : Set K), ⟨C, rfl⟩, fun A hA => ?_⟩
  have hAk : ∀ k, A₀ k ≤ A := by
    intro k
    rw [← hS k, Algebra.adjoin_le_iff]
    intro z hz
    exact hA (Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_biUnion.2
      ⟨k, Finset.mem_univ _, Finset.mem_coe.1 hz⟩)))
  have hsmem : ∀ k j, s k j ∈ Set.range (closureChartMap (algebraMap A K) e k) := fun k j =>
    hA₀' k A (hAk k) _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
  have hhmem : ∀ k j, h k j ∈ Set.range (closureChartMap (algebraMap A K) e k) := fun k j =>
    hA₀' k A (hAk k) _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
  choose sA hsA using hsmem
  choose hA' hhA using hhmem
  refine ⟨sA, hsA, ?_⟩
  have : QuasiCompact (e ≫ polynomialProjectiveCoefficientMap (algebraMap A K)) := by
    have := polynomialProjectiveCoefficientMap_isAffineHom (n := n) (algebraMap A K)
    infer_instance
  -- the relations hold on the closure
  have hrelA : ∀ k, ∑ j, hA' k j * sA k j = 1 := by
    intro k
    apply closureChartMap_injective (algebraMap A K) e k
    rw [map_sum, map_one]
    simp only [map_mul, hsA, hhA]
    exact hh k
  rw [eq_top_iff, ← iSup_projectivePullbackCoordinateOpen (projectiveClosureι (algebraMap A K) e)]
  refine iSup_le fun k => ?_
  have hV := projectivePullbackCoordinateOpen_isAffineOpen_of_isClosedImmersion
    (projectiveClosureι (algebraMap A K) e) k
  have hspanA : Ideal.span (Set.range (sA k)) = ⊤ := by
    rw [eq_top_iff, ← (Ideal.span_singleton_one), Ideal.span_le, Set.singleton_subset_iff,
      SetLike.mem_coe, ← hrelA k]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
  have hcov := (hV.iSup_basicOpen_eq_self_iff).2 hspanA
  rw [← hcov]
  refine iSup_le fun f => ?_
  obtain ⟨_, j, rfl⟩ := f
  exact le_iSup_of_le k (le_iSup_of_le j le_rfl)

end MixedFujita
