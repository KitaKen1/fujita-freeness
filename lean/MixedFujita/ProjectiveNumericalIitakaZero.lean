/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ProjectiveNumericallyTrivialSectionBounds
public import MixedFujita.ProjectiveNumericallyTrivialPrincipality
public import MixedFujita.IitakaGrowth
public import MixedFujita.CartierGlobalGenerationOperations

/-! 全正次元での数値自明と実飯高次元0の辞書。 See reports/check-215-curve-f1-f2-integration.json for the verified scope. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Order
open scoped Classical
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra
  functionFieldBaseScalarTower

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
  {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  {n : ℕ} (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
  (hproj : ∃ H : CartierDivisor X, CartierIsAmpleProj K H)
include hdim hn hproj


theorem projective_iitakaZero_of_numericallyTrivial_of_positive_generated_multiple
    (D : CartierDivisor X) (hD : CartierIsNumericallyTrivial K D)
    (hgg : ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • D)) :
    CartierIitakaDimension K D 0 := by
  obtain ⟨q, hq, hgg⟩ := hgg
  constructor
  · refine ⟨1, zero_lt_one, Filter.frequently_atTop.mpr ?_⟩
    intro b
    refine ⟨(b + 1) * q, by nlinarith, ?_⟩
    have hgen : CartierIsGloballyGenerated (((b + 1) * q) • D) := by
      rw [mul_nsmul']
      exact cartierIsGloballyGenerated_nsmul (q • D) hgg (b + 1)
    letI := (projective_numericallyTrivial_graded_sections_bound hdim hn hproj D hD
      ((b + 1) * q)).1
    have hpos : 0 < Module.finrank K Γ(((((b + 1) * q) • D)).sheaf, ⊤) :=
      Module.finrank_pos_iff_exists_ne_zero.mpr
        (cartierIsGloballyGenerated_exists_nonzero_section hgen)
    have hle : (1 : ℝ) ≤ Module.finrank K Γ(((((b + 1) * q) • D)).sheaf, ⊤) := by
      exact_mod_cast hpos
    simpa only [pow_zero, mul_one] using hle
  · refine ⟨1, fun j => ?_⟩
    have hle := (projective_numericallyTrivial_graded_sections_bound hdim hn hproj D hD j).2
    simp only [pow_zero, mul_one]
    exact_mod_cast hle


theorem projective_iitakaZero_iff_numericallyTrivial_of_eventually_globallyGenerated
    (D : CartierDivisor X)
    (hgg : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → CartierIsGloballyGenerated (q • D)) :
    CartierIitakaDimension K D 0 ↔ CartierIsNumericallyTrivial K D := by
  constructor
  · intro hk
    obtain ⟨φ, hφ⟩ := principal_of_eventually_globallyGenerated_of_iitakaZero
      hdim hn hproj D hgg hk
    rw [hφ]
    exact cartierIsNumericallyTrivial_principal φ
  · intro hD
    obtain ⟨q₀, hq₀⟩ := hgg
    exact projective_iitakaZero_of_numericallyTrivial_of_positive_generated_multiple
      hdim hn hproj D hD ⟨max q₀ 1, by omega, hq₀ _ (le_max_left _ _)⟩

end MixedFujita
