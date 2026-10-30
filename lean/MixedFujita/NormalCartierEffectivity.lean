/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RationalCartierWeilDictionary
public import MixedFujita.LogPairDenominatorScaling
public import OAI.AlgebraicGeometry.SectionFields.Recovery

/-!
On a normal Noetherian scheme, nonnegative actual prime coefficients imply
Cartier effectivity by Hartogs. Thus a nonnegative Q-Cartier Weil divisor
has an actual effective Cartier multiple. Coefficients below one give the
exact integral coefficient window at that denominator; this is not an
all-model klt assertion.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]

/-- Cartier effectivity on a normal scheme is equivalent to nonnegative prime coefficients. -/
theorem normal_cartier_isEffective_iff_coefficients_nonneg
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (C : CartierDivisor X) :
    C.IsEffective ↔ ∀ z : CodimensionOnePoint X, 0 ≤ cartierCoefficient C (z : X) := by
  constructor
  · intro h z
    exact cartierCoefficient_nonneg_of_isEffective C h (z : X)
  · intro h
    apply CartierDivisor.isEffective_iff_exists.mpr
    intro x
    obtain ⟨f, hf⟩ := C.exists_isLocalEquationAt x
    obtain ⟨U, hxU, hU⟩ := CartierDivisor.isLocalEquationAt_iff.mp hf
    letI : Nonempty U := ⟨⟨x, hxU⟩⟩
    obtain ⟨s, hs⟩ := OAI.RelativeDenominators.exists_section_of_ord_nonneg X hnorm U
      (f : X.functionField) (Units.ne_zero f) (by
        intro z hz hcod
        rw [← cartierCoefficient_eq_ord
          (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hU hz)]
        exact h ⟨z, hcod⟩)
    refine ⟨f, hf, X.presheaf.germ U x hxU s, ?_⟩
    exact (X.algebraMap_germ_eq_germToFunctionField hxU s).trans hs

/-- A nonnegative Q-Cartier Weil divisor has an actual effective Cartier multiple, and conversely. -/
theorem nonnegative_isQCartier_iff_exists_effective_cartier_multiple
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (b : CodimensionOnePoint X →₀ ℚ) (hb : ∀ z, 0 ≤ b z) :
    OAI.RelativeDenominators.IsQCartier X b ↔
      ∃ (m : ℕ), 0 < m ∧ ∃ C : CartierDivisor X, C.IsEffective ∧
        ∀ z : CodimensionOnePoint X, (cartierCoefficient C (z : X) : ℚ) = (m : ℚ) * b z := by
  constructor
  · intro h
    obtain ⟨m, hm, C, hC⟩ := (isQCartier_iff_exists_actual_cartier_multiple hnorm b).mp h
    refine ⟨m, hm, C, (normal_cartier_isEffective_iff_coefficients_nonneg hnorm C).mpr ?_, hC⟩
    intro z
    have hz : (0 : ℚ) ≤ (cartierCoefficient C (z : X) : ℚ) := by
      rw [hC z]
      exact mul_nonneg (Nat.cast_nonneg m) (hb z)
    exact_mod_cast hz
  · rintro ⟨m, hm, C, _, hC⟩
    exact (isQCartier_iff_exists_actual_cartier_multiple hnorm b).mpr ⟨m, hm, C, hC⟩

/-- The strict rational coefficient window yields an actual effective numerator with coefficients below its denominator. -/
theorem exists_effective_cartier_multiple_of_isQCartier_coefficients_mem_Ico
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (b : CodimensionOnePoint X →₀ ℚ) (hb : ∀ z, b z ∈ Set.Ico (0 : ℚ) 1)
    (hQ : OAI.RelativeDenominators.IsQCartier X b) :
    ∃ (m : ℕ), 0 < m ∧ ∃ C : CartierDivisor X, C.IsEffective ∧
      (∀ z : CodimensionOnePoint X, (cartierCoefficient C (z : X) : ℚ) = (m : ℚ) * b z) ∧
      ∀ z : CodimensionOnePoint X, 0 ≤ cartierCoefficient C (z : X) ∧
        cartierCoefficient C (z : X) < (m : ℤ) := by
  obtain ⟨m, hm, C, heff, hC⟩ :=
    (nonnegative_isQCartier_iff_exists_effective_cartier_multiple hnorm b (fun z => (hb z).1)).mp hQ
  refine ⟨m, hm, C, heff, hC, fun z => ⟨cartierCoefficient_nonneg_of_isEffective C heff _, ?_⟩⟩
  have hlt : (cartierCoefficient C (z : X) : ℚ) < (m : ℚ) := by
    rw [hC z]
    exact (mul_lt_mul_of_pos_left (hb z).2 (by exact_mod_cast hm)).trans_eq (mul_one _)
  exact_mod_cast hlt

end MixedFujita
