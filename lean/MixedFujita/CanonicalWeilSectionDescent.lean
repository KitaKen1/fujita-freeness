/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FixedSNCDirectImagePrimeBounds
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Sheaf

/-! Turn rational descent with primewise bounds into unique actual sections
of the actual Weil divisor sheaf. This constructs the target section; it does
not assert that every target section comes from the source direct image. -/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- An actual Cartier direct-image section with rational descent and prime
bounds determines a unique actual section of the corresponding Weil sheaf. -/
theorem cartier_direct_image_section_unique_weil_section_of_prime_bounds
    {S B : Scheme.{u}} [IsIntegral S] [IsIntegral B] [IsLocallyNoetherian B]
    [∀ η : CodimensionOnePoint B, IsDiscreteValuationRing (B.presheaf.stalk (η : B))]
    (q : S ⟶ B) [IsDominant q] (E : CartierDivisor S) (R : SchemeWeilDivisor B)
    (U : B.Opens) [Nonempty U] (s : Γ(E.sheaf, q ⁻¹ᵁ U))
    (hdesc : letI := dominant_preimage_nonempty q U
      ∃ z : B.functionField,
        (dominantFunctionFieldMap q).hom z =
          rationalFunctionsEquiv (X := S) (q ⁻¹ᵁ U)
            (Scheme.Modules.Hom.app E.sheafι (q ⁻¹ᵁ U) s) ∧
        ∀ η : CodimensionOnePoint B, (η : B) ∈ U → z = 0 ∨
          0 ≤ B.ord z (η : B) + R η) :
    letI := dominant_preimage_nonempty q U
    ∃! t : Γ(SchemeWeilDivisor.sheaf R, U),
      (dominantFunctionFieldMap q).hom
        (rationalFunctionsEquiv (X := B) U
          (Scheme.Modules.Hom.app (SchemeWeilDivisor.sheafι R) U t)) =
      rationalFunctionsEquiv (X := S) (q ⁻¹ᵁ U)
        (Scheme.Modules.Hom.app E.sheafι (q ⁻¹ᵁ U) s) := by
  letI := dominant_preimage_nonempty q U
  obtain ⟨z, hz, hbound⟩ := hdesc
  have hmem : (rationalFunctionsEquiv (X := B) U).symm z ∈
      SchemeWeilDivisor.sections R U := by
    apply SchemeWeilDivisor.mem_sections.mpr
    intro η hηU
    rw [LinearEquiv.apply_symm_apply]
    rcases hbound η hηU with hzero | hb
    · exact Or.inl hzero
    · right
      change -R η ≤ B.ord z (η : B)
      omega
  let t : Γ(SchemeWeilDivisor.sheaf R, U) := SchemeWeilDivisor.sectionMk _ hmem
  refine ⟨t, ?_, ?_⟩
  · simpa only [t, SchemeWeilDivisor.sheafι_app_sectionMk,
      LinearEquiv.apply_symm_apply] using hz
  · intro t' ht'
    apply SchemeWeilDivisor.sheafι_app_injective R U
    apply (rationalFunctionsEquiv (X := B) U).injective
    apply (dominantFunctionFieldMap q).hom.injective
    simpa only [t, SchemeWeilDivisor.sheafι_app_sectionMk,
      LinearEquiv.apply_symm_apply] using ht'.trans hz.symm

end MixedFujita
