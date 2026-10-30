/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ExceptionalCartierSections
public import MixedFujita.DominantOpenBaseRestriction

/-! Actual rational Cartier sections on a base inverse-image open pull back
to a smaller actual base restriction, with the same base rational function. -/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- Restrict a pulled base rational Cartier section through the actual
base-change square; the field maps are the actual dominant maps. -/
theorem cartier_rational_section_on_base_open_restriction
    {S B : Scheme.{u}} [IsIntegral S] [IsIntegral B]
    (q : S ⟶ B) [IsDominant q] (E : CartierDivisor S)
    (W U : B.Opens) [Nonempty W] [Nonempty U] (hUW : U ≤ W)
    (z : B.functionField)
    (hs : letI := dominant_preimage_nonempty q W
      (rationalFunctionsEquiv (X := S) (q ⁻¹ᵁ W)).symm
        ((dominantFunctionFieldMap q).hom z) ∈ E.sections (q ⁻¹ᵁ W)) :
    letI := dominant_preimage_nonempty q U
    letI : IsDominant U.ι :=
      ⟨U.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
    letI : IsDominant (q ⁻¹ᵁ U).ι :=
      ⟨(q ⁻¹ᵁ U).ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
    letI : IsDominant (q ∣_ U) := isDominant_morphismRestrict_integral q U
    (rationalFunctionsEquiv (X := (q ⁻¹ᵁ U).toScheme) ⊤).symm
      ((dominantFunctionFieldMap (q ∣_ U)).hom ((dominantFunctionFieldMap U.ι).hom z)) ∈
        (cartierPullback (q ⁻¹ᵁ U).ι E).sections ⊤ := by
  letI := dominant_preimage_nonempty q W
  letI := dominant_preimage_nonempty q U
  letI : IsDominant U.ι :=
    ⟨U.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  letI : IsDominant (q ⁻¹ᵁ U).ι :=
    ⟨(q ⁻¹ᵁ U).ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  letI : IsDominant (q ∣_ U) := isDominant_morphismRestrict_integral q U
  have hopen : (q ⁻¹ᵁ U).ι ⁻¹ᵁ (q ⁻¹ᵁ W) = ⊤ := by
    ext x
    exact iff_of_true (hUW x.property) trivial
  letI : Nonempty ((q ⁻¹ᵁ U).ι ⁻¹ᵁ (q ⁻¹ᵁ W)) := by rw [hopen]; infer_instance
  have h := cartierPullback_mem_sections_on_open (q ⁻¹ᵁ U).ι E (q ⁻¹ᵁ W)
    ((dominantFunctionFieldMap q).hom z) hs
  have hfield : (dominantFunctionFieldMap (q ⁻¹ᵁ U).ι).hom
      ((dominantFunctionFieldMap q).hom z) =
      (dominantFunctionFieldMap (q ∣_ U)).hom ((dominantFunctionFieldMap U.ι).hom z) := by
    have hmaps : dominantFunctionFieldMap ((q ∣_ U) ≫ U.ι) =
        dominantFunctionFieldMap ((q ⁻¹ᵁ U).ι ≫ q) := by
      simp only [morphismRestrict_ι]
    rw [dominantFunctionFieldMap_comp, dominantFunctionFieldMap_comp] at hmaps
    exact (ConcreteCategory.congr_hom hmaps z).symm
  rw [hfield] at h
  have transport (V : (q ⁻¹ᵁ U).toScheme.Opens) (hV : Nonempty V)
      (hEq : (q ⁻¹ᵁ U).ι ⁻¹ᵁ (q ⁻¹ᵁ W) = V) :
      letI := hV
      (rationalFunctionsEquiv (X := (q ⁻¹ᵁ U).toScheme) V).symm
        ((dominantFunctionFieldMap (q ∣_ U)).hom ((dominantFunctionFieldMap U.ι).hom z)) ∈
          (cartierPullback (q ⁻¹ᵁ U).ι E).sections V := by
    subst V
    exact h
  exact transport ⊤ inferInstance hopen

end MixedFujita
