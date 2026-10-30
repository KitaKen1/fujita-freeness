/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ExceptionalGenericDirectImage

/-!
An actual canonical unit frame on a generic base open forces every actual
Cartier direct-image section over any nonempty base open to be a unique
rational base function. Restrict to the intersection with the frame open and
use the actual unit map's function-field formula. This is rational descent,
not a claim that the rational base function is regular on the original open.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {T B : Scheme.{u}} [IsIntegral T] [IsIntegral B]

/-- Surjectivity of the canonical unit map on subopens of one generic open
puts every rational Cartier section in the actual base function-field image. -/
theorem cartier_rational_section_descends_of_generic_unit_frame
    (q : T ⟶ B) [IsDominant q] (E : CartierDivisor T) (heff : E.IsEffective)
    (W : B.Opens) (hgenW : genericPoint B ∈ W)
    [IsIso ((effectiveCartierPushforwardUnitMap q E heff).over W)]
    (U : B.Opens) [Nonempty U] (z : T.functionField)
    (hs : letI := dominant_preimage_nonempty q U
      (rationalFunctionsEquiv (X := T) (q ⁻¹ᵁ U)).symm z ∈ E.sections (q ⁻¹ᵁ U)) :
    ∃! r : B.functionField, (dominantFunctionFieldMap q).hom r = z := by
  letI := dominant_preimage_nonempty q U
  obtain ⟨b⟩ := (inferInstance : Nonempty U)
  have hgenU : genericPoint B ∈ U :=
    (genericPoint_specializes b.1).mem_open U.isOpen b.property
  let V : B.Opens := U ⊓ W
  letI : Nonempty V := ⟨⟨genericPoint B, hgenU, hgenW⟩⟩
  letI := dominant_preimage_nonempty q V
  have hsV : (rationalFunctionsEquiv (X := T) (q ⁻¹ᵁ V)).symm z ∈ E.sections (q ⁻¹ᵁ V) := by
    apply CartierDivisor.mem_sections.mpr
    intro t ht f hf
    have h := (CartierDivisor.mem_sections.mp hs) t ht.1 f hf
    simpa only [LinearEquiv.apply_symm_apply] using h
  have hframe : Function.Surjective
      (Scheme.Modules.Hom.app (effectiveCartierPushforwardUnitMap q E heff) V) := by
    have h := ConcreteCategory.bijective_of_isIso
      ((PresheafOfModules.evaluation _
        (op (Over.mk (homOfLE (show V ≤ W from inf_le_right))))).map
          ((SheafOfModules.forget _).map ((effectiveCartierPushforwardUnitMap q E heff).over W)))
    exact h.2
  obtain ⟨a, ha⟩ := hframe
    (CartierDivisor.sectionMk ((rationalFunctionsEquiv (X := T) (q ⁻¹ᵁ V)).symm z) hsV)
  have hrat := effectiveCartierPushforwardUnitMap_rational q E heff V a
  rw [ha, CartierDivisor.sheafι_app_sectionMk, LinearEquiv.apply_symm_apply] at hrat
  refine ⟨B.germToFunctionField V a, hrat.symm, ?_⟩
  intro r hr
  exact (dominantFunctionFieldMap q).hom.injective (hr.trans hrat)

/-- Every actual direct-image section descends uniquely as a rational base
function when the canonical unit frame is supplied on one generic open. -/
theorem cartier_direct_image_section_descends_of_generic_unit_frame
    (q : T ⟶ B) [IsDominant q] (E : CartierDivisor T) (heff : E.IsEffective)
    (W : B.Opens) (hgenW : genericPoint B ∈ W)
    [IsIso ((effectiveCartierPushforwardUnitMap q E heff).over W)]
    (U : B.Opens) [Nonempty U] (s : Γ(E.sheaf, q ⁻¹ᵁ U)) :
    letI := dominant_preimage_nonempty q U
    ∃! r : B.functionField, (dominantFunctionFieldMap q).hom r =
      rationalFunctionsEquiv (X := T) (q ⁻¹ᵁ U)
        (Scheme.Modules.Hom.app E.sheafι (q ⁻¹ᵁ U) s) := by
  letI := dominant_preimage_nonempty q U
  apply cartier_rational_section_descends_of_generic_unit_frame q E heff W hgenW U
  simpa only [LinearEquiv.symm_apply_apply] using E.sheafι_app_mem (q ⁻¹ᵁ U) s

/-- Apply rational descent to the actual generic unit frame already constructed
on a modified base; no new rational-image hypothesis is supplied. -/
theorem exceptional_modified_base_direct_image_section_rational_descent
    {Y : Scheme.{u}} [IsIntegral Y]
    (q : T ⟶ B) [IsDominant q] (ρ : B ⟶ Y)
    (E : CartierDivisor T) (heff : E.IsEffective)
    (W : Y.Opens) (hgen : genericPoint B ∈ ρ ⁻¹ᵁ W)
    [IsIso (ρ ∣_ W)] [IsIso (effectiveCartierPushforwardUnitMap (q ≫ ρ) E heff)]
    (U : B.Opens) [Nonempty U] (s : Γ(E.sheaf, q ⁻¹ᵁ U)) :
    letI := dominant_preimage_nonempty q U
    ∃! r : B.functionField, (dominantFunctionFieldMap q).hom r =
      rationalFunctionsEquiv (X := T) (q ⁻¹ᵁ U)
        (Scheme.Modules.Hom.app E.sheafι (q ⁻¹ᵁ U) s) := by
  letI := exceptional_modified_base_unit_over_isIso q ρ E heff W
  exact cartier_direct_image_section_descends_of_generic_unit_frame q E heff (ρ ⁻¹ᵁ W) hgen U s

end MixedFujita
