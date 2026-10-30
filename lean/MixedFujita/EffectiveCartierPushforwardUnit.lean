/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ExceptionalCartierRegularFunctions
public import MixedFujita.ClosedEmbeddingSheafExactness

/-!
The actual canonical morphism O_X -> p_* O_T(E) for an effective Cartier
divisor E. Its formula in rational functions turns the actual all-open section
criterion into an isomorphism of module sheaves, including the empty open.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- The effective Cartier inclusion is the actual regular-function inclusion
when viewed in the function field of any nonempty open. -/
theorem effectiveCartierUnitToSheaf_rational {T : Scheme.{u}} [IsIntegral T]
    (E : CartierDivisor T) (hE : E.IsEffective) (W : T.Opens) [Nonempty W]
    (a : Γ(T, W)) :
    rationalFunctionsEquiv (X := T) W
      (Scheme.Modules.Hom.app E.sheafι W (Scheme.Modules.Hom.app (E.unitToSheaf hE) W a)) =
      T.germToFunctionField W a := by
  have h : Scheme.Modules.Hom.app E.sheafι W
      (Scheme.Modules.Hom.app (E.unitToSheaf hE) W a) =
      Scheme.Modules.Hom.app (toRationalFunctions T) W a := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, E.unitToSheaf_ι]
  rw [h, rationalFunctionsEquiv_toRationalFunctions_app]

variable {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]

/-- The canonical morphism from regular functions to the direct image of O(E). -/
noncomputable def effectiveCartierPushforwardUnitMap (p : T ⟶ X)
    (E : CartierDivisor T) (hE : E.IsEffective) :
    SheafOfModules.unit X.ringCatSheaf ⟶ (Scheme.Modules.pushforward p).obj E.sheaf :=
  SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom ≫
    (Scheme.Modules.pushforward p).map (E.unitToSheaf hE)

/-- On actual sections the canonical map pulls back regular functions and then
uses the standard effective-Cartier inclusion. -/
theorem effectiveCartierPushforwardUnitMap_app (p : T ⟶ X)
    (E : CartierDivisor T) (hE : E.IsEffective) (U : X.Opens) (a : Γ(X, U)) :
    Scheme.Modules.Hom.app (effectiveCartierPushforwardUnitMap p E hE) U a =
      Scheme.Modules.Hom.app (E.unitToSheaf hE) (p ⁻¹ᵁ U) ((p.app U).hom a) := rfl

/-- The canonical pushforward morphism has the actual function-field pullback formula. -/
theorem effectiveCartierPushforwardUnitMap_rational (p : T ⟶ X) [IsDominant p]
    (E : CartierDivisor T) (hE : E.IsEffective) (U : X.Opens) [Nonempty U]
    (a : Γ(X, U)) :
    letI := dominant_preimage_nonempty p U
    rationalFunctionsEquiv (X := T) (p ⁻¹ᵁ U)
      (Scheme.Modules.Hom.app E.sheafι (p ⁻¹ᵁ U)
        (Scheme.Modules.Hom.app (effectiveCartierPushforwardUnitMap p E hE) U a)) =
      (dominantFunctionFieldMap p).hom (X.germToFunctionField U a) := by
  haveI := dominant_preimage_nonempty p U
  rw [effectiveCartierPushforwardUnitMap_app, effectiveCartierUnitToSheaf_rational]
  simpa only [Scheme.Hom.appLE_eq_app] using
    (dominantFunctionFieldMap_germ p U (p ⁻¹ᵁ U) le_rfl a).symm

/-- Unique descent of actual sections on every nonempty open makes the
canonical map an isomorphism of module sheaves. Empty opens are handled by
the sheaf axiom, rather than by an extra nonemptiness assumption. -/
theorem effectiveCartierPushforwardUnitMap_isIso_of_section_criterion
    (p : T ⟶ X) [IsDominant p] (E : CartierDivisor T) (hE : E.IsEffective)
    (hsections : ∀ (U : X.Opens) [Nonempty U] (z : T.functionField),
      letI := dominant_preimage_nonempty p U
      (rationalFunctionsEquiv (X := T) (p ⁻¹ᵁ U)).symm z ∈ E.sections (p ⁻¹ᵁ U) ↔
      ∃! a : Γ(X, U), (dominantFunctionFieldMap p).hom (X.germToFunctionField U a) = z) :
    IsIso (effectiveCartierPushforwardUnitMap p E hE) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  rcases isEmpty_or_nonempty U with hU | hU
  · have hbot : U = ⊥ := Opens.coe_eq_empty.mp (Set.isEmpty_coe_sort.mp hU)
    haveI : Subsingleton Γ(SheafOfModules.unit X.ringCatSheaf, U) :=
      abelianSheaf_empty_sections_subsingleton
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj (SheafOfModules.unit X.ringCatSheaf)) hbot
    haveI : Subsingleton Γ((Scheme.Modules.pushforward p).obj E.sheaf, U) :=
      abelianSheaf_empty_sections_subsingleton
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj ((Scheme.Modules.pushforward p).obj E.sheaf)) hbot
    exact ⟨fun a b _ => Subsingleton.elim a b, fun b => ⟨0, Subsingleton.elim _ _⟩⟩
  · haveI := dominant_preimage_nonempty p U
    constructor
    · intro a b hab
      apply X.germToFunctionField_injective U
      apply (dominantFunctionFieldMap p).hom.injective
      have h := congrArg (fun s : Γ((Scheme.Modules.pushforward p).obj E.sheaf, U) =>
        rationalFunctionsEquiv (X := T) (p ⁻¹ᵁ U)
          (Scheme.Modules.Hom.app E.sheafι (p ⁻¹ᵁ U) s)) hab
      simpa only [effectiveCartierPushforwardUnitMap_rational] using h
    · intro s
      let z := rationalFunctionsEquiv (X := T) (p ⁻¹ᵁ U)
        (Scheme.Modules.Hom.app E.sheafι (p ⁻¹ᵁ U) s)
      have hs : (rationalFunctionsEquiv (X := T) (p ⁻¹ᵁ U)).symm z ∈
          E.sections (p ⁻¹ᵁ U) := by
        simpa only [z, LinearEquiv.symm_apply_apply] using E.sheafι_app_mem (p ⁻¹ᵁ U) s
      obtain ⟨a, ha, -⟩ := (hsections U z).mp hs
      refine ⟨a, ?_⟩
      apply E.sheafι_app_injective (p ⁻¹ᵁ U)
      apply (rationalFunctionsEquiv (X := T) (p ⁻¹ᵁ U)).injective
      rw [effectiveCartierPushforwardUnitMap_rational]
      exact ha

end MixedFujita
