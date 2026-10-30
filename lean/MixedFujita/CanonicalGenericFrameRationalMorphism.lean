/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.GenericFrameRationalSectionDescent
public import TauCeti.AlgebraicGeometry.Modules.RationalEmbedding

/-! Assemble the checked unique actual rational descent into a genuine
module-sheaf morphism. Its linearity and naturality are forced by the actual
injective base function-field map and the source Cartier inclusion. -/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {T B : Scheme.{u}} [IsIntegral T] [IsIntegral B]
  (q : T ⟶ B) [IsDominant q] (E : CartierDivisor T) (heff : E.IsEffective)
  (F : B.Opens) (hgenF : genericPoint B ∈ F)
  [IsIso ((effectiveCartierPushforwardUnitMap q E heff).over F)]

/-- The unique actual descended base rational function of a source section. -/
noncomputable def canonicalRoundupRationalValue
    (U : B.Opens) [Nonempty U] (s : Γ(E.sheaf, q ⁻¹ᵁ U)) : B.functionField :=
  Classical.choose
    (cartier_direct_image_section_descends_of_generic_unit_frame q E heff F hgenF U s)

/-- The descended function retains the actual source rational section. -/
theorem canonicalRoundupRationalValue_spec
    (U : B.Opens) [Nonempty U] (s : Γ(E.sheaf, q ⁻¹ᵁ U)) :
    letI := dominant_preimage_nonempty q U
    (dominantFunctionFieldMap q).hom (canonicalRoundupRationalValue q E heff F hgenF U s) =
      rationalFunctionsEquiv (X := T) (q ⁻¹ᵁ U)
        (Scheme.Modules.Hom.app E.sheafι (q ⁻¹ᵁ U) s) :=
  (Classical.choose_spec
    (cartier_direct_image_section_descends_of_generic_unit_frame q E heff F hgenF U s)).1

/-- Actual unique rational descent assembles into a linear natural morphism
on every open. Empty opens use the rational-function sheaf's zero section. -/
noncomputable def canonicalRoundupRationalHom :
    (Scheme.Modules.pushforward q).obj E.sheaf ⟶ Scheme.rationalFunctions B := by
  classical
  let M := (Scheme.Modules.pushforward q).obj E.sheaf
  let value (U : B.Opens) [Nonempty U] (s : Γ(M, U)) :=
    canonicalRoundupRationalValue q E heff F hgenF U s
  have hadd (U : B.Opens) [Nonempty U] (s t : Γ(M, U)) :
      value U (s + t) = value U s + value U t := by
    letI := dominant_preimage_nonempty q U
    apply (dominantFunctionFieldMap q).hom.injective
    simp only [value, map_add, canonicalRoundupRationalValue_spec]
  have hsmul (U : B.Opens) [Nonempty U] (a : Γ(B, U)) (s : Γ(M, U)) :
      value U (a • s) = a • value U s := by
    letI := dominant_preimage_nonempty q U
    apply (dominantFunctionFieldMap q).hom.injective
    rw [canonicalRoundupRationalValue_spec]
    change rationalFunctionsEquiv (X := T) (q ⁻¹ᵁ U)
      (Scheme.Modules.Hom.app E.sheafι (q ⁻¹ᵁ U)
        (((q.app U).hom a) • (id s : Γ(E.sheaf, q ⁻¹ᵁ U)))) =
        (dominantFunctionFieldMap q).hom (B.germToFunctionField U a * value U s)
    rw [Scheme.Modules.Hom.app_smul, LinearEquiv.map_smul, map_mul,
      canonicalRoundupRationalValue_spec]
    change T.germToFunctionField (q ⁻¹ᵁ U) ((q.app U).hom a) * _ =
      (dominantFunctionFieldMap q).hom (B.germToFunctionField U a) * _
    congr 1
    simpa only [Scheme.Hom.appLE_eq_app] using
      (dominantFunctionFieldMap_germ q U (q ⁻¹ᵁ U) le_rfl a).symm
  have hmap {U V : B.Opens} [Nonempty U] [Nonempty V]
      (i : V ⟶ U) (s : Γ(M, U)) :
      value V (M.presheaf.map i.op s) = value U s := by
    letI := dominant_preimage_nonempty q U
    letI := dominant_preimage_nonempty q V
    apply (dominantFunctionFieldMap q).hom.injective
    rw [canonicalRoundupRationalValue_spec, canonicalRoundupRationalValue_spec]
    let j : (q ⁻¹ᵁ V) ⟶ (q ⁻¹ᵁ U) := homOfLE (fun _ hx => i.le hx)
    have hres := ConcreteCategory.congr_hom (E.sheafι.mapPresheaf.naturality j.op) s
    change Scheme.Modules.Hom.app E.sheafι (q ⁻¹ᵁ V)
      (E.sheaf.presheaf.map j.op s) = (Scheme.rationalFunctions T).presheaf.map j.op
        (Scheme.Modules.Hom.app E.sheafι (q ⁻¹ᵁ U) s) at hres
    change rationalFunctionsEquiv (X := T) (q ⁻¹ᵁ V)
      (Scheme.Modules.Hom.app E.sheafι (q ⁻¹ᵁ V) (E.sheaf.presheaf.map j.op s)) = _
    rw [hres, Scheme.rationalFunctionsEquiv_map]
  let app (U : B.Opens) [Nonempty U] :
      M.val.obj (op U) ⟶ (Scheme.rationalFunctions B).val.obj (op U) :=
    { hom' :=
        { toFun := fun s => (rationalFunctionsEquiv (X := B) U).symm (value U s)
          map_add' := fun s t => by rw [hadd, map_add]
          map_smul' := fun a s => by rw [hsmul, map_smul]; rfl } }
  have happ {U V : B.Opens} [Nonempty U] [Nonempty V]
      (i : V ⟶ U) (s : Γ(M, U)) :
      app V (M.presheaf.map i.op s) =
        (Scheme.rationalFunctions B).presheaf.map i.op (app U s) := by
    apply (rationalFunctionsEquiv (X := B) V).injective
    change rationalFunctionsEquiv (X := B) V
        ((rationalFunctionsEquiv (X := B) V).symm (value V (M.presheaf.map i.op s))) =
      rationalFunctionsEquiv (X := B) V
        ((Scheme.rationalFunctions B).presheaf.map i.op
          ((rationalFunctionsEquiv (X := B) U).symm (value U s)))
    rw [LinearEquiv.apply_symm_apply, Scheme.rationalFunctionsEquiv_map,
      LinearEquiv.apply_symm_apply, hmap]
  exact
    { val :=
      { app := fun U => if hU : Nonempty U.unop then
          letI := hU
          app U.unop
        else 0
        naturality := fun {U V} i => by
          by_cases hV : Nonempty V.unop
          · letI := hV
            let x : V.unop := Classical.choice hV
            have hU : Nonempty U.unop := ⟨⟨x.1, i.unop.le x.2⟩⟩
            letI := hU
            simp only [dite_eq_left hV, dite_eq_left hU]
            ext s
            exact happ i.unop s
          · have hbot : V.unop = ⊥ := (Opens.not_nonempty_iff_eq_bot V.unop).mp
              (fun ⟨x, hx⟩ => hV ⟨⟨x, hx⟩⟩)
            letI : Subsingleton
                ((ModuleCat.restrictScalars (B.ringCatSheaf.obj.map i).hom).obj
                  ((Scheme.rationalFunctions B).val.obj V)) :=
              ⟨fun a b => (Scheme.subsingleton_rationalFunctions V.unop hbot).elim a b⟩
            ext s
            exact Subsingleton.elim _ _ } }

theorem canonicalRoundupRationalHom_field_pullback
    (U : B.Opens) [Nonempty U] (s : Γ(E.sheaf, q ⁻¹ᵁ U)) :
    letI := dominant_preimage_nonempty q U
    (dominantFunctionFieldMap q).hom
      (rationalFunctionsEquiv (X := B) U
        (Scheme.Modules.Hom.app (canonicalRoundupRationalHom q E heff F hgenF) U s)) =
      rationalFunctionsEquiv (X := T) (q ⁻¹ᵁ U)
        (Scheme.Modules.Hom.app E.sheafι (q ⁻¹ᵁ U) s) := by
  letI := dominant_preimage_nonempty q U
  simp only [canonicalRoundupRationalHom, Scheme.Modules.Hom.app,
    dite_eq_left (inferInstance : Nonempty U)]
  change (dominantFunctionFieldMap q).hom
    (rationalFunctionsEquiv (X := B) U
      ((rationalFunctionsEquiv (X := B) U).symm
        (canonicalRoundupRationalValue q E heff F hgenF U s))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact canonicalRoundupRationalValue_spec q E heff F hgenF U s

theorem canonicalRoundupRationalHom_app_injective (U : B.Opens) :
    Function.Injective
      (Scheme.Modules.Hom.app (canonicalRoundupRationalHom q E heff F hgenF) U) := by
  classical
  intro s t h
  by_cases hU : Nonempty U
  · letI := hU
    letI := dominant_preimage_nonempty q U
    apply E.sheafι_app_injective (q ⁻¹ᵁ U)
    apply (rationalFunctionsEquiv (X := T) (q ⁻¹ᵁ U)).injective
    rw [← canonicalRoundupRationalHom_field_pullback q E heff F hgenF U s,
      ← canonicalRoundupRationalHom_field_pullback q E heff F hgenF U t, h]
  · let M := (Scheme.Modules.pushforward q).obj E.sheaf
    exact TopCat.Presheaf.section_ext ⟨M.presheaf, M.isSheaf⟩ U s t
      (fun x hx => (hU ⟨⟨x, hx⟩⟩).elim)

theorem canonicalRoundupRationalHom_mono :
    Mono (canonicalRoundupRationalHom q E heff F hgenF) :=
  (SheafOfModules.forget _).mono_of_mono_map
    (PresheafOfModules.mono_of_injective (fun U =>
      canonicalRoundupRationalHom_app_injective q E heff F hgenF U.unop))

end MixedFujita
