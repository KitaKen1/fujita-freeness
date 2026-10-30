/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.IsomorphismLocusOpens
public import MixedFujita.EffectiveCartierPushforwardUnit
public import MixedFujita.ModulePushforwardTensorComparisons
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-! If the exceptional direct image is the structure module on the original base,
it is the structure module on the isomorphism locus of a modified base. The
actual canonical unit morphism is an isomorphism there, on every subopen including
the empty open. This does not assert the same identity on the whole modified base. -/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- The actual effective-Cartier unit morphisms compose on actual sections. -/
theorem effectiveCartierPushforwardUnitMap_comp_app
    {T B Y : Scheme.{u}} [IsIntegral T] [IsIntegral B] [IsIntegral Y]
    (q : T ⟶ B) (ρ : B ⟶ Y) (E : CartierDivisor T) (hE : E.IsEffective)
    (V : Y.Opens) (a : Γ(Y, V)) :
    Scheme.Modules.Hom.app (effectiveCartierPushforwardUnitMap (q ≫ ρ) E hE) V a =
      Scheme.Modules.Hom.app (effectiveCartierPushforwardUnitMap q E hE) (ρ ⁻¹ᵁ V)
        ((ρ.app V).hom a) := by
  simp only [effectiveCartierPushforwardUnitMap_app, Scheme.Hom.comp_app, CommRingCat.comp_apply]
  rfl

/-- Isomorphisms on all subopens give an actual isomorphism of restricted module sheaves. -/
theorem moduleHom_over_isIso_of_app_isIso {B : Scheme.{u}} {M N : B.Modules}
    (f : M ⟶ N) (U : B.Opens) (h : ∀ V : B.Opens, V ≤ U → IsIso (f.app V)) :
    IsIso (f.over U) := by
  apply (isIso_iff_of_reflects_iso (f.over U) (SheafOfModules.forget _)).mp
  apply modulePresheafHom_isIso_of_app_isIso
  intro V
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  change Function.Bijective (f.app V.unop.left)
  letI := h V.unop.left V.unop.hom.le
  exact ConcreteCategory.bijective_of_isIso (f.app V.unop.left)

variable {T B Y : Scheme.{u}} [IsIntegral T] [IsIntegral B] [IsIntegral Y]
  (q : T ⟶ B) (ρ : B ⟶ Y) (E : CartierDivisor T) (hE : E.IsEffective)
  (W : Y.Opens) [IsIso (ρ ∣_ W)]
  [IsIso (effectiveCartierPushforwardUnitMap (q ≫ ρ) E hE)]

/-- On the modified base's actual isomorphism locus every section of the same
exceptional Cartier sheaf descends uniquely through the canonical unit morphism. -/
theorem exceptional_modified_base_unit_app_isIso
    (U : B.Opens) (hU : U ≤ ρ ⁻¹ᵁ W) :
    IsIso (Scheme.Modules.Hom.app (effectiveCartierPushforwardUnitMap q E hE) U) := by
  obtain ⟨V, hVW, rfl, hρapp⟩ := exists_base_open_of_subset_isomorphism_locus ρ W U hU
  have hρbij := ConcreteCategory.bijective_of_isIso (ρ.app V)
  have hcomp := ConcreteCategory.bijective_of_isIso
    (Scheme.Modules.Hom.app (effectiveCartierPushforwardUnitMap (q ≫ ρ) E hE) V)
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro a b hab
    obtain ⟨a', rfl⟩ := hρbij.2 a
    obtain ⟨b', rfl⟩ := hρbij.2 b
    apply congrArg (ρ.app V).hom
    apply hcomp.1
    simpa only [effectiveCartierPushforwardUnitMap_comp_app] using hab
  · intro s
    obtain ⟨a, ha⟩ := hcomp.2 s
    refine ⟨(ρ.app V).hom a, ?_⟩
    simpa only [effectiveCartierPushforwardUnitMap_comp_app] using ha

/-- The canonical exceptional direct-image morphism is an actual sheaf isomorphism
on the full inverse image of the original-base isomorphism locus. -/
theorem exceptional_modified_base_unit_over_isIso :
    IsIso ((effectiveCartierPushforwardUnitMap q E hE).over (ρ ⁻¹ᵁ W)) := by
  apply moduleHom_over_isIso_of_app_isIso
  exact exceptional_modified_base_unit_app_isIso q ρ E hE W

/-- The actual rank-one frame on the same modified-base open. -/
noncomputable def exceptionalModifiedBaseUnitOverIso :
    SheafOfModules.unit (B.ringCatSheaf.over (ρ ⁻¹ᵁ W)) ≅
      ((Scheme.Modules.pushforward q).obj E.sheaf).over (ρ ⁻¹ᵁ W) := by
  letI := exceptional_modified_base_unit_over_isIso q ρ E hE W
  exact asIso ((effectiveCartierPushforwardUnitMap q E hE).over (ρ ⁻¹ᵁ W))

end MixedFujita
