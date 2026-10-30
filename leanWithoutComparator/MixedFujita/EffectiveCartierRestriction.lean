/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.EffectiveCartierInclusion

/-!
Restrict the inclusion O(-D) -> O_X to an actual open subscheme Y.
Its target is the structure module of Y, using Mathlib's restrictUnitIso.
This does not construct a Cartier divisor on a nonintegral base change.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

variable (X : Scheme.{u}) [IsIntegral X]

noncomputable def negativeCartierToOpenUnit
    (D : CartierDivisor X) (hD : D.IsEffective)
    {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] :
    (-D).sheaf.restrict j ⟶ SheafOfModules.unit Y.ringCatSheaf :=
  (Scheme.Modules.restrictFunctor j).map (negativeCartierToUnit X D hD) ≫
    (Scheme.Modules.restrictUnitIso j).hom

theorem negativeCartierToOpenUnit_app
    (D : CartierDivisor X) (hD : D.IsEffective)
    {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] (U : Y.Opens)
    (s : Γ((-D).sheaf.restrict j, U)) :
    Scheme.Modules.Hom.app (negativeCartierToOpenUnit X D hD j) U s =
      (j.appIso U).hom (Scheme.Modules.Hom.app (negativeCartierToUnit X D hD)
        (j ''ᵁ U) (((-D).sheaf.restrictAppIso j U).hom s)) := rfl

theorem negativeCartierToOpenUnit_app_injective
    (D : CartierDivisor X) (hD : D.IsEffective)
    {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] (U : Y.Opens) :
    Function.Injective (Scheme.Modules.Hom.app (negativeCartierToOpenUnit X D hD j) U) := by
  intro s t h
  rw [negativeCartierToOpenUnit_app, negativeCartierToOpenUnit_app] at h
  have h' := (ConcreteCategory.bijective_of_isIso (j.appIso U).hom).1 h
  have h'' := negativeCartierToUnit_app_injective X D hD (j ''ᵁ U) h'
  exact (ConcreteCategory.bijective_of_isIso ((-D).sheaf.restrictAppIso j U).hom).1 h''

theorem negativeCartierToOpenUnit_mono
    (D : CartierDivisor X) (hD : D.IsEffective)
    {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] :
    Mono (negativeCartierToOpenUnit X D hD j) := by
  apply (SheafOfModules.forget _).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro U
  exact negativeCartierToOpenUnit_app_injective X D hD j U.unop

attribute [instance] negativeCartierToOpenUnit_mono

theorem negativeCartierToOpenUnit_range_iff
    (D : CartierDivisor X) (hD : D.IsEffective)
    {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] (U : Y.Opens)
    (a : Γ(Y, U)) :
    a ∈ Set.range (Scheme.Modules.Hom.app (negativeCartierToOpenUnit X D hD j) U) ↔
      Scheme.Modules.Hom.app (toRationalFunctions X) (j ''ᵁ U)
        ((j.appIso U).inv a) ∈ (-D).sections (j ''ᵁ U) := by
  rw [← negativeCartierToUnit_range_iff X D hD]
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨((-D).sheaf.restrictAppIso j U).hom s, ?_⟩
    rw [negativeCartierToOpenUnit_app]
    simp
  · rintro ⟨s, hs⟩
    refine ⟨((-D).sheaf.restrictAppIso j U).inv s, ?_⟩
    rw [negativeCartierToOpenUnit_app]
    simp only [Iso.inv_hom_id_apply]
    rw [hs]
    simp

end MixedFujita
