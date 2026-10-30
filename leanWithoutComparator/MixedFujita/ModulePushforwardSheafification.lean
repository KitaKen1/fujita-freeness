/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ModuleRestrictionTensorComparisons
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Restriction

/-!
Pushforward along an actual continuous and cocontinuous site functor commutes
with module sheafification, including an arbitrary coefficient-sheaf map.
The comparison is constructed from the actual sheafification unit; its
underlying additive presheaf map is the actual whiskered sheafification map.
Cocontinuity makes this locally bijective and the proved localization
criterion makes its sheafification an isomorphism. No coefficient-map
invertibility is needed for this commutation theorem.
For an actual scheme open immersion, the actual coefficient map and
restriction/sheafification comparison are constructed explicitly. This does
not yet identify the canonical tensor comparison induced by the separate
restriction/pushforward adjunction, or assert its invertibility.
-/

@[expose] public section
open CategoryTheory Opposite
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : C ⥤ D) [F.IsContinuous J K]
  {R : Sheaf K RingCat.{u}} {S : Sheaf J RingCat.{u}}
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]

noncomputable def modulePushforwardSheafificationUnit (P : PresheafOfModules.{u} R.obj) :
    (PresheafOfModules.pushforward (F := F) φ.hom).obj P ⟶
      ((SheafOfModules.pushforward (F := F) φ).obj
        ((PresheafOfModules.sheafification (𝟙 R.obj)).obj P)).val :=
  (PresheafOfModules.pushforward (F := F) φ.hom).map
    ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P)

theorem modulePushforwardSheafificationUnit_toPresheaf (P : PresheafOfModules.{u} R.obj) :
    (PresheafOfModules.toPresheaf _).map (modulePushforwardSheafificationUnit F φ P) =
      Functor.whiskerLeft F.op (CategoryTheory.toSheafify K P.presheaf) := by
  change Functor.whiskerLeft F.op
      ((PresheafOfModules.toPresheaf _).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P)) = _
  rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]

variable [F.IsCocontinuous J K] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

theorem modulePushforwardSheafificationUnit_isLocallyBijective
    (P : PresheafOfModules.{u} R.obj) :
    J.W ((PresheafOfModules.toPresheaf _).map
      (modulePushforwardSheafificationUnit F φ P)) := by
  rw [modulePushforwardSheafificationUnit_toPresheaf]
  exact (J.W_iff_isLocallyBijective _).mpr
    ⟨Presheaf.isLocallyInjective_whisker J K F _,
      Presheaf.isLocallySurjective_whisker J K F _⟩

variable [HasWeakSheafify J AddCommGrpCat.{u}]

theorem modulePushforwardSheafificationUnit_sheafification_isIso
    (P : PresheafOfModules.{u} R.obj) :
    IsIso ((PresheafOfModules.sheafification (𝟙 S.obj)).map
      (modulePushforwardSheafificationUnit F φ P)) := by
  change ((MorphismProperty.isomorphisms _).inverseImage
    (PresheafOfModules.sheafification (𝟙 S.obj)))
      (modulePushforwardSheafificationUnit F φ P)
  rw [← PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms]
  exact modulePushforwardSheafificationUnit_isLocallyBijective F φ P

noncomputable def modulePushforwardSheafificationIso
    (P : PresheafOfModules.{u} R.obj) :
    (SheafOfModules.pushforward (F := F) φ).obj
      ((PresheafOfModules.sheafification (𝟙 R.obj)).obj P) ≅
    (PresheafOfModules.sheafification (𝟙 S.obj)).obj
      ((PresheafOfModules.pushforward (F := F) φ.hom).obj P) := by
  let : IsIso ((PresheafOfModules.sheafification (𝟙 S.obj)).map
      (modulePushforwardSheafificationUnit F φ P)) :=
    modulePushforwardSheafificationUnit_sheafification_isIso F φ P
  exact (TauCeti.SheafOfModules.sheafificationIso S
      ((SheafOfModules.pushforward (F := F) φ).obj
        ((PresheafOfModules.sheafification (𝟙 R.obj)).obj P))).symm ≪≫
    (asIso ((PresheafOfModules.sheafification (𝟙 S.obj)).map
      (modulePushforwardSheafificationUnit F φ P))).symm

theorem modulePushforwardSheafificationIso_inv (P : PresheafOfModules.{u} R.obj) :
    (modulePushforwardSheafificationIso F φ P).inv =
      (PresheafOfModules.sheafification (𝟙 S.obj)).map
        (modulePushforwardSheafificationUnit F φ P) ≫
      (TauCeti.SheafOfModules.sheafificationIso S
        ((SheafOfModules.pushforward (F := F) φ).obj
          ((PresheafOfModules.sheafification (𝟙 R.obj)).obj P))).hom := by
  simp [modulePushforwardSheafificationIso]

omit [F.IsCocontinuous J K] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
theorem modulePushforwardSheafificationUnit_naturality
    {P Q : PresheafOfModules.{u} R.obj} (f : P ⟶ Q) :
    (PresheafOfModules.pushforward (F := F) φ.hom).map f ≫
      modulePushforwardSheafificationUnit F φ Q =
    modulePushforwardSheafificationUnit F φ P ≫
      ((SheafOfModules.pushforward (F := F) φ).map
        ((PresheafOfModules.sheafification (𝟙 R.obj)).map f)).val := by
  change (PresheafOfModules.pushforward (F := F) φ.hom).map f ≫
      (PresheafOfModules.pushforward (F := F) φ.hom).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app Q) =
    (PresheafOfModules.pushforward (F := F) φ.hom).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P) ≫
      (PresheafOfModules.pushforward (F := F) φ.hom).map
        ((PresheafOfModules.sheafification (𝟙 R.obj) ⋙
          SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).map f)
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (PresheafOfModules.pushforward (F := F) φ.hom).map
    ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.naturality f)

open AlgebraicGeometry TopologicalSpace
variable {X Y : Scheme.{u}}

noncomputable def moduleOpenRestrictionRingHom (f : X ⟶ Y) [IsOpenImmersion f] :
    X.ringCatSheaf ⟶ (f.opensFunctor.sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y)).obj Y.ringCatSheaf :=
  let α : X.presheaf ⟶ f.opensFunctor.op ⋙ Y.presheaf :=
    { app U := (f.appIso U.unop).inv }
  ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩

theorem moduleOpenRestrictionRingHom_pushforward (f : X ⟶ Y) [IsOpenImmersion f] :
    SheafOfModules.pushforward (F := f.opensFunctor) (moduleOpenRestrictionRingHom f) =
      Scheme.Modules.restrictFunctor f := rfl

noncomputable def moduleOpenRestrictionSheafificationIso
    (f : X ⟶ Y) [IsOpenImmersion f] (P : PresheafOfModules.{u} Y.ringCatSheaf.obj) :
    (Scheme.Modules.restrictFunctor f).obj
      ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj P) ≅
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
      ((PresheafOfModules.pushforward (F := f.opensFunctor)
        (moduleOpenRestrictionRingHom f).hom).obj P) :=
  modulePushforwardSheafificationIso f.opensFunctor (moduleOpenRestrictionRingHom f) P

end MixedFujita
