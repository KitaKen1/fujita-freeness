/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierGlobalPullback

/-!
Compute the actual adjunction-unit pullback on every open, its restriction
compatibility and naturality under module morphisms. Pulling back the
canonical structure module and using its isomorphism gives the actual
scheme map on regular functions. Thus a global module coefficient map
pulls back to the actual pulled regular coefficient, without assuming a
coefficient equality. The comparison for arbitrary local Cartier frames
uses the unit-compatible restriction isomorphism in ModulePullbackRestriction.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false

universe u

variable {X Y : Scheme.{u}}

noncomputable def modulePullbackSections (φ : Y ⟶ X) (M : X.Modules) (U : X.Opens) :
    Γ(M, U) →+ Γ((Scheme.Modules.pullback φ).obj M, φ ⁻¹ᵁ U) :=
  (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction φ).unit.app M) U).hom

theorem modulePullbackSections_apply (φ : Y ⟶ X) (M : X.Modules) (U : X.Opens)
    (s : Γ(M, U)) : modulePullbackSections φ M U s =
      Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction φ).unit.app M) U s := rfl

theorem modulePullbackSections_restrict (φ : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) (s : Γ(M, U)) :
    modulePullbackSections φ M V (M.presheaf.map i.op s) =
      ((Scheme.Modules.pullback φ).obj M).presheaf.map ((Opens.map φ.base).map i).op
        (modulePullbackSections φ M U s) := by
  exact ConcreteCategory.congr_hom
    (((Scheme.Modules.pullbackPushforwardAdjunction φ).unit.app M).mapPresheaf.naturality i.op) s

theorem modulePullbackSections_naturality (φ : Y ⟶ X) {M N : X.Modules}
    (a : M ⟶ N) (U : X.Opens) (s : Γ(M, U)) :
    modulePullbackSections φ N U (Scheme.Modules.Hom.app a U s) =
      Scheme.Modules.Hom.app ((Scheme.Modules.pullback φ).map a) (φ ⁻¹ᵁ U)
        (modulePullbackSections φ M U s) := by
  exact ConcreteCategory.congr_hom
    (congrArg (fun b => Scheme.Modules.Hom.app b U)
      ((Scheme.Modules.pullbackPushforwardAdjunction φ).unit.naturality a)) s

theorem modulePullbackSections_smul (φ : Y ⟶ X) (M : X.Modules) (U : X.Opens)
    (r : Γ(X, U)) (s : Γ(M, U)) :
    modulePullbackSections φ M U (r • s) =
      φ.app U r • modulePullbackSections φ M U s := by
  exact Scheme.Modules.Hom.app_smul
    ((Scheme.Modules.pullbackPushforwardAdjunction φ).unit.app M) r s

theorem modulePullbackGlobalSections_eq_top (φ : Y ⟶ X) (M : X.Modules) (s : Γ(M, ⊤)) :
    modulePullbackGlobalSections φ M s =
      ((Scheme.Modules.pullback φ).obj M).presheaf.map
        (eqToHom φ.preimage_top.symm).op (modulePullbackSections φ M ⊤ s) := rfl

theorem modulePullbackGlobalSections_restrict (φ : Y ⟶ X) (M : X.Modules)
    (U : X.Opens) (s : Γ(M, ⊤)) :
    ((Scheme.Modules.pullback φ).obj M).presheaf.map (homOfLE le_top : φ ⁻¹ᵁ U ⟶ ⊤).op
      (modulePullbackGlobalSections φ M s) =
        modulePullbackSections φ M U (M.presheaf.map (homOfLE le_top : U ⟶ ⊤).op s) := by
  rw [modulePullbackGlobalSections_eq_top, modulePullbackSections_restrict]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

theorem modulePullbackGlobalSections_naturality (φ : Y ⟶ X) {M N : X.Modules}
    (a : M ⟶ N) (s : Γ(M, ⊤)) :
    modulePullbackGlobalSections φ N (Scheme.Modules.Hom.app a ⊤ s) =
      Scheme.Modules.Hom.app ((Scheme.Modules.pullback φ).map a) ⊤
        (modulePullbackGlobalSections φ M s) := by
  rw [modulePullbackGlobalSections_eq_top, modulePullbackGlobalSections_eq_top,
    modulePullbackSections_naturality]
  exact (ConcreteCategory.congr_hom
    (((Scheme.Modules.pullback φ).map a).mapPresheaf.naturality
      (eqToHom φ.preimage_top.symm).op) _).symm

noncomputable def modulePullbackCoefficientHom (φ : Y ⟶ X) {M : X.Modules}
    (c : M ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (Scheme.Modules.pullback φ).obj M ⟶ SheafOfModules.unit Y.ringCatSheaf :=
  (Scheme.Modules.pullback φ).map c ≫ (Scheme.Modules.pullbackObjUnitIso φ).hom

theorem modulePullbackSections_unit_coefficient (φ : Y ⟶ X) (U : X.Opens) (r : Γ(X, U)) :
    Scheme.Modules.Hom.app (Scheme.Modules.pullbackObjUnitIso φ).hom (φ ⁻¹ᵁ U)
      (modulePullbackSections φ (SheafOfModules.unit X.ringCatSheaf) U r) = φ.app U r := by
  have h := Scheme.Modules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom φ
  rw [Adjunction.homEquiv_unit] at h
  exact ConcreteCategory.congr_hom
    (congrArg (fun b => Scheme.Modules.Hom.app b U) h) r

theorem modulePullbackSections_coefficient (φ : Y ⟶ X) {M : X.Modules}
    (c : M ⟶ SheafOfModules.unit X.ringCatSheaf) (U : X.Opens) (s : Γ(M, U)) :
    Scheme.Modules.Hom.app (modulePullbackCoefficientHom φ c) (φ ⁻¹ᵁ U)
      (modulePullbackSections φ M U s) = φ.app U (Scheme.Modules.Hom.app c U s) := by
  change Scheme.Modules.Hom.app (Scheme.Modules.pullbackObjUnitIso φ).hom (φ ⁻¹ᵁ U)
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullback φ).map c) (φ ⁻¹ᵁ U)
      (modulePullbackSections φ M U s)) = _
  rw [← modulePullbackSections_naturality, modulePullbackSections_unit_coefficient]

noncomputable def modulePullbackFrameIso (φ : Y ⟶ X) {M : X.Modules}
    (e : M ≅ SheafOfModules.unit X.ringCatSheaf) :
    (Scheme.Modules.pullback φ).obj M ≅ SheafOfModules.unit Y.ringCatSheaf :=
  (Scheme.Modules.pullback φ).mapIso e ≪≫ Scheme.Modules.pullbackObjUnitIso φ

theorem modulePullbackFrameIso_hom (φ : Y ⟶ X) {M : X.Modules}
    (e : M ≅ SheafOfModules.unit X.ringCatSheaf) :
    (modulePullbackFrameIso φ e).hom = modulePullbackCoefficientHom φ e.hom := rfl

theorem modulePullbackSections_frame_coefficient (φ : Y ⟶ X) {M : X.Modules}
    (e : M ≅ SheafOfModules.unit X.ringCatSheaf) (U : X.Opens) (s : Γ(M, U)) :
    Scheme.Modules.Hom.app (modulePullbackFrameIso φ e).hom (φ ⁻¹ᵁ U)
      (modulePullbackSections φ M U s) = φ.app U (Scheme.Modules.Hom.app e.hom U s) := by
  exact modulePullbackSections_coefficient φ e.hom U s

end MixedFujita
