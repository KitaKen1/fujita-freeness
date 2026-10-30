/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ModulePullbackSections

/-!
Construct the actual pullback/restriction comparison using uniqueness of
left adjoints. Its unit compatibility is proved by the uniqueness theorem,
so later computations of local coefficients do not need to assume that
compatibility or unfold five separate pseudofunctor isomorphisms. Both
sides are actual sheaves of modules on the actual preimage open scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false

universe u

variable {X Y : Scheme.{u}}

noncomputable def modulePullbackRestrictionPushforwardIso (φ : Y ⟶ X) (U : X.Opens) :
    Scheme.Modules.pushforward (φ ⁻¹ᵁ U).ι ⋙ Scheme.Modules.pushforward φ ≅
      Scheme.Modules.pushforward (φ ∣_ U) ⋙ Scheme.Modules.pushforward U.ι :=
  Scheme.Modules.pushforwardComp (φ ⁻¹ᵁ U).ι φ ≪≫
    Scheme.Modules.pushforwardCongr (morphismRestrict_ι φ U).symm ≪≫
      (Scheme.Modules.pushforwardComp (φ ∣_ U) U.ι).symm

noncomputable def modulePullbackRestrictionAdjunction (φ : Y ⟶ X) (U : X.Opens) :
    Scheme.Modules.pullback φ ⋙ Scheme.Modules.restrictFunctor (φ ⁻¹ᵁ U).ι ⊣
      Scheme.Modules.pushforward (φ ∣_ U) ⋙ Scheme.Modules.pushforward U.ι :=
  ((Scheme.Modules.pullbackPushforwardAdjunction φ).comp
    (Scheme.Modules.restrictAdjunction (φ ⁻¹ᵁ U).ι)).ofNatIsoRight
      (modulePullbackRestrictionPushforwardIso φ U)

noncomputable def modulePullbackRestrictionIso (φ : Y ⟶ X) (U : X.Opens) (M : X.Modules) :
    ((Scheme.Modules.pullback φ).obj M).restrict (φ ⁻¹ᵁ U).ι ≅
      (Scheme.Modules.pullback (φ ∣_ U)).obj (M.restrict U.ι) :=
  ((modulePullbackRestrictionAdjunction φ U).leftAdjointUniq
    ((Scheme.Modules.restrictAdjunction U.ι).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (φ ∣_ U)))).app M

theorem modulePullbackRestrictionIso_unit (φ : Y ⟶ X) (U : X.Opens) (M : X.Modules) :
    (modulePullbackRestrictionAdjunction φ U).unit.app M ≫
      (Scheme.Modules.pushforward U.ι).map
        ((Scheme.Modules.pushforward (φ ∣_ U)).map (modulePullbackRestrictionIso φ U M).hom) =
      ((Scheme.Modules.restrictAdjunction U.ι).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (φ ∣_ U))).unit.app M :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ M

theorem modulePullbackRestrictionIso_unit_explicit (φ : Y ⟶ X) (U : X.Opens) (M : X.Modules) :
    ((Scheme.Modules.pullbackPushforwardAdjunction φ).unit.app M ≫
      (Scheme.Modules.pushforward φ).map
        ((Scheme.Modules.restrictAdjunction (φ ⁻¹ᵁ U).ι).unit.app
          ((Scheme.Modules.pullback φ).obj M))) ≫
      (modulePullbackRestrictionPushforwardIso φ U).hom.app
        (((Scheme.Modules.pullback φ).obj M).restrict (φ ⁻¹ᵁ U).ι) ≫
      (Scheme.Modules.pushforward U.ι).map
        ((Scheme.Modules.pushforward (φ ∣_ U)).map (modulePullbackRestrictionIso φ U M).hom) =
    (Scheme.Modules.restrictAdjunction U.ι).unit.app M ≫
      (Scheme.Modules.pushforward U.ι).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (φ ∣_ U)).unit.app (M.restrict U.ι)) := by
  exact modulePullbackRestrictionIso_unit φ U M

theorem modulePullbackRestrictionIso_unit_sections (φ : Y ⟶ X) (U V : X.Opens)
    (M : X.Modules) (s : Γ(M, V)) :
    Scheme.Modules.Hom.app
      ((Scheme.Modules.pushforward U.ι).map
        ((Scheme.Modules.pushforward (φ ∣_ U)).map (modulePullbackRestrictionIso φ U M).hom)) V
      (Scheme.Modules.Hom.app ((modulePullbackRestrictionAdjunction φ U).unit.app M) V s) =
    Scheme.Modules.Hom.app
      (((Scheme.Modules.restrictAdjunction U.ι).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (φ ∣_ U))).unit.app M) V s := by
  exact ConcreteCategory.congr_hom
    (congrArg (fun b => Scheme.Modules.Hom.app b V)
      (modulePullbackRestrictionIso_unit φ U M)) s

noncomputable def modulePullbackRestrictedCoefficientHom (φ : Y ⟶ X) (U : X.Opens)
    {M : X.Modules} (c : M.restrict U.ι ⟶ SheafOfModules.unit (U : Scheme).ringCatSheaf) :
    ((Scheme.Modules.pullback φ).obj M).restrict (φ ⁻¹ᵁ U).ι ⟶
      SheafOfModules.unit ((φ ⁻¹ᵁ U) : Scheme).ringCatSheaf :=
  (modulePullbackRestrictionIso φ U M).hom ≫ modulePullbackCoefficientHom (φ ∣_ U) c

theorem modulePullbackCoefficientHom_adjoint (φ : Y ⟶ X) {M : X.Modules}
    (c : M ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (Scheme.Modules.pullbackPushforwardAdjunction φ).unit.app M ≫
      (Scheme.Modules.pushforward φ).map (modulePullbackCoefficientHom φ c) =
        c ≫ SheafOfModules.unitToPushforwardObjUnit φ.toRingCatSheafHom := by
  have hn : (Scheme.Modules.pullbackPushforwardAdjunction φ).unit.app M ≫
      (Scheme.Modules.pushforward φ).map ((Scheme.Modules.pullback φ).map c) =
      c ≫ (Scheme.Modules.pullbackPushforwardAdjunction φ).unit.app
        (SheafOfModules.unit X.ringCatSheaf) :=
    ((Scheme.Modules.pullbackPushforwardAdjunction φ).unit.naturality c).symm
  have hu : (Scheme.Modules.pullbackPushforwardAdjunction φ).unit.app
      (SheafOfModules.unit X.ringCatSheaf) ≫
      (Scheme.Modules.pushforward φ).map (Scheme.Modules.pullbackObjUnitIso φ).hom =
      SheafOfModules.unitToPushforwardObjUnit φ.toRingCatSheafHom :=
    Scheme.Modules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom φ
  unfold modulePullbackCoefficientHom
  rw [Functor.map_comp, ← Category.assoc]
  exact (congrArg (· ≫ (Scheme.Modules.pushforward φ).map
    (Scheme.Modules.pullbackObjUnitIso φ).hom) hn).trans
      ((Category.assoc _ _ _).trans (congrArg (c ≫ ·) hu))

theorem modulePullbackRestrictedCoefficientHom_adjoint (φ : Y ⟶ X) (U : X.Opens)
    {M : X.Modules} (c : M.restrict U.ι ⟶ SheafOfModules.unit (U : Scheme).ringCatSheaf) :
    (Scheme.Modules.pullbackPushforwardAdjunction φ).unit.app M ≫
      (Scheme.Modules.pushforward φ).map
        ((Scheme.Modules.restrictAdjunction (φ ⁻¹ᵁ U).ι).unit.app
            ((Scheme.Modules.pullback φ).obj M) ≫
          (Scheme.Modules.pushforward (φ ⁻¹ᵁ U).ι).map
            (modulePullbackRestrictedCoefficientHom φ U c)) ≫
      (modulePullbackRestrictionPushforwardIso φ U).hom.app
        (SheafOfModules.unit ((φ ⁻¹ᵁ U) : Scheme).ringCatSheaf) =
    (Scheme.Modules.restrictAdjunction U.ι).unit.app M ≫
      (Scheme.Modules.pushforward U.ι).map c ≫
      (Scheme.Modules.pushforward U.ι).map
        (SheafOfModules.unitToPushforwardObjUnit (φ ∣_ U).toRingCatSheafHom) := by
  have h := congrArg (fun b => b ≫ (Scheme.Modules.pushforward U.ι).map
      ((Scheme.Modules.pushforward (φ ∣_ U)).map
        (modulePullbackCoefficientHom (φ ∣_ U) c)))
    (modulePullbackRestrictionIso_unit_explicit φ U M)
  have hn : (Scheme.Modules.pushforward φ).map
      ((Scheme.Modules.pushforward (φ ⁻¹ᵁ U).ι).map
        (modulePullbackRestrictedCoefficientHom φ U c)) ≫
      (modulePullbackRestrictionPushforwardIso φ U).hom.app
        (SheafOfModules.unit ((φ ⁻¹ᵁ U) : Scheme).ringCatSheaf) =
      (modulePullbackRestrictionPushforwardIso φ U).hom.app
        (((Scheme.Modules.pullback φ).obj M).restrict (φ ⁻¹ᵁ U).ι) ≫
      (Scheme.Modules.pushforward U.ι).map
        ((Scheme.Modules.pushforward (φ ∣_ U)).map
          (modulePullbackRestrictedCoefficientHom φ U c)) :=
    (modulePullbackRestrictionPushforwardIso φ U).hom.naturality _
  calc
    _ = (Scheme.Modules.pullbackPushforwardAdjunction φ).unit.app M ≫
        (Scheme.Modules.pushforward φ).map
          ((Scheme.Modules.restrictAdjunction (φ ⁻¹ᵁ U).ι).unit.app
            ((Scheme.Modules.pullback φ).obj M)) ≫
        ((Scheme.Modules.pushforward φ).map
          ((Scheme.Modules.pushforward (φ ⁻¹ᵁ U).ι).map
            (modulePullbackRestrictedCoefficientHom φ U c)) ≫
          (modulePullbackRestrictionPushforwardIso φ U).hom.app
            (SheafOfModules.unit ((φ ⁻¹ᵁ U) : Scheme).ringCatSheaf)) := by
      rw [Functor.map_comp]
      simp only [Category.assoc]
    _ = _ := congrArg (fun b => (Scheme.Modules.pullbackPushforwardAdjunction φ).unit.app M ≫
        (Scheme.Modules.pushforward φ).map
          ((Scheme.Modules.restrictAdjunction (φ ⁻¹ᵁ U).ι).unit.app
            ((Scheme.Modules.pullback φ).obj M)) ≫ b) hn
    _ = (Scheme.Modules.restrictAdjunction U.ι).unit.app M ≫
        (Scheme.Modules.pushforward U.ι).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (φ ∣_ U)).unit.app (M.restrict U.ι)) ≫
        (Scheme.Modules.pushforward U.ι).map
          ((Scheme.Modules.pushforward (φ ∣_ U)).map
            (modulePullbackCoefficientHom (φ ∣_ U) c)) := by
      simpa only [modulePullbackRestrictedCoefficientHom, Functor.map_comp, Category.assoc] using h
    _ = (Scheme.Modules.restrictAdjunction U.ι).unit.app M ≫
        (Scheme.Modules.pushforward U.ι).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (φ ∣_ U)).unit.app (M.restrict U.ι) ≫
            (Scheme.Modules.pushforward (φ ∣_ U)).map (modulePullbackCoefficientHom (φ ∣_ U) c)) := by
      rw [Functor.map_comp]
    _ = (Scheme.Modules.restrictAdjunction U.ι).unit.app M ≫
        (Scheme.Modules.pushforward U.ι).map
          (c ≫ SheafOfModules.unitToPushforwardObjUnit (φ ∣_ U).toRingCatSheafHom) :=
      congrArg (fun b => (Scheme.Modules.restrictAdjunction U.ι).unit.app M ≫
        (Scheme.Modules.pushforward U.ι).map b) (modulePullbackCoefficientHom_adjoint (φ ∣_ U) c)
    _ = _ := by rw [Functor.map_comp]

end MixedFujita
