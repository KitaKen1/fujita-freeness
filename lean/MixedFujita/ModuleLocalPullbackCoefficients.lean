/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ModulePullbackRegularTransports
public import MixedFujita.ModuleOpenFrameGerms

/-!
Compute the coefficient of the actual pulled section in the actual
pulled local frame as the actual scheme map of the source coefficient.
The open-section equality and actual global-section germ equality are
proved from the actual adjunction and regular-function comparison; no
coefficient equality or order inequality is supplied.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {X Y : Scheme.{u}}

noncomputable def moduleLocalPullbackFrameIso (φ : Y ⟶ X) (M : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf) :
    ((Scheme.Modules.pullback φ).obj M).restrict (φ ⁻¹ᵁ U).ι ≅
      SheafOfModules.unit ((φ ⁻¹ᵁ U) : Scheme).ringCatSheaf :=
  modulePullbackRestrictionIso φ U M ≪≫ modulePullbackFrameIso (φ ∣_ U) e

theorem moduleLocalPullbackFrameIso_hom (φ : Y ⟶ X) (M : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf) :
    (moduleLocalPullbackFrameIso φ M U e).hom =
      modulePullbackRestrictedCoefficientHom φ U e.hom := rfl

theorem modulePullbackSections_local_frame_coefficient (φ : Y ⟶ X)
    (M : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf)
    (s : Γ(M, U)) :
    moduleOverFrameCoefficient ((Scheme.Modules.pullback φ).obj M) (φ ⁻¹ᵁ U)
      (moduleRestrictFrameOverIso _ _ (moduleLocalPullbackFrameIso φ M U e))
      (φ ⁻¹ᵁ U) le_rfl (modulePullbackSections φ M U s) =
    φ.app U (moduleOverFrameCoefficient M U (moduleRestrictFrameOverIso M U e) U le_rfl s) := by
  have h := modulePullbackRestrictedCoefficientHom_component_square φ M U e s
  rw [← moduleLocalPullbackFrameIso_hom φ M U e,
    moduleRestrictFrameOverIso_adjoint_component,
    moduleRestrictFrameOverIso_adjoint_component, moduleUnitToPushforwardObjUnit_app] at h
  have hr := modulePullbackRestrictionPushforwardIso_unit_regular φ U
    (moduleOverFrameCoefficient M U (moduleRestrictFrameOverIso M U e) U le_rfl s)
  let : IsIso ((φ ⁻¹ᵁ U).ι.app (φ ⁻¹ᵁ U)) := by
    rw [Scheme.Opens.ι_app_self]
    infer_instance
  apply (ConcreteCategory.bijective_of_isIso ((φ ⁻¹ᵁ U).ι.app (φ ⁻¹ᵁ U))).1
  apply (ConcreteCategory.bijective_of_isIso
    (Scheme.Modules.Hom.app ((modulePullbackRestrictionPushforwardIso φ U).hom.app
      (SheafOfModules.unit ((φ ⁻¹ᵁ U) : Scheme).ringCatSheaf)) U)).1
  exact h.trans hr.symm

theorem moduleLocalPullbackFrame_global_germ (φ : Y ⟶ X) (M : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf)
    (y : Y) (hy : φ y ∈ U) (s : Γ(M, ⊤)) :
    moduleOverFrameGlobalCoefficientGerm ((Scheme.Modules.pullback φ).obj M) (φ ⁻¹ᵁ U)
      (moduleRestrictFrameOverIso _ _ (moduleLocalPullbackFrameIso φ M U e)) y hy
      (modulePullbackGlobalSections φ M s) =
    φ.stalkMap y
      (moduleOverFrameGlobalCoefficientGerm M U (moduleRestrictFrameOverIso M U e) (φ y) hy s) := by
  unfold moduleOverFrameGlobalCoefficientGerm
  rw [modulePullbackGlobalSections_restrict, modulePullbackSections_local_frame_coefficient]
  exact (Scheme.Hom.germ_stalkMap_apply φ U y hy _).symm

end MixedFujita
