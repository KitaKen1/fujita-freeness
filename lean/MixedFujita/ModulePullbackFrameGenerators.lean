/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ModuleLocalPullbackCoefficients
public import MixedFujita.EffectiveCartierIdealSheaf

/-!
The section with frame coefficient one is an actual local generator.
Its adjunction pullback again has coefficient one. A pulled-back map
to the structure module is therefore multiplication by the pulled-back
image of this generator, on every subopen. Its image ideal is principal.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {X Y : Scheme.{u}}

noncomputable def moduleOpenFrameGenerator (M : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf) : Γ(M, U) :=
  (moduleOverFrameCoefficient M U (moduleRestrictFrameOverIso M U e) U le_rfl).symm 1

theorem moduleOpenFrameGenerator_coefficient (M : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf) :
    moduleOverFrameCoefficient M U (moduleRestrictFrameOverIso M U e) U le_rfl
      (moduleOpenFrameGenerator M U e) = 1 :=
  LinearEquiv.apply_symm_apply _ _

theorem moduleFrame_section_eq_coefficient_smul (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (t : Γ(M, U)) (ht : moduleOverFrameCoefficient M U e U le_rfl t = 1)
    (W : X.Opens) (hWU : W ≤ U) (s : Γ(M, W)) :
    s = moduleOverFrameCoefficient M U e W hWU s •
      M.presheaf.map (homOfLE hWU).op t := by
  apply (moduleOverFrameCoefficient M U e W hWU).injective
  rw [LinearEquiv.map_smul, moduleOverFrameCoefficient_restrict M U e le_rfl,
    ht, map_one, smul_eq_mul, mul_one]

theorem moduleOpenFrameGenerator_generates (M : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf)
    (W : X.Opens) (hWU : W ≤ U) (s : Γ(M, W)) :
    s = moduleOverFrameCoefficient M U (moduleRestrictFrameOverIso M U e) W hWU s •
      M.presheaf.map (homOfLE hWU).op (moduleOpenFrameGenerator M U e) :=
  moduleFrame_section_eq_coefficient_smul M U _ _
    (moduleOpenFrameGenerator_coefficient M U e) W hWU s

noncomputable def modulePulledOpenFrame (φ : Y ⟶ X) (M : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf) :
    ((Scheme.Modules.pullback φ).obj M).over (φ ⁻¹ᵁ U) ≅
      SheafOfModules.unit (Y.ringCatSheaf.over (φ ⁻¹ᵁ U)) :=
  moduleRestrictFrameOverIso _ _ (moduleLocalPullbackFrameIso φ M U e)

theorem modulePullbackFrameGenerator_coefficient (φ : Y ⟶ X) (M : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf) :
    moduleOverFrameCoefficient ((Scheme.Modules.pullback φ).obj M) (φ ⁻¹ᵁ U)
      (modulePulledOpenFrame φ M U e) (φ ⁻¹ᵁ U) le_rfl
        (modulePullbackSections φ M U (moduleOpenFrameGenerator M U e)) = 1 := by
  rw [modulePulledOpenFrame, modulePullbackSections_local_frame_coefficient,
    moduleOpenFrameGenerator_coefficient, map_one]

theorem modulePullbackFrameGenerator_generates (φ : Y ⟶ X) (M : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf)
    (W : Y.Opens) (hWU : W ≤ φ ⁻¹ᵁ U)
    (s : Γ((Scheme.Modules.pullback φ).obj M, W)) :
    s = moduleOverFrameCoefficient ((Scheme.Modules.pullback φ).obj M) (φ ⁻¹ᵁ U)
      (modulePulledOpenFrame φ M U e) W hWU s •
        ((Scheme.Modules.pullback φ).obj M).presheaf.map (homOfLE hWU).op
          (modulePullbackSections φ M U (moduleOpenFrameGenerator M U e)) :=
  moduleFrame_section_eq_coefficient_smul _ _ _ _
    (modulePullbackFrameGenerator_coefficient φ M U e) W hWU s

theorem modulePullbackStructureHom_local_formula (φ : Y ⟶ X) (M : X.Modules)
    (c : M ⟶ SheafOfModules.unit X.ringCatSheaf) (U : X.Opens)
    (e : M.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf)
    (W : Y.Opens) (hWU : W ≤ φ ⁻¹ᵁ U)
    (s : Γ((Scheme.Modules.pullback φ).obj M, W)) :
    Scheme.Modules.Hom.app (modulePullbackCoefficientHom φ c) W s =
      moduleOverFrameCoefficient ((Scheme.Modules.pullback φ).obj M) (φ ⁻¹ᵁ U)
        (modulePulledOpenFrame φ M U e) W hWU s *
          Y.presheaf.map (homOfLE hWU).op
            (φ.app U (Scheme.Modules.Hom.app c U (moduleOpenFrameGenerator M U e))) := by
  conv_lhs => rw [modulePullbackFrameGenerator_generates φ M U e W hWU s]
  rw [Scheme.Modules.Hom.app_smul]
  have hn := PresheafOfModules.naturality_apply
    (modulePullbackCoefficientHom φ c).val (homOfLE hWU).op
      (modulePullbackSections φ M U (moduleOpenFrameGenerator M U e))
  change Scheme.Modules.Hom.app (modulePullbackCoefficientHom φ c) W
      (((Scheme.Modules.pullback φ).obj M).presheaf.map (homOfLE hWU).op
        (modulePullbackSections φ M U (moduleOpenFrameGenerator M U e))) =
    Y.presheaf.map (homOfLE hWU).op
      (Scheme.Modules.Hom.app (modulePullbackCoefficientHom φ c) (φ ⁻¹ᵁ U)
        (modulePullbackSections φ M U (moduleOpenFrameGenerator M U e))) at hn
  rw [hn, modulePullbackSections_coefficient, smul_eq_mul]

theorem modulePullbackStructureHom_local_image (φ : Y ⟶ X) (M : X.Modules)
    (c : M ⟶ SheafOfModules.unit X.ringCatSheaf) (U : X.Opens)
    (e : M.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf)
    (W : Y.Opens) (hWU : W ≤ φ ⁻¹ᵁ U) :
    moduleStructureImageIdeal (modulePullbackCoefficientHom φ c) W =
      Ideal.span ({(Y.presheaf.map (homOfLE hWU).op
        (φ.app U (Scheme.Modules.Hom.app c U (moduleOpenFrameGenerator M U e))))} :
          Set Γ(Y, W)) := by
  apply SetLike.coe_injective
  ext a
  change (∃ s, Scheme.Modules.Hom.app (modulePullbackCoefficientHom φ c) W s = a) ↔
    a ∈ Ideal.span ({(Y.presheaf.map (homOfLE hWU).op
      (φ.app U (Scheme.Modules.Hom.app c U (moduleOpenFrameGenerator M U e))))} : Set Γ(Y, W))
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨_, (modulePullbackStructureHom_local_formula φ M c U e W hWU s).symm⟩
  · rintro ⟨r, hr⟩
    refine ⟨(moduleOverFrameCoefficient ((Scheme.Modules.pullback φ).obj M) (φ ⁻¹ᵁ U)
      (modulePulledOpenFrame φ M U e) W hWU).symm r, ?_⟩
    rw [modulePullbackStructureHom_local_formula φ M c U e W hWU,
      LinearEquiv.apply_symm_apply, hr]

end MixedFujita
