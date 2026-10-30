/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ModuleRestrictedFrameComponents

/-!
Evaluate the actual adjunction square on open sections, including the
actual open-inclusion and pushforward comparison transports. Identify
restricted-frame components with their ambient coefficient followed by
the open-inclusion regular-function map. Removing the remaining regular
function transports, or passing to their actual stalk germs, is separate.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {X Y : Scheme.{u}}

theorem moduleRestrictFrameOverIso_adjoint_component (M : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf)
    (s : Γ(M, U)) :
    Scheme.Modules.Hom.app e.hom (U.ι ⁻¹ᵁ U)
      (M.presheaf.map (homOfLE (U.ι.image_preimage_le U)).op s) =
    U.ι.app U (moduleOverFrameCoefficient M U (moduleRestrictFrameOverIso M U e) U le_rfl s) := by
  have h := moduleOverFrameCoefficient_restrict M U (moduleRestrictFrameOverIso M U e) le_rfl
    (homOfLE (U.ι.image_preimage_le U)) s
  rw [moduleRestrictFrameOverIso_component] at h
  rw [Scheme.Opens.ι_app_self]
  rw [show (eqToHom (by simp) : U.ι ''ᵁ (U.ι ⁻¹ᵁ U) ⟶ U) =
    homOfLE (U.ι.image_preimage_le U) from Subsingleton.elim _ _]
  exact h

theorem modulePullbackRestrictedCoefficientHom_component_square (φ : Y ⟶ X)
    (M : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf)
    (s : Γ(M, U)) :
    Scheme.Modules.Hom.app
      ((modulePullbackRestrictionPushforwardIso φ U).hom.app
        (SheafOfModules.unit ((φ ⁻¹ᵁ U) : Scheme).ringCatSheaf)) U
      (Scheme.Modules.Hom.app (modulePullbackRestrictedCoefficientHom φ U e.hom)
        ((φ ⁻¹ᵁ U).ι ⁻¹ᵁ (φ ⁻¹ᵁ U))
        (((Scheme.Modules.pullback φ).obj M).presheaf.map
          (homOfLE ((φ ⁻¹ᵁ U).ι.image_preimage_le (φ ⁻¹ᵁ U))).op
          (modulePullbackSections φ M U s))) =
    Scheme.Modules.Hom.app
      (SheafOfModules.unitToPushforwardObjUnit (φ ∣_ U).toRingCatSheafHom) (U.ι ⁻¹ᵁ U)
      (Scheme.Modules.Hom.app e.hom (U.ι ⁻¹ᵁ U)
        (M.presheaf.map (homOfLE (U.ι.image_preimage_le U)).op s)) := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun b => Scheme.Modules.Hom.app b U)
      (modulePullbackRestrictedCoefficientHom_adjoint φ U e.hom)) s
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Modules.pushforward_map_app, Scheme.Modules.restrictAdjunction_unit_app_app] at h
  rw [modulePullbackSections_apply]
  convert h using 1

end MixedFujita
