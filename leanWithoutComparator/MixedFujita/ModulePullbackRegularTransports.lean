/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ModulePullbackFrameCoefficients

/-!
Identify the actual regular-function maps in the open-restriction
adjunction square. The actual pushforward comparison on the unit module
is the same transport as the scheme restriction square on regular
functions. This allows cancelling the actual comparison isomorphism
and the open-inclusion regular-function isomorphism in coefficient
computations, without supplying a coefficient-compatibility equality.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {X Y : Scheme.{u}}

theorem moduleUnitToPushforwardObjUnit_app (φ : Y ⟶ X) (U : X.Opens) (r : Γ(X, U)) :
    Scheme.Modules.Hom.app (SheafOfModules.unitToPushforwardObjUnit φ.toRingCatSheafHom) U r =
      φ.app U r := by
  rfl

theorem modulePullbackRestrictionPushforwardIso_unit_regular (φ : Y ⟶ X) (U : X.Opens)
    (r : Γ(X, U)) :
    Scheme.Modules.Hom.app
      ((modulePullbackRestrictionPushforwardIso φ U).hom.app
        (SheafOfModules.unit ((φ ⁻¹ᵁ U) : Scheme).ringCatSheaf)) U
      ((φ ⁻¹ᵁ U).ι.app (φ ⁻¹ᵁ U) (φ.app U r)) =
    (φ ∣_ U).app (U.ι ⁻¹ᵁ U) (U.ι.app U r) := by
  have h := ConcreteCategory.congr_hom (Scheme.Hom.congr_app (morphismRestrict_ι φ U) U) r
  simp only [Scheme.Hom.comp_app, ConcreteCategory.comp_apply] at h
  unfold modulePullbackRestrictionPushforwardIso
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforwardComp_inv_app_app, Scheme.Modules.pushforwardCongr_hom_app_app,
    Category.id_comp, Category.comp_id]
  convert h.symm using 1 <;> rfl

end MixedFujita
