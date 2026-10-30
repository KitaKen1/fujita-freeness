/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ModuleOpenFrameCoefficients

/-!
Evaluate actual open frame coefficients of actual global module sections
in actual local rings. Shrinking the open leaves the germ unchanged.
Module isomorphisms preserve these coefficients under the transported
frame. Changing a frame multiplies every coefficient germ by one actual
local unit, obtained by mapping the actual regular transition unit.
The actual Cartier open equation frame recovers the intrinsic Cartier
local coefficient. No coefficient identity or transition unit is supplied.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false

universe u

variable {X : Scheme.{u}}

noncomputable def moduleOverFrameGlobalCoefficientGerm (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (x : X) (hx : x ∈ U) (s : Γ(M, ⊤)) : X.presheaf.stalk x :=
  X.presheaf.germ U x hx (moduleOverFrameCoefficient M U e U le_rfl
    (M.presheaf.map (homOfLE le_top : U ⟶ ⊤).op s))

theorem moduleOverFrameGlobalCoefficientGerm_change_frame (M : X.Modules) (U : X.Opens)
    (e d : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (x : X) (hx : x ∈ U) :
    ∃ v : (X.presheaf.stalk x)ˣ, ∀ s : Γ(M, ⊤),
      moduleOverFrameGlobalCoefficientGerm M U e x hx s =
        (v : X.presheaf.stalk x) * moduleOverFrameGlobalCoefficientGerm M U d x hx s := by
  obtain ⟨v, hv⟩ := moduleOverFrameCoefficient_change_frame M U e d U le_rfl
  refine ⟨Units.map (X.presheaf.germ U x hx).hom.toMonoidHom v, fun s => ?_⟩
  simp only [moduleOverFrameGlobalCoefficientGerm, Units.coe_map]
  rw [hv _, map_mul]
  rfl

theorem moduleOverFrameGlobalCoefficientGerm_restrict (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (V : X.Opens) (hVU : V ≤ U) (x : X) (hx : x ∈ V) (s : Γ(M, ⊤)) :
    moduleOverFrameGlobalCoefficientGerm M V (moduleOverFrameRestrictIso M U e V hVU) x hx s =
      moduleOverFrameGlobalCoefficientGerm M U e x (hVU hx) s := by
  unfold moduleOverFrameGlobalCoefficientGerm
  rw [moduleOverFrameRestrictIso_coefficient]
  have h : M.presheaf.map (homOfLE le_top : V ⟶ ⊤).op s =
      M.presheaf.map (homOfLE hVU).op
        (M.presheaf.map (homOfLE le_top : U ⟶ ⊤).op s) := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  rw [h, moduleOverFrameCoefficient_restrict]
  exact X.presheaf.germ_res_apply (homOfLE hVU) x hx _

theorem moduleOverFrameGlobalCoefficientGerm_viaIso {M N : X.Modules} (U : X.Opens)
    (a : M ≅ N) (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (x : X) (hx : x ∈ U) (s : Γ(M, ⊤)) :
    moduleOverFrameGlobalCoefficientGerm N U (moduleOverFrameViaIso U a e) x hx
      (Scheme.Modules.Hom.app a.hom ⊤ s) = moduleOverFrameGlobalCoefficientGerm M U e x hx s := by
  unfold moduleOverFrameGlobalCoefficientGerm
  have h := ConcreteCategory.congr_hom
    (a.hom.mapPresheaf.naturality (homOfLE le_top : U ⟶ ⊤).op) s
  change Scheme.Modules.Hom.app a.hom U (M.presheaf.map (homOfLE le_top : U ⟶ ⊤).op s) =
    N.presheaf.map (homOfLE le_top : U ⟶ ⊤).op (Scheme.Modules.Hom.app a.hom ⊤ s) at h
  rw [← h, moduleOverFrameViaIso_coefficient]

variable [IsIntegral X]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

theorem moduleOverFrameGlobalCoefficientGerm_cartier (D : CartierDivisor X) (U : X.Opens)
    [Nonempty U] (f : X.functionFieldˣ)
    (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U)
    (x : X) (hx : x ∈ U) (s : Γ(D.sheaf, ⊤)) :
    moduleOverFrameGlobalCoefficientGerm D.sheaf U (cartierOpenFrameIso D U f hf) x hx s =
      cartierLocalCoefficient D x f (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hf hx) s :=
  cartierOpenCoefficient_germ_global D U f hf x hx s

theorem moduleRestrictFrameGlobalCoefficientGerm_cartier (D : CartierDivisor X) (U : X.Opens)
    [Nonempty U] (f : X.functionFieldˣ)
    (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U)
    (x : X) (hx : x ∈ U) (s : Γ(D.sheaf, ⊤)) :
    moduleOverFrameGlobalCoefficientGerm D.sheaf U
      (moduleRestrictFrameOverIso D.sheaf U (cartierOpenRestrictFrameIso D U f hf)) x hx s =
      cartierLocalCoefficient D x f (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hf hx) s := by
  rw [show moduleRestrictFrameOverIso D.sheaf U (cartierOpenRestrictFrameIso D U f hf) =
    cartierOpenFrameIso D U f hf from moduleRestrictFrameOverIso_roundTrip _ _ _]
  exact moduleOverFrameGlobalCoefficientGerm_cartier D U f hf x hx s

end MixedFujita
