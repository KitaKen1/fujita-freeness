/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ModuleOpenFrameGerms

/-!
For an actual module isomorphism to an actual Cartier sheaf, construct
the unit comparing an actual module-frame coefficient germ with the
intrinsic Cartier coefficient of the transported actual global section.
The comparison works on a smaller common neighborhood of any point; no
coefficient-compatibility equality or transition unit is supplied.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false

universe u

variable {X : Scheme.{u}} [IsIntegral X]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

theorem cartierRepresentationFrameUnits_on_open (M : X.Modules) (D : CartierDivisor X)
    (a : M ≅ D.sheaf) (U : X.Opens) [Nonempty U]
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (f : X.functionFieldˣ) (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U)
    (x : X) (hx : x ∈ U) :
    ∃ v : (X.presheaf.stalk x)ˣ, ∀ s : Γ(M, ⊤),
      cartierLocalCoefficient D x f (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hf hx)
        (Scheme.Modules.Hom.app a.hom ⊤ s) =
      (v : X.presheaf.stalk x) * moduleOverFrameGlobalCoefficientGerm M U e x hx s := by
  obtain ⟨v, hv⟩ := moduleOverFrameGlobalCoefficientGerm_change_frame D.sheaf U
    (cartierOpenFrameIso D U f hf) (moduleOverFrameViaIso U a e) x hx
  refine ⟨v, fun s => ?_⟩
  have h := hv (Scheme.Modules.Hom.app a.hom ⊤ s)
  rw [moduleOverFrameGlobalCoefficientGerm_cartier,
    moduleOverFrameGlobalCoefficientGerm_viaIso] at h
  exact h

theorem cartierRepresentationFrameUnits_neighborhood (M : X.Modules) (D : CartierDivisor X)
    (a : M ≅ D.sheaf) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (x : X) (hx : x ∈ U) :
    ∃ (V : X.Opens) (_hVU : V ≤ U) (hxV : x ∈ V) (f : X.functionFieldˣ),
      haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
      ∃ hf : rationalUnitClass X V (Additive.ofMul f) = D |_ V,
        ∃ v : (X.presheaf.stalk x)ˣ, ∀ s : Γ(M, ⊤),
          cartierLocalCoefficient D x f
            (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hf hxV)
            (Scheme.Modules.Hom.app a.hom ⊤ s) =
          (v : X.presheaf.stalk x) * moduleOverFrameGlobalCoefficientGerm M U e x hx s := by
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt x
  obtain ⟨W, hxW, hW⟩ := CartierDivisor.isLocalEquationAt_iff.mp hf
  let V : X.Opens := U ⊓ W
  have hxV : x ∈ V := ⟨hx, hxW⟩
  let : Nonempty V := ⟨⟨x, hxV⟩⟩
  let : Nonempty W := ⟨⟨x, hxW⟩⟩
  have hV := CartierDivisor.rationalUnitClass_eq_of_le (show V ≤ W from inf_le_right) hW
  obtain ⟨v, hv⟩ := cartierRepresentationFrameUnits_on_open M D a V
    (moduleOverFrameRestrictIso M U e V inf_le_left) f hV x hxV
  refine ⟨V, inf_le_left, hxV, f, hV, v, fun s => ?_⟩
  simpa only [moduleOverFrameGlobalCoefficientGerm_restrict] using hv s

theorem cartierRepresentationFrameOrder_eq (M : X.Modules) (D : CartierDivisor X)
    (a : M ≅ D.sheaf) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (x : X) (hx : x ∈ U) (s : Γ(M, ⊤)) :
    cartierSectionVanishingOrder D x (Scheme.Modules.Hom.app a.hom ⊤ s) =
      localAdicOrder (X.presheaf.stalk x) (moduleOverFrameGlobalCoefficientGerm M U e x hx s) := by
  obtain ⟨V, _, hxV, f, hf, v, hv⟩ := cartierRepresentationFrameUnits_neighborhood M D a U e x hx
  let : Nonempty V := ⟨⟨x, hxV⟩⟩
  rw [cartierSectionVanishingOrder_eq_localCoefficient D x f
      (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hf hxV), hv s,
    localAdicOrder_unit_mul]

end MixedFujita
