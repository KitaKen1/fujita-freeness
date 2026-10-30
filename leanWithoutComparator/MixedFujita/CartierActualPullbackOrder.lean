/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ModuleLocalPullbackCoefficients
public import MixedFujita.CartierPullbackFrameOrder

/-!
Identify the actual pulled-frame coefficient germ with the actual
source intrinsic Cartier coefficient sent through the scheme stalk map.
The actual pulled global section in a chosen target Cartier presentation
therefore has that intrinsic pulled order. Construct its coefficient
comparison unit, rather than assuming one. Nonzero source sections can
still pull back to zero; the proved nonzero criterion concerns the
actual pulled section and the actual restricted stalk coefficient.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {X Y : Scheme.{u}} [IsIntegral X]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

theorem cartierPullbackFrameCoefficientGerm_eq_stalkCoefficient
    (D : CartierDivisor X) (φ : Y ⟶ X) (U : X.Opens) [Nonempty U]
    (f : X.functionFieldˣ) (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U)
    (y : Y) (hy : φ y ∈ U) (s : Γ(D.sheaf, ⊤)) :
    cartierPullbackFrameCoefficientGerm D φ U f hf y hy s =
      cartierStalkPullbackCoefficient D φ y f
        (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hf hy) s := by
  unfold cartierPullbackFrameCoefficientGerm
  rw [show cartierPullbackLocalFrameIso D φ U f hf =
    moduleLocalPullbackFrameIso φ D.sheaf U (cartierOpenRestrictFrameIso D U f hf) from rfl,
    moduleLocalPullbackFrame_global_germ, moduleRestrictFrameGlobalCoefficientGerm_cartier]
  rfl

theorem cartierPullbackFrameOrder_eq_stalkOrder (D : CartierDivisor X) (φ : Y ⟶ X)
    (U : X.Opens) [Nonempty U] (f : X.functionFieldˣ)
    (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U)
    (y : Y) (hy : φ y ∈ U) (s : Γ(D.sheaf, ⊤)) :
    cartierPullbackFrameOrder D φ U f hf y hy s = cartierStalkPullbackOrder D φ y s := by
  unfold cartierPullbackFrameOrder
  rw [cartierPullbackFrameCoefficientGerm_eq_stalkCoefficient,
    cartierStalkPullbackOrder_eq_localCoefficient D φ y f
      (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hf hy)]

theorem cartierSourceOrder_le_actualPullbackFrameOrder (D : CartierDivisor X) (φ : Y ⟶ X)
    (U : X.Opens) [Nonempty U] (f : X.functionFieldˣ)
    (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U)
    (y : Y) (hy : φ y ∈ U) (s : Γ(D.sheaf, ⊤)) :
    cartierSectionVanishingOrder D (φ y) s ≤ cartierPullbackFrameOrder D φ U f hf y hy s := by
  rw [cartierPullbackFrameOrder_eq_stalkOrder]
  exact cartierSectionVanishingOrder_le_stalkPullbackOrder D φ y s

variable [IsIntegral Y]

theorem cartierActualPullback_local_coefficients (D : CartierDivisor X) (φ : Y ⟶ X)
    (E : CartierDivisor Y) (a : (Scheme.Modules.pullback φ).obj D.sheaf ≅ E.sheaf)
    (y : Y) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt (φ y) f) :
    ∃ (g : Y.functionFieldˣ) (hg : E.IsLocalEquationAt y g),
      ∃ v : (Y.presheaf.stalk y)ˣ, ∀ s : Γ(D.sheaf, ⊤),
        cartierStalkPullbackCoefficient D φ y f hf s =
          (v : Y.presheaf.stalk y) * cartierLocalCoefficient E y g hg
            (cartierPullbackGlobalSectionViaIso D φ E a s) := by
  obtain ⟨U, hy, hU⟩ := CartierDivisor.isLocalEquationAt_iff.mp hf
  let : Nonempty U := ⟨⟨φ y, hy⟩⟩
  obtain ⟨V, _, hyV, g, hg, v, hv⟩ := cartierRepresentationFrameUnits_neighborhood
    ((Scheme.Modules.pullback φ).obj D.sheaf) E a (φ ⁻¹ᵁ U)
      (moduleRestrictFrameOverIso _ _ (cartierPullbackLocalFrameIso D φ U f hU)) y hy
  let : Nonempty V := ⟨⟨y, hyV⟩⟩
  refine ⟨g, CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hg hyV, v⁻¹,
    fun s => ?_⟩
  have h := hv (modulePullbackGlobalSections φ D.sheaf s)
  change cartierLocalCoefficient E y g _ (cartierPullbackGlobalSectionViaIso D φ E a s) =
    (v : Y.presheaf.stalk y) * cartierPullbackFrameCoefficientGerm D φ U f hU y hy s at h
  rw [cartierPullbackFrameCoefficientGerm_eq_stalkCoefficient] at h
  rw [h]
  exact (v.inv_mul_cancel_left _).symm

theorem cartierStalkPullbackOrder_eq_actualGlobalPullback (D : CartierDivisor X) (φ : Y ⟶ X)
    (E : CartierDivisor Y) (a : (Scheme.Modules.pullback φ).obj D.sheaf ≅ E.sheaf)
    (y : Y) (s : Γ(D.sheaf, ⊤)) :
    cartierStalkPullbackOrder D φ y s =
      cartierSectionVanishingOrder E y (cartierPullbackGlobalSectionViaIso D φ E a s) := by
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt (φ y)
  obtain ⟨U, hy, hU⟩ := CartierDivisor.isLocalEquationAt_iff.mp hf
  let : Nonempty U := ⟨⟨φ y, hy⟩⟩
  exact (cartierPullbackFrameOrder_eq_stalkOrder D φ U f hU y hy s).symm.trans
    (cartierPullbackFrameOrder_eq_target_order D φ U f hU y hy s E a)

theorem cartierSourceOrder_le_actualGlobalPullback (D : CartierDivisor X) (φ : Y ⟶ X)
    (E : CartierDivisor Y) (a : (Scheme.Modules.pullback φ).obj D.sheaf ≅ E.sheaf)
    (y : Y) (s : Γ(D.sheaf, ⊤)) :
    cartierSectionVanishingOrder D (φ y) s ≤
      cartierSectionVanishingOrder E y (cartierPullbackGlobalSectionViaIso D φ E a s) := by
  exact (cartierSectionVanishingOrder_le_stalkPullbackOrder D φ y s).trans_eq
    (cartierStalkPullbackOrder_eq_actualGlobalPullback D φ E a y s)

theorem cartierStalkPullbackCoefficient_ne_zero_iff_actualGlobalPullback
    (D : CartierDivisor X) (φ : Y ⟶ X) (y : Y)
    (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt (φ y) f) (s : Γ(D.sheaf, ⊤)) :
    cartierStalkPullbackCoefficient D φ y f hf s ≠ 0 ↔
      modulePullbackGlobalSections φ D.sheaf s ≠ 0 := by
  obtain ⟨E, ⟨a⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor D φ
  obtain ⟨g, hg, v, hv⟩ := cartierActualPullback_local_coefficients D φ E a y f hf
  rw [hv s]
  simp only [ne_eq, Units.mul_right_eq_zero]
  exact (cartierLocalCoefficient_ne_zero_iff E y g hg _).trans
    (cartierPullbackGlobalSectionViaIso_ne_zero_iff D φ E a s)

theorem cartierStalkPullbackOrder_lt_top_iff_actualGlobalPullback
    (D : CartierDivisor X) (φ : Y ⟶ X) (y : Y) [IsNoetherianRing (Y.presheaf.stalk y)]
    (s : Γ(D.sheaf, ⊤)) :
    cartierStalkPullbackOrder D φ y s < ⊤ ↔ modulePullbackGlobalSections φ D.sheaf s ≠ 0 := by
  obtain ⟨E, ⟨a⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor D φ
  rw [cartierStalkPullbackOrder_eq_actualGlobalPullback D φ E a y s,
    cartierSectionVanishingOrder_lt_top_iff, cartierPullbackGlobalSectionViaIso_ne_zero_iff]

end MixedFujita
