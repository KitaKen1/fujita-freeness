/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierSectionBaseIdeal
public import MixedFujita.CartierStalkPullbackOrder
public import Hironaka.Scheme.IdealSheaf.StalkIdeal
public import Hironaka.Scheme.BlowUp.Descent
public import MixedFujita.AlignedEtalePointBlowup

/-! Every actual Cartier section coefficient belongs to the actual
section-base stalk ideal, and its pullback belongs to the principalized
fixed-part stalk ideal. A regular representative of any local equation
generates the effective Cartier stalk ideal. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

theorem effectiveCartier_stalkIdeal_eq_span_of_localEquation
    (D : CartierDivisor X) (hD : D.IsEffective) (x : X) (f : X.functionFieldˣ)
    (hf : D.IsLocalEquationAt x f) (a : X.presheaf.stalk x)
    (ha : algebraMap (X.presheaf.stalk x) X.functionField a = (f : X.functionField)) :
    (effectiveCartierIdealSheaf D hD).stalkIdeal x = Ideal.span {a} := by
  obtain ⟨U, hxU, hne, b, hb, hEq⟩ := exists_affineOpen_regularEquation_of_isEffective D hD x
  let v := X.presheaf.germ U.1 x hxU b
  have hspan : (effectiveCartierIdealSheaf D hD).stalkIdeal x = Ideal.span {v} := by
    rw [Scheme.IdealSheafData.stalkIdeal_eq_map_germ _ U hxU,
      effectiveCartierIdealSheaf_ideal_eq_span D hD U b hb hEq,
      Ideal.map_span, Set.image_singleton]
  obtain ⟨w, hw⟩ := hf.exists_unit_mul_eq
    (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hEq hxU)
  have hav : v * w = a := by
    apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
    rw [ha, ← hw, map_mul, X.algebraMap_germ_eq_germToFunctionField hxU,
      regularEquationRationalUnit_val]
    exact mul_comm _ _
  rw [hspan]
  exact Ideal.span_singleton_eq_span_singleton.mpr ⟨w, hav⟩

theorem cartierLocalCoefficient_mem_zeroIdeal (D : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) (x : X) (f : X.functionFieldˣ)
    (hf : D.IsLocalEquationAt x f) :
    cartierLocalCoefficient D x f hf s ∈ (cartierSectionZeroIdeal D s hs).stalkIdeal x := by
  have hI := effectiveCartier_stalkIdeal_eq_span_of_localEquation
    (cartierSectionZeroDivisor D s hs) (cartierSectionZeroDivisor_isEffective D s hs) x
      (f * cartierSectionUnit D s hs) (cartierSectionZeroDivisor_localEquation D s hs x f hf)
        (cartierLocalCoefficient D x f hf s) (by
          simpa only [Units.val_mul, cartierSectionUnit_val] using cartierLocalCoefficient_image D x f hf s)
  change cartierLocalCoefficient D x f hf s ∈
    (effectiveCartierIdealSheaf _ (cartierSectionZeroDivisor_isEffective D s hs)).stalkIdeal x
  rw [hI]
  exact Ideal.subset_span rfl

variable {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]

theorem cartierStalkPullbackCoefficient_mem_fixedPart {J : Type*} [Finite J]
    (ρ : Y ⟶ X) [IsDominant ρ] (D : CartierDivisor X)
    (s : J → Γ(D.sheaf, ⊤)) (hs : ∀ j, s j ≠ 0)
    (G : CartierDivisor Y) (hG : G.IsEffective)
    (hGI : effectiveCartierIdealSheaf G hG = (cartierSectionBaseIdeal D s hs).comap ρ)
    (P : Y) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt (ρ P) f) (j : J) :
    cartierStalkPullbackCoefficient D ρ P f hf (s j) ∈ (effectiveCartierIdealSheaf G hG).stalkIdeal P := by
  rw [hGI, Scheme.IdealSheafData.stalkIdeal_comap]
  apply Ideal.mem_map_of_mem
  apply Scheme.IdealSheafData.stalkIdeal_mono
    (show cartierSectionZeroIdeal D (s j) (hs j) ≤ cartierSectionBaseIdeal D s hs from by
      unfold cartierSectionBaseIdeal
      exact le_iSup (fun i => cartierSectionZeroIdeal D (s i) (hs i)) j) (ρ P)
  exact cartierLocalCoefficient_mem_zeroIdeal D (s j) (hs j) (ρ P) f hf

theorem stalkMapAtEq_cartier_coefficient (ρ : Y ⟶ X) [IsDominant ρ]
    (P : Y) (x : X) (hq : ρ P = x) (D : CartierDivisor X) (f : X.functionFieldˣ)
    (hf : D.IsLocalEquationAt x f) (s : Γ(D.sheaf, ⊤)) :
    stalkMapAtEq ρ P x hq (cartierLocalCoefficient D x f hf s) =
      cartierStalkPullbackCoefficient D ρ P f (hq.symm ▸ hf) s := by
  subst x
  rfl

end MixedFujita
