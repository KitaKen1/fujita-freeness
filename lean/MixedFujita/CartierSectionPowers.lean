/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierSectionProducts

/-!
Actual powers of global Cartier sections, including the zeroth power.
The construction uses the rational function and its regular local
coefficients directly, avoiding recursive transports of section types.
Taylor and vanishing-order statements use given completion coordinates.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u
variable {X : Scheme.{u}} [IsIntegral X]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

theorem cartierLocalEquation_pow (D : CartierDivisor X) (x : X)
    (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f) (k : ℕ) :
    (k • D).IsLocalEquationAt x (f ^ k) := by
  induction k with
  | zero => simpa using CartierDivisor.isLocalEquationAt_zero x
  | succ k ih => simpa only [succ_nsmul, pow_succ] using ih.mul hf

theorem cartierSectionPower_mem_sections (D : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) (k : ℕ) :
    (rationalFunctionsEquiv (X := X) ⊤).symm (cartierSectionRational D s ^ k) ∈
      (k • D).sections ⊤ := by
  apply CartierDivisor.mem_sections_iff_exists.mpr
  intro x hx
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt x
  refine ⟨f ^ k, cartierLocalEquation_pow D x f hf k, ?_⟩
  rw [LinearEquiv.apply_symm_apply]
  refine ⟨cartierLocalCoefficient D x f hf s ^ k, ?_⟩
  rw [map_pow, cartierLocalCoefficient_image, mul_pow]
  rfl

noncomputable def cartierSectionPower (D : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) (k : ℕ) : Γ((k • D).sheaf, ⊤) :=
  CartierDivisor.sectionMk _ (cartierSectionPower_mem_sections D s k)

theorem cartierSectionPower_rational (D : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) (k : ℕ) :
    cartierSectionRational (k • D) (cartierSectionPower D s k) =
      cartierSectionRational D s ^ k := by
  simp only [cartierSectionPower, cartierSectionRational_apply,
    CartierDivisor.sheafι_app_sectionMk, LinearEquiv.apply_symm_apply]

theorem cartierSectionPower_ne_zero (D : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) (k : ℕ) :
    cartierSectionPower D s k ≠ 0 := by
  apply (map_ne_zero_iff _ (cartierSectionRational_injective (k • D))).mp
  rw [cartierSectionPower_rational]
  exact pow_ne_zero _ ((map_ne_zero_iff _ (cartierSectionRational_injective D)).mpr hs)

theorem cartierSectionPower_localCoefficient (D : CartierDivisor X) (x : X)
    (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
    (s : Γ(D.sheaf, ⊤)) (k : ℕ) :
    cartierLocalCoefficient (k • D) x (f ^ k) (cartierLocalEquation_pow D x f hf k)
      (cartierSectionPower D s k) = cartierLocalCoefficient D x f hf s ^ k := by
  apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  rw [cartierLocalCoefficient_image, map_pow, cartierLocalCoefficient_image,
    cartierSectionPower_rational, mul_pow]
  rfl

theorem cartierSectionUnit_power (D : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) (k : ℕ) :
    cartierSectionUnit (k • D) (cartierSectionPower D s k)
      (cartierSectionPower_ne_zero D s hs k) = cartierSectionUnit D s hs ^ k := by
  apply Units.ext
  simp only [cartierSectionUnit_val, cartierSectionPower_rational]
  rfl

theorem principalCartierDivisor_power (f : X.functionFieldˣ) (k : ℕ) :
    principalCartierDivisor X (f ^ k) = k • principalCartierDivisor X f := by
  induction k with
  | zero => simp only [pow_zero, principalCartierDivisor_one, zero_nsmul]
  | succ k ih => rw [pow_succ, principalCartierDivisor_mul, ih, succ_nsmul]

theorem cartierSectionZeroDivisor_power (D : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) (k : ℕ) :
    cartierSectionZeroDivisor (k • D) (cartierSectionPower D s k)
      (cartierSectionPower_ne_zero D s hs k) = k • cartierSectionZeroDivisor D s hs := by
  rw [cartierSectionZeroDivisor, cartierSectionUnit_power D s hs k,
    principalCartierDivisor_power, cartierSectionZeroDivisor, nsmul_add]

section Coordinates
variable {K : Type u} [Field K] [X.Over (Spec (CommRingCat.of K))]
attribute [local instance] cartierBaseGlobalAlgebra cartierBaseLocalAlgebra
  cartierBaseLocalScalarTower cartierBaseSectionScalarTower

theorem cartierTaylorCoordinates_power {n : ℕ} (D : CartierDivisor X) (x : X)
    (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (s : Γ(D.sheaf, ⊤)) (k : ℕ) :
    cartierTaylorCoordinates (k • D) x (f ^ k) (cartierLocalEquation_pow D x f hf k)
      coordinates (cartierSectionPower D s k) =
        cartierTaylorCoordinates D x f hf coordinates s ^ k := by
  rw [cartierTaylorCoordinates_apply, cartierSectionPower_localCoefficient,
    map_pow, map_pow, cartierTaylorCoordinates_apply]

theorem cartierSectionVanishingOrder_power {n : ℕ} (D : CartierDivisor X)
    (x : X) [IsNoetherianRing (X.presheaf.stalk x)]
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (s : Γ(D.sheaf, ⊤)) (k : ℕ) :
    cartierSectionVanishingOrder (k • D) x (cartierSectionPower D s k) =
      k • cartierSectionVanishingOrder D x s := by
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt x
  rw [← cartierTaylorCoordinates_order_eq_vanishingOrder (k • D) x (f ^ k)
      (cartierLocalEquation_pow D x f hf k) coordinates,
    cartierTaylorCoordinates_power D x f hf coordinates,
    powerSeries_order_pow_exact, cartierTaylorCoordinates_order_eq_vanishingOrder]

end Coordinates
end MixedFujita
