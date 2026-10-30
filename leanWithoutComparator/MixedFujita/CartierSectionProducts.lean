/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierVanishingOrder

/-!
Construct actual products of global sections of O_X(D) and O_X(E), as
sections of O_X(D+E). Rational functions and compatible local coefficients
multiply exactly; their effective zero divisors add. The Taylor map built
from a given completion-coordinate isomorphism respects this actual
product. On Noetherian stalks the intrinsic section vanishing orders add.
Coordinate existence and the blow-up geometry remain unproved.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

variable {X : Scheme.{u}} [IsIntegral X]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

theorem cartierSectionProduct_mem_sections (D E : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) (t : Γ(E.sheaf, ⊤)) :
    (rationalFunctionsEquiv (X := X) ⊤).symm
      (cartierSectionRational D s * cartierSectionRational E t) ∈ (D + E).sections ⊤ := by
  apply CartierDivisor.mem_sections_iff_exists.mpr
  intro x hx
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt x
  obtain ⟨g, hg⟩ := E.exists_isLocalEquationAt x
  refine ⟨f * g, hf.mul hg, ?_⟩
  rw [LinearEquiv.apply_symm_apply, Units.val_mul]
  refine ⟨cartierLocalCoefficient D x f hf s * cartierLocalCoefficient E x g hg t, ?_⟩
  rw [map_mul, cartierLocalCoefficient_image, cartierLocalCoefficient_image]
  ring

noncomputable def cartierSectionProduct (D E : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) (t : Γ(E.sheaf, ⊤)) : Γ((D + E).sheaf, ⊤) :=
  CartierDivisor.sectionMk _ (cartierSectionProduct_mem_sections D E s t)

theorem cartierSectionProduct_rational (D E : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) (t : Γ(E.sheaf, ⊤)) :
    cartierSectionRational (D + E) (cartierSectionProduct D E s t) =
      cartierSectionRational D s * cartierSectionRational E t := by
  simp only [cartierSectionProduct, cartierSectionRational_apply,
    CartierDivisor.sheafι_app_sectionMk, LinearEquiv.apply_symm_apply]

theorem cartierSectionProduct_ne_zero (D E : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) (t : Γ(E.sheaf, ⊤)) (hs : s ≠ 0) (ht : t ≠ 0) :
    cartierSectionProduct D E s t ≠ 0 := by
  apply (map_ne_zero_iff _ (cartierSectionRational_injective (D + E))).mp
  rw [cartierSectionProduct_rational]
  exact mul_ne_zero
    ((map_ne_zero_iff _ (cartierSectionRational_injective D)).mpr hs)
    ((map_ne_zero_iff _ (cartierSectionRational_injective E)).mpr ht)

theorem cartierSectionProduct_localCoefficient (D E : CartierDivisor X)
    (x : X) (f g : X.functionFieldˣ)
    (hf : D.IsLocalEquationAt x f) (hg : E.IsLocalEquationAt x g)
    (s : Γ(D.sheaf, ⊤)) (t : Γ(E.sheaf, ⊤)) :
    cartierLocalCoefficient (D + E) x (f * g) (hf.mul hg) (cartierSectionProduct D E s t) =
      cartierLocalCoefficient D x f hf s * cartierLocalCoefficient E x g hg t := by
  apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  rw [map_mul, cartierLocalCoefficient_image, cartierLocalCoefficient_image,
    cartierLocalCoefficient_image, cartierSectionProduct_rational, Units.val_mul]
  ring

theorem cartierSectionUnit_product (D E : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) (t : Γ(E.sheaf, ⊤)) (hs : s ≠ 0) (ht : t ≠ 0) :
    cartierSectionUnit (D + E) (cartierSectionProduct D E s t)
      (cartierSectionProduct_ne_zero D E s t hs ht) =
    cartierSectionUnit D s hs * cartierSectionUnit E t ht := by
  apply Units.ext
  simp only [cartierSectionUnit_val, Units.val_mul, cartierSectionProduct_rational]

theorem cartierSectionZeroDivisor_product (D E : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) (t : Γ(E.sheaf, ⊤)) (hs : s ≠ 0) (ht : t ≠ 0) :
    cartierSectionZeroDivisor (D + E) (cartierSectionProduct D E s t)
      (cartierSectionProduct_ne_zero D E s t hs ht) =
    cartierSectionZeroDivisor D s hs + cartierSectionZeroDivisor E t ht := by
  rw [cartierSectionZeroDivisor, cartierSectionUnit_product D E s t hs ht,
    principalCartierDivisor_mul, cartierSectionZeroDivisor, cartierSectionZeroDivisor]
  abel_nf

section Coordinates

variable {K : Type u} [Field K] [X.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierBaseGlobalAlgebra cartierBaseLocalAlgebra
  cartierBaseLocalScalarTower cartierBaseSectionScalarTower

theorem cartierTaylorCoordinates_product {n : ℕ} (D E : CartierDivisor X)
    (x : X) (f g : X.functionFieldˣ)
    (hf : D.IsLocalEquationAt x f) (hg : E.IsLocalEquationAt x g)
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (s : Γ(D.sheaf, ⊤)) (t : Γ(E.sheaf, ⊤)) :
    cartierTaylorCoordinates (D + E) x (f * g) (hf.mul hg) coordinates
      (cartierSectionProduct D E s t) =
    cartierTaylorCoordinates D x f hf coordinates s *
      cartierTaylorCoordinates E x g hg coordinates t := by
  rw [cartierTaylorCoordinates_apply, cartierSectionProduct_localCoefficient,
    map_mul, map_mul, cartierTaylorCoordinates_apply, cartierTaylorCoordinates_apply]

omit [X.Over (Spec (CommRingCat.of K))] [IsIntegral X] in
theorem powerSeries_order_mul_exact {n : ℕ}
    (φ ψ : MvPowerSeries (Fin n) K) : (φ * ψ).order = φ.order + ψ.order := by
  by_cases hφ : φ = 0
  · simp [hφ]
  by_cases hψ : ψ = 0
  · simp [hψ]
  obtain ⟨p, hp⟩ := exists_initialMonomial (MonomialOrder.degLex (σ := Fin n)) hφ
  obtain ⟨q, hq⟩ := exists_initialMonomial (MonomialOrder.degLex (σ := Fin n)) hψ
  rw [degreeLex_initial_order (initialMonomial_mul _ hp hq),
    degreeLex_initial_order hp, degreeLex_initial_order hq, map_add, Nat.cast_add]

omit [X.Over (Spec (CommRingCat.of K))] [IsIntegral X] in
theorem powerSeries_order_pow_exact {n : ℕ} (φ : MvPowerSeries (Fin n) K) (d : ℕ) :
    (φ ^ d).order = d • φ.order := by
  induction d with
  | zero =>
    simp only [pow_zero, zero_nsmul]
    apply le_antisymm
    · have h : MvPowerSeries.coeff (0 : Fin n →₀ ℕ) (1 : MvPowerSeries (Fin n) K) ≠ 0 :=
        by simp
      simpa only [map_zero, Nat.cast_zero] using MvPowerSeries.order_le h
    · exact zero_le
  | succ d hd => rw [pow_succ, powerSeries_order_mul_exact, hd, succ_nsmul]

theorem cartierSectionVanishingOrder_product {n : ℕ} (D E : CartierDivisor X)
    (x : X) [IsNoetherianRing (X.presheaf.stalk x)]
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (s : Γ(D.sheaf, ⊤)) (t : Γ(E.sheaf, ⊤)) :
    cartierSectionVanishingOrder (D + E) x (cartierSectionProduct D E s t) =
      cartierSectionVanishingOrder D x s + cartierSectionVanishingOrder E x t := by
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt x
  obtain ⟨g, hg⟩ := E.exists_isLocalEquationAt x
  rw [← cartierTaylorCoordinates_order_eq_vanishingOrder (D + E) x (f * g) (hf.mul hg)
    coordinates, cartierTaylorCoordinates_product D E x f g hf hg coordinates,
    powerSeries_order_mul_exact,
    cartierTaylorCoordinates_order_eq_vanishingOrder,
    cartierTaylorCoordinates_order_eq_vanishingOrder]

end Coordinates

end MixedFujita
