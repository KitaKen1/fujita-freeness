/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierTauProducts
public import MixedFujita.TaylorSemigroup

/-!
Actual sections of O(j*A), with the compatible local equations f^j,
give a graded family of Taylor maps for any given completion coordinates.
Actual section multiplication proves closure of their images. Initial
exponent counts and the existing slice-growth theorem are then instantiated
for these actual section spaces, rather than abstract graded vector spaces.
Coordinate existence, finite dimensionality from projectivity, and the
geometric uniform lower bound for central slices remain explicit inputs.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme
open scoped Pointwise

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u
variable {X : Scheme.{u}} [IsIntegral X]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

noncomputable def cartierGradedSectionProduct (A : CartierDivisor X) (j h : ℕ)
    (s : Γ((j • A).sheaf, ⊤)) (t : Γ((h • A).sheaf, ⊤)) :
    Γ(((j + h) • A).sheaf, ⊤) :=
  cartierSectionCast (by rw [add_nsmul]) (cartierSectionProduct (j • A) (h • A) s t)

theorem cartierGradedSectionProduct_rational (A : CartierDivisor X) (j h : ℕ)
    (s : Γ((j • A).sheaf, ⊤)) (t : Γ((h • A).sheaf, ⊤)) :
    cartierSectionRational ((j + h) • A) (cartierGradedSectionProduct A j h s t) =
      cartierSectionRational (j • A) s * cartierSectionRational (h • A) t := by
  rw [cartierGradedSectionProduct, cartierSectionCast_rational, cartierSectionProduct_rational]

theorem cartierGradedSectionProduct_localCoefficient (A : CartierDivisor X) (x : X)
    (f : X.functionFieldˣ) (hf : A.IsLocalEquationAt x f) (j h : ℕ)
    (s : Γ((j • A).sheaf, ⊤)) (t : Γ((h • A).sheaf, ⊤)) :
    cartierLocalCoefficient ((j + h) • A) x (f ^ (j + h))
      (cartierLocalEquation_pow A x f hf _) (cartierGradedSectionProduct A j h s t) =
        cartierLocalCoefficient (j • A) x (f ^ j) (cartierLocalEquation_pow A x f hf j) s *
          cartierLocalCoefficient (h • A) x (f ^ h) (cartierLocalEquation_pow A x f hf h) t := by
  apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  rw [map_mul, cartierLocalCoefficient_image, cartierLocalCoefficient_image,
    cartierLocalCoefficient_image, cartierGradedSectionProduct_rational]
  change (f : X.functionField) ^ (j + h) *
    (cartierSectionRational (j • A) s * cartierSectionRational (h • A) t) =
      ((f : X.functionField) ^ j * cartierSectionRational (j • A) s) *
        ((f : X.functionField) ^ h * cartierSectionRational (h • A) t)
  rw [pow_add]
  ring

section Coordinates
variable {K : Type u} [Field K] [X.Over (Spec (CommRingCat.of K))]
attribute [local instance] cartierBaseGlobalAlgebra cartierBaseLocalAlgebra
  cartierBaseLocalScalarTower cartierBaseSectionScalarTower

noncomputable def cartierGradedTaylor {σ : Type*} (A : CartierDivisor X) (x : X)
    (f : X.functionFieldˣ) (hf : A.IsLocalEquationAt x f)
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries σ K) (j : ℕ) :
    Γ((j • A).sheaf, ⊤) →ₗ[K] MvPowerSeries σ K :=
  coordinates.toLinearMap.comp
    (cartierBaseCompletedCoefficient (j • A) x (f ^ j) (cartierLocalEquation_pow A x f hf j))

theorem cartierGradedTaylor_apply {σ : Type*} (A : CartierDivisor X) (x : X)
    (f : X.functionFieldˣ) (hf : A.IsLocalEquationAt x f)
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries σ K) (j : ℕ) (s : Γ((j • A).sheaf, ⊤)) :
    cartierGradedTaylor A x f hf coordinates j s =
      coordinates (algebraMap (X.presheaf.stalk x)
        (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (X.presheaf.stalk x))
        (cartierLocalCoefficient (j • A) x (f ^ j) (cartierLocalEquation_pow A x f hf j) s)) := rfl

theorem cartierGradedTaylor_fin_eq {n : ℕ} (A : CartierDivisor X) (x : X)
    (f : X.functionFieldˣ) (hf : A.IsLocalEquationAt x f)
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K) (j : ℕ) :
    cartierGradedTaylor A x f hf coordinates j =
      cartierTaylorCoordinates (j • A) x (f ^ j) (cartierLocalEquation_pow A x f hf j)
        coordinates := rfl

theorem cartierGradedTaylor_injective {σ : Type*} (A : CartierDivisor X) (x : X)
    [IsNoetherianRing (X.presheaf.stalk x)]
    (f : X.functionFieldˣ) (hf : A.IsLocalEquationAt x f)
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries σ K) (j : ℕ) :
    Function.Injective (cartierGradedTaylor A x f hf coordinates j) :=
  coordinates.injective.comp (cartierCompletedLocalCoefficient_injective _ x _ _)

theorem cartierGradedTaylor_product {σ : Type*} (A : CartierDivisor X) (x : X)
    (f : X.functionFieldˣ) (hf : A.IsLocalEquationAt x f)
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries σ K) (j h : ℕ)
    (s : Γ((j • A).sheaf, ⊤)) (t : Γ((h • A).sheaf, ⊤)) :
    cartierGradedTaylor A x f hf coordinates (j + h) (cartierGradedSectionProduct A j h s t) =
      cartierGradedTaylor A x f hf coordinates j s *
        cartierGradedTaylor A x f hf coordinates h t := by
  rw [cartierGradedTaylor_apply, cartierGradedSectionProduct_localCoefficient A x f hf j h s t,
    map_mul, map_mul, cartierGradedTaylor_apply, cartierGradedTaylor_apply]

section FiniteSections
variable (A : CartierDivisor X) (x : X) (f : X.functionFieldˣ) (hf : A.IsLocalEquationAt x f)
  [∀ j : ℕ, FiniteDimensional K Γ((j • A).sheaf, ⊤)]

noncomputable def cartierGradedInitialExponents {σ : Type*} (m : MonomialOrder σ)
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries σ K) (j : ℕ) : Finset (σ →₀ ℕ) :=
  initialMonomialFinset m (LinearMap.range (cartierGradedTaylor A x f hf coordinates j))

theorem cartierGradedInitialExponents_mem {σ : Type*} (m : MonomialOrder σ)
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries σ K) (j : ℕ) (p : σ →₀ ℕ) :
    p ∈ cartierGradedInitialExponents A x f hf m coordinates j ↔
      ∃ s : Γ((j • A).sheaf, ⊤), IsInitialMonomial m
        (cartierGradedTaylor A x f hf coordinates j s) p := by
  rw [cartierGradedInitialExponents, mem_initialMonomialFinset]
  constructor
  · rintro ⟨φ, ⟨s, rfl⟩, hp⟩
    exact ⟨s, hp⟩
  · rintro ⟨s, hp⟩
    exact ⟨_, ⟨s, rfl⟩, hp⟩

theorem cartierGradedInitialExponents_card {σ : Type*} [IsNoetherianRing (X.presheaf.stalk x)]
    (m : MonomialOrder σ)
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries σ K) (j : ℕ) :
    (cartierGradedInitialExponents A x f hf m coordinates j).card =
      Module.finrank K Γ((j • A).sheaf, ⊤) := by
  rw [cartierGradedInitialExponents, initialMonomialFinset_card,
    LinearMap.finrank_range_of_inj (cartierGradedTaylor_injective A x f hf coordinates j)]

theorem cartierGradedInitialExponents_add_subset {σ : Type*} [DecidableEq σ]
    (m : MonomialOrder σ)
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries σ K) (j h : ℕ) :
    cartierGradedInitialExponents A x f hf m coordinates j +
      cartierGradedInitialExponents A x f hf m coordinates h ⊆
        cartierGradedInitialExponents A x f hf m coordinates (j + h) := by
  apply initialMonomialFinset_add_subset
  intro φ hφ ψ hψ
  obtain ⟨s, rfl⟩ := hφ
  obtain ⟨t, rfl⟩ := hψ
  exact ⟨cartierGradedSectionProduct A j h s t,
    cartierGradedTaylor_product A x f hf coordinates j h s t⟩

noncomputable def cartierTaylorExponentPoints {r d : ℕ}
    (m : MonomialOrder (Fin r ⊕ Fin (d + 1)))
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin r ⊕ Fin (d + 1)) K) (j : ℕ) :
    Finset ((Fin r → ℤ) × (Fin (d + 1) → ℤ)) :=
  taylorExponentPoints m (cartierGradedTaylor A x f hf coordinates) j

theorem cartierTaylorExponentPoints_card {r d : ℕ} [IsNoetherianRing (X.presheaf.stalk x)]
    (m : MonomialOrder (Fin r ⊕ Fin (d + 1)))
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin r ⊕ Fin (d + 1)) K) (j : ℕ) :
    (cartierTaylorExponentPoints A x f hf m coordinates j).card =
      Module.finrank K Γ((j • A).sheaf, ⊤) :=
  taylorExponentPoints_card m _ j (cartierGradedTaylor_injective A x f hf coordinates j)

theorem cartierTaylorExponentPoints_semigroup {r d : ℕ}
    (m : MonomialOrder (Fin r ⊕ Fin (d + 1)))
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin r ⊕ Fin (d + 1)) K) :
    GradedExponentSemigroup (cartierTaylorExponentPoints A x f hf m coordinates) :=
  taylorExponentPoints_semigroup m _ (cartierGradedSectionProduct A)
    (cartierGradedTaylor_product A x f hf coordinates)

theorem cartier_weightedSliceMoment_growth {r d : ℕ}
    (m : MonomialOrder (Fin r ⊕ Fin (d + 1)))
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin r ⊕ Fin (d + 1)) K)
    (H h₀ : ℕ)
    (hcube : binaryVectors (d + 1) ⊆ exponentSlice
      (cartierTaylorExponentPoints A x f hf m coordinates) h₀ 0)
    {lam C : ℝ} (hlam : 0 ≤ lam) (hH : 0 < lam * H - C)
    (hlower : ∀ q ≥ H, lam * q - C ≤ sliceRadius (exponentSlice
      (cartierTaylorExponentPoints A x f hf m coordinates) q 0))
    (j h : ℕ) (w : (Fin r → ℤ) → ℝ)
    (hh : H + h₀ ≤ h) (hr : 0 ≤ lam * h - (C + lam * h₀))
    (hw : ∀ p, 0 ≤ w p) :
    weightedSliceMoment (cartierTaylorExponentPoints A x f hf m coordinates) j w +
      (d + 2 : ℝ) * (lam * h - (C + lam * h₀)) *
        weightedSliceCount (cartierTaylorExponentPoints A x f hf m coordinates) j w ≤
      weightedSliceMoment (cartierTaylorExponentPoints A x f hf m coordinates) (j + h) w :=
  taylor_weightedSliceMoment_growth m _ (cartierGradedSectionProduct A)
    (cartierGradedTaylor_product A x f hf coordinates)
    H h₀ hcube hlam hH hlower j h w hh hr hw

end FiniteSections
end Coordinates
end MixedFujita
