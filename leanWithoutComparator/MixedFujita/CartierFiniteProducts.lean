/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierSectionPowers
public import MixedFujita.SharedRationalProducts

/-!
Actual finite weighted products of Cartier sections on an integral scheme.
The target divisor is the actual sum of the integer multiples. Local
coefficients and given-coordinate Taylor series are the corresponding
products, including for an empty index set and zero multiplicities.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u
variable {X : Scheme.{u}} [IsIntegral X]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

theorem cartierLocalEquation_weighted_prod {ι : Type*} (E : Finset ι)
    (D : ι → CartierDivisor X) (k : ι → ℕ) (x : X) (f : ι → X.functionFieldˣ)
    (hf : ∀ i ∈ E, (D i).IsLocalEquationAt x (f i)) :
    (∑ i ∈ E, k i • D i).IsLocalEquationAt x (∏ i ∈ E, f i ^ k i) := by
  classical
  revert hf
  induction E using Finset.induction_on with
  | empty => intro _; simpa using CartierDivisor.isLocalEquationAt_zero x
  | @insert i E hi ih =>
    intro hf
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact (cartierLocalEquation_pow _ x _ (hf i (Finset.mem_insert_self i E)) _).mul
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem cartierFiniteProduct_mem_sections {ι : Type*} (E : Finset ι)
    (D : ι → CartierDivisor X) (k : ι → ℕ) (s : ∀ i, Γ((D i).sheaf, ⊤)) :
    (rationalFunctionsEquiv (X := X) ⊤).symm
      (∏ i ∈ E, cartierSectionRational (D i) (s i) ^ k i) ∈
        (∑ i ∈ E, k i • D i).sections ⊤ := by
  classical
  apply CartierDivisor.mem_sections_iff_exists.mpr
  intro x hx
  let f (i : ι) := Classical.choose ((D i).exists_isLocalEquationAt x)
  have hf (i : ι) : (D i).IsLocalEquationAt x (f i) :=
    Classical.choose_spec ((D i).exists_isLocalEquationAt x)
  refine ⟨∏ i ∈ E, f i ^ k i, cartierLocalEquation_weighted_prod E D k x f
    (fun i _ => hf i), ?_⟩
  rw [LinearEquiv.apply_symm_apply]
  refine ⟨∏ i ∈ E, cartierLocalCoefficient (D i) x (f i) (hf i) (s i) ^ k i, ?_⟩
  simp only [map_prod, map_pow, cartierLocalCoefficient_image]
  simp only [mul_pow, Units.coe_prod]
  exact Finset.prod_mul_distrib (s := E)
    (f := fun i => (f i : X.functionField) ^ k i)
    (g := fun i => cartierSectionRational (D i) (s i) ^ k i)

noncomputable def cartierFiniteProduct {ι : Type*} (E : Finset ι)
    (D : ι → CartierDivisor X) (k : ι → ℕ) (s : ∀ i, Γ((D i).sheaf, ⊤)) :
    Γ((∑ i ∈ E, k i • D i).sheaf, ⊤) :=
  CartierDivisor.sectionMk _ (cartierFiniteProduct_mem_sections E D k s)

theorem cartierFiniteProduct_rational {ι : Type*} (E : Finset ι)
    (D : ι → CartierDivisor X) (k : ι → ℕ) (s : ∀ i, Γ((D i).sheaf, ⊤)) :
    cartierSectionRational (∑ i ∈ E, k i • D i) (cartierFiniteProduct E D k s) =
      ∏ i ∈ E, cartierSectionRational (D i) (s i) ^ k i := by
  simp only [cartierFiniteProduct, cartierSectionRational_apply,
    CartierDivisor.sheafι_app_sectionMk, LinearEquiv.apply_symm_apply]

theorem cartierFiniteProduct_ne_zero {ι : Type*} (E : Finset ι)
    (D : ι → CartierDivisor X) (k : ι → ℕ) (s : ∀ i, Γ((D i).sheaf, ⊤))
    (hs : ∀ i ∈ E, s i ≠ 0) : cartierFiniteProduct E D k s ≠ 0 := by
  apply (map_ne_zero_iff _ (cartierSectionRational_injective _)).mp
  rw [cartierFiniteProduct_rational]
  exact Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _
    ((map_ne_zero_iff _ (cartierSectionRational_injective _)).mpr (hs i hi))

theorem cartierFiniteProduct_localCoefficient {ι : Type*} (E : Finset ι)
    (D : ι → CartierDivisor X) (k : ι → ℕ) (x : X) (f : ι → X.functionFieldˣ)
    (hf : ∀ i, (D i).IsLocalEquationAt x (f i))
    (s : ∀ i, Γ((D i).sheaf, ⊤)) :
    cartierLocalCoefficient (∑ i ∈ E, k i • D i) x (∏ i ∈ E, f i ^ k i)
      (cartierLocalEquation_weighted_prod E D k x f (fun i _ => hf i))
      (cartierFiniteProduct E D k s) =
        ∏ i ∈ E, cartierLocalCoefficient (D i) x (f i) (hf i) (s i) ^ k i := by
  classical
  apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  simp only [cartierLocalCoefficient_image, cartierFiniteProduct_rational,
    map_prod, map_pow]
  simp only [mul_pow, Units.coe_prod]
  exact (Finset.prod_mul_distrib (s := E)
    (f := fun i => (f i : X.functionField) ^ k i)
    (g := fun i => cartierSectionRational (D i) (s i) ^ k i)).symm

theorem cartierSectionUnit_finiteProduct {ι : Type*} (E : Finset ι)
    (D : ι → CartierDivisor X) (k : ι → ℕ) (s : ∀ i, Γ((D i).sheaf, ⊤))
    (hs : ∀ i, s i ≠ 0) :
    cartierSectionUnit (∑ i ∈ E, k i • D i) (cartierFiniteProduct E D k s)
      (cartierFiniteProduct_ne_zero E D k s (fun i _ => hs i)) =
        ∏ i ∈ E, cartierSectionUnit (D i) (s i) (hs i) ^ k i := by
  apply Units.ext
  simp [cartierSectionUnit_val, cartierFiniteProduct_rational]

theorem principalCartierDivisor_weighted_prod {ι : Type*} (E : Finset ι)
    (f : ι → X.functionFieldˣ) (k : ι → ℕ) :
    principalCartierDivisor X (∏ i ∈ E, f i ^ k i) =
      ∑ i ∈ E, k i • principalCartierDivisor X (f i) := by
  classical
  induction E using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Finset.sum_empty, principalCartierDivisor_one]
  | @insert i E hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, principalCartierDivisor_mul,
      principalCartierDivisor_power, ih]

theorem cartierSectionZeroDivisor_finiteProduct {ι : Type*} (E : Finset ι)
    (D : ι → CartierDivisor X) (k : ι → ℕ) (s : ∀ i, Γ((D i).sheaf, ⊤))
    (hs : ∀ i, s i ≠ 0) :
    cartierSectionZeroDivisor (∑ i ∈ E, k i • D i) (cartierFiniteProduct E D k s)
      (cartierFiniteProduct_ne_zero E D k s (fun i _ => hs i)) =
        ∑ i ∈ E, k i • cartierSectionZeroDivisor (D i) (s i) (hs i) := by
  rw [cartierSectionZeroDivisor, cartierSectionUnit_finiteProduct E D k s hs,
    principalCartierDivisor_weighted_prod, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [cartierSectionZeroDivisor, nsmul_add]

section Coordinates
variable {K : Type u} [Field K] [X.Over (Spec (CommRingCat.of K))]
attribute [local instance] cartierBaseGlobalAlgebra cartierBaseLocalAlgebra
  cartierBaseLocalScalarTower cartierBaseSectionScalarTower

theorem cartierTaylorCoordinates_finiteProduct {n : ℕ} {ι : Type*} (E : Finset ι)
    (D : ι → CartierDivisor X) (k : ι → ℕ) (x : X) (f : ι → X.functionFieldˣ)
    (hf : ∀ i, (D i).IsLocalEquationAt x (f i))
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (s : ∀ i, Γ((D i).sheaf, ⊤)) :
    cartierTaylorCoordinates (∑ i ∈ E, k i • D i) x (∏ i ∈ E, f i ^ k i)
      (cartierLocalEquation_weighted_prod E D k x f (fun i _ => hf i)) coordinates
      (cartierFiniteProduct E D k s) =
        ∏ i ∈ E, cartierTaylorCoordinates (D i) x (f i) (hf i) coordinates (s i) ^ k i := by
  rw [cartierTaylorCoordinates_apply, cartierFiniteProduct_localCoefficient E D k x f hf]
  simp only [map_prod, map_pow, cartierTaylorCoordinates_apply]

omit [X.Over (Spec (CommRingCat.of K))] [IsIntegral X] in
theorem powerSeries_order_weighted_prod {n : ℕ} {ι : Type*} (E : Finset ι)
    (φ : ι → MvPowerSeries (Fin n) K) (k : ι → ℕ) :
    (∏ i ∈ E, φ i ^ k i).order = ∑ i ∈ E, k i • (φ i).order := by
  classical
  induction E using Finset.induction_on with
  | empty =>
    simpa only [Finset.prod_empty, Finset.sum_empty, pow_zero, zero_nsmul] using
      powerSeries_order_pow_exact (1 : MvPowerSeries (Fin n) K) 0
  | @insert i E hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, powerSeries_order_mul_exact,
      powerSeries_order_pow_exact, ih]

theorem cartierSectionVanishingOrder_finiteProduct {n : ℕ} {ι : Type*} (E : Finset ι)
    (D : ι → CartierDivisor X) (k : ι → ℕ) (x : X)
    [IsNoetherianRing (X.presheaf.stalk x)]
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (s : ∀ i, Γ((D i).sheaf, ⊤)) :
    cartierSectionVanishingOrder (∑ i ∈ E, k i • D i) x (cartierFiniteProduct E D k s) =
      ∑ i ∈ E, k i • cartierSectionVanishingOrder (D i) x (s i) := by
  classical
  let f (i : ι) := Classical.choose ((D i).exists_isLocalEquationAt x)
  have hf (i : ι) : (D i).IsLocalEquationAt x (f i) :=
    Classical.choose_spec ((D i).exists_isLocalEquationAt x)
  rw [← cartierTaylorCoordinates_order_eq_vanishingOrder _ x _
      (cartierLocalEquation_weighted_prod E D k x f (fun i _ => hf i)) coordinates,
    cartierTaylorCoordinates_finiteProduct E D k x f hf coordinates,
    powerSeries_order_weighted_prod]
  simp only [cartierTaylorCoordinates_order_eq_vanishingOrder]

end Coordinates
end MixedFujita
