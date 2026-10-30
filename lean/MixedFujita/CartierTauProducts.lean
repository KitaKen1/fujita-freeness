/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierFiniteProducts
public import MixedFujita.TauDegreeNormalization

/-!
The shared rational products are actual global sections of a common
integer multiple of an actual Cartier divisor A. For tau=a/b, the
r*a power has degree h*tau for h=r*j*D*b. Given completion coordinates,
the actual Taylor series has the prescribed initial exponent. This does
not establish the geometric hypotheses producing the rational targets,
the existence of the coordinates, or the exceptional-divisor geometry.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u
variable {X : Scheme.{u}} [IsIntegral X]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

noncomputable def cartierSectionCast {D E : CartierDivisor X} (h : D = E)
    (s : Γ(D.sheaf, ⊤)) : Γ(E.sheaf, ⊤) := h ▸ s

theorem cartierSectionCast_rational {D E : CartierDivisor X} (h : D = E)
    (s : Γ(D.sheaf, ⊤)) :
    cartierSectionRational E (cartierSectionCast h s) = cartierSectionRational D s := by
  subst E
  rfl

theorem cartierSectionCast_ne_zero {D E : CartierDivisor X} (h : D = E)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) : cartierSectionCast h s ≠ 0 := by
  subst E
  exact hs

theorem cartierSectionCast_localCoefficient {D E : CartierDivisor X} (h : D = E)
    (x : X) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
    (hg : E.IsLocalEquationAt x f) (s : Γ(D.sheaf, ⊤)) :
    cartierLocalCoefficient E x f hg (cartierSectionCast h s) =
      cartierLocalCoefficient D x f hf s := by
  subst E
  rfl

theorem cartierSectionCast_zeroDivisor {D E : CartierDivisor X} (h : D = E)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) :
    cartierSectionZeroDivisor E (cartierSectionCast h s) (cartierSectionCast_ne_zero h s hs) =
      cartierSectionZeroDivisor D s hs := by
  subst E
  rfl

theorem cartierSectionCast_vanishingOrder {D E : CartierDivisor X} (h : D = E)
    (x : X) (s : Γ(D.sheaf, ⊤)) :
    cartierSectionVanishingOrder E x (cartierSectionCast h s) =
      cartierSectionVanishingOrder D x s := by
  subst E
  rfl

def equalityCartierMultiplicity {ι L : Type*} [Fintype L]
    (E : Finset ι) (q : L → ι → ℚ≥0) (r a : ℕ) (l : L) (i : ι) : ℕ :=
  (r * a) * sharedRationalMultiplicity E q l i

theorem equalityCartierMultiplicity_sum {ι L : Type*} [Fintype L]
    (E : Finset ι) (q : L → ι → ℚ≥0) (r a : ℕ) (l : L)
    (hq : (∑ i ∈ E, q l i) = 1) :
    (∑ i ∈ E, equalityCartierMultiplicity E q r a l i) =
      (r * a) * sharedRationalDenominator E q := by
  simp only [equalityCartierMultiplicity, ← Finset.mul_sum,
    sharedRationalMultiplicity_sum E q l hq]

theorem equalityCartierProduct_divisor {ι L : Type*} [Fintype L]
    (E : Finset ι) (q : L → ι → ℚ≥0) (A : CartierDivisor X) (j r a : ℕ) (l : L)
    (hq : (∑ i ∈ E, q l i) = 1) :
    (∑ i ∈ E, equalityCartierMultiplicity E q r a l i • (j • A)) =
      equalitySectionDegree r j (sharedRationalDenominator E q) a • A := by
  rw [Finset.sum_nsmul_assoc, smul_smul, equalityCartierMultiplicity_sum E q r a l hq]
  congr 1
  unfold equalitySectionDegree
  ring

noncomputable def equalityCartierProduct {ι L : Type*} [Fintype L]
    (E : Finset ι) (q : L → ι → ℚ≥0) (A : CartierDivisor X) (j r a : ℕ) (l : L)
    (hq : (∑ i ∈ E, q l i) = 1) (s : ι → Γ((j • A).sheaf, ⊤)) :
    Γ((equalitySectionDegree r j (sharedRationalDenominator E q) a • A).sheaf, ⊤) :=
  cartierSectionCast (equalityCartierProduct_divisor E q A j r a l hq)
    (cartierFiniteProduct E (fun _ => j • A) (equalityCartierMultiplicity E q r a l) s)

theorem equalityCartierProduct_rational {ι L : Type*} [Fintype L]
    (E : Finset ι) (q : L → ι → ℚ≥0) (A : CartierDivisor X) (j r a : ℕ) (l : L)
    (hq : (∑ i ∈ E, q l i) = 1) (s : ι → Γ((j • A).sheaf, ⊤)) :
    cartierSectionRational _ (equalityCartierProduct E q A j r a l hq s) =
      ∏ i ∈ E, cartierSectionRational (j • A) (s i) ^ equalityCartierMultiplicity E q r a l i := by
  rw [equalityCartierProduct, cartierSectionCast_rational, cartierFiniteProduct_rational]

theorem equalityCartierProduct_ne_zero {ι L : Type*} [Fintype L]
    (E : Finset ι) (q : L → ι → ℚ≥0) (A : CartierDivisor X) (j r a : ℕ) (l : L)
    (hq : (∑ i ∈ E, q l i) = 1) (s : ι → Γ((j • A).sheaf, ⊤))
    (hs : ∀ i ∈ E, s i ≠ 0) : equalityCartierProduct E q A j r a l hq s ≠ 0 :=
  cartierSectionCast_ne_zero _ _ (cartierFiniteProduct_ne_zero E _ _ s hs)

theorem equalityCartierProduct_localEquation {ι L : Type*} [Fintype L]
    (E : Finset ι) (q : L → ι → ℚ≥0) (j r a : ℕ) (l : L)
    (hq : (∑ i ∈ E, q l i) = 1) (f : X.functionFieldˣ) :
    (∏ i ∈ E, (f ^ j) ^ equalityCartierMultiplicity E q r a l i) =
      f ^ equalitySectionDegree r j (sharedRationalDenominator E q) a := by
  rw [Finset.prod_pow_eq_pow_sum, equalityCartierMultiplicity_sum E q r a l hq,
    ← pow_mul]
  congr 1
  unfold equalitySectionDegree
  ring

theorem equalityCartierProduct_localCoefficient {ι L : Type*} [Fintype L]
    (E : Finset ι) (q : L → ι → ℚ≥0) (A : CartierDivisor X) (j r a : ℕ) (l : L)
    (hq : (∑ i ∈ E, q l i) = 1) (x : X) (f : X.functionFieldˣ)
    (hf : A.IsLocalEquationAt x f) (s : ι → Γ((j • A).sheaf, ⊤)) :
    cartierLocalCoefficient _ x
      (f ^ equalitySectionDegree r j (sharedRationalDenominator E q) a)
      (cartierLocalEquation_pow A x f hf _) (equalityCartierProduct E q A j r a l hq s) =
        ∏ i ∈ E, cartierLocalCoefficient (j • A) x (f ^ j)
          (cartierLocalEquation_pow A x f hf j) (s i) ^ equalityCartierMultiplicity E q r a l i := by
  apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  rw [cartierLocalCoefficient_image, equalityCartierProduct_rational]
  simp only [map_prod, map_pow, cartierLocalCoefficient_image, mul_pow]
  rw [Finset.prod_mul_distrib]
  congr 1
  have h := equalityCartierProduct_localEquation E q j r a l hq f
  exact_mod_cast h.symm

theorem equalityCartierProduct_zeroDivisor {ι L : Type*} [Fintype L]
    (E : Finset ι) (q : L → ι → ℚ≥0) (A : CartierDivisor X) (j r a : ℕ) (l : L)
    (hq : (∑ i ∈ E, q l i) = 1) (s : ι → Γ((j • A).sheaf, ⊤)) (hs : ∀ i, s i ≠ 0) :
    cartierSectionZeroDivisor _ (equalityCartierProduct E q A j r a l hq s)
      (equalityCartierProduct_ne_zero E q A j r a l hq s (fun i _ => hs i)) =
        ∑ i ∈ E, equalityCartierMultiplicity E q r a l i •
          cartierSectionZeroDivisor (j • A) (s i) (hs i) := by
  exact (cartierSectionCast_zeroDivisor (equalityCartierProduct_divisor E q A j r a l hq)
    (cartierFiniteProduct E (fun _ => j • A) (equalityCartierMultiplicity E q r a l) s)
    (cartierFiniteProduct_ne_zero E _ _ s (fun i _ => hs i))).trans
      (cartierSectionZeroDivisor_finiteProduct E _ _ s hs)

theorem equalityCartierProduct_degree_tau {ι L : Type*} [Fintype L]
    (E : Finset ι) (q : L → ι → ℚ≥0) (j r a : ℕ) {b : ℕ} (hb : 0 < b) :
    (equalityHeight r j (sharedRationalDenominator E q) b : ℚ) * ((a : ℚ) / b) =
      equalitySectionDegree r j (sharedRationalDenominator E q) a :=
  equalityHeight_mul_tau r j (sharedRationalDenominator E q) a hb

section Coordinates
variable {K : Type u} [Field K] [X.Over (Spec (CommRingCat.of K))]
attribute [local instance] cartierBaseGlobalAlgebra cartierBaseLocalAlgebra
  cartierBaseLocalScalarTower cartierBaseSectionScalarTower

theorem equalityCartierProduct_taylor {n : ℕ} {ι L : Type*} [Fintype L]
    (E : Finset ι) (q : L → ι → ℚ≥0) (A : CartierDivisor X) (j r a : ℕ) (l : L)
    (hq : (∑ i ∈ E, q l i) = 1) (x : X) (f : X.functionFieldˣ)
    (hf : A.IsLocalEquationAt x f)
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (s : ι → Γ((j • A).sheaf, ⊤)) :
    cartierTaylorCoordinates _ x
      (f ^ equalitySectionDegree r j (sharedRationalDenominator E q) a)
      (cartierLocalEquation_pow A x f hf _) coordinates
      (equalityCartierProduct E q A j r a l hq s) =
        ∏ i ∈ E, cartierTaylorCoordinates (j • A) x (f ^ j)
          (cartierLocalEquation_pow A x f hf j) coordinates (s i) ^
            equalityCartierMultiplicity E q r a l i := by
  rw [cartierTaylorCoordinates_apply, equalityCartierProduct_localCoefficient E q A j r a l
    hq x f hf]
  simp only [map_prod, map_pow, cartierTaylorCoordinates_apply]

theorem equalityCartierProduct_initialMonomial {n : ℕ} {ι L : Type*} [Fintype L]
    (E : Finset ι) (q : L → ι → ℚ≥0) (A : CartierDivisor X) (j r a : ℕ) (l : L)
    (hq : (∑ i ∈ E, q l i) = 1) (x : X) (f : X.functionFieldˣ)
    (hf : A.IsLocalEquationAt x f)
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (s : ι → Γ((j • A).sheaf, ⊤)) (p : ι → Fin n →₀ ℕ) (m : MonomialOrder (Fin n))
    (hp : ∀ i ∈ E, IsInitialMonomial m
      (cartierTaylorCoordinates (j • A) x (f ^ j) (cartierLocalEquation_pow A x f hf j)
        coordinates (s i)) (p i)) :
    IsInitialMonomial m (cartierTaylorCoordinates _ x
      (f ^ equalitySectionDegree r j (sharedRationalDenominator E q) a)
      (cartierLocalEquation_pow A x f hf _) coordinates
      (equalityCartierProduct E q A j r a l hq s))
      ((r * a) • ∑ i ∈ E, sharedRationalMultiplicity E q l i • p i) := by
  rw [equalityCartierProduct_taylor E q A j r a l hq x f hf coordinates]
  simpa only [equalityCartierMultiplicity, Finset.smul_sum, smul_smul] using
    initialMonomial_weighted_prod m E
      (fun i => cartierTaylorCoordinates (j • A) x (f ^ j)
        (cartierLocalEquation_pow A x f hf j) coordinates (s i)) p
      (equalityCartierMultiplicity E q r a l) hp

theorem equalityCartierProduct_vanishingOrder {n : ℕ} {ι L : Type*} [Fintype L]
    (E : Finset ι) (q : L → ι → ℚ≥0) (A : CartierDivisor X) (j r a : ℕ) (l : L)
    (hq : (∑ i ∈ E, q l i) = 1) (x : X) [IsNoetherianRing (X.presheaf.stalk x)]
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (s : ι → Γ((j • A).sheaf, ⊤)) :
    cartierSectionVanishingOrder _ x (equalityCartierProduct E q A j r a l hq s) =
      ∑ i ∈ E, equalityCartierMultiplicity E q r a l i •
        cartierSectionVanishingOrder (j • A) x (s i) := by
  rw [equalityCartierProduct, cartierSectionCast_vanishingOrder]
  exact cartierSectionVanishingOrder_finiteProduct E _ _ x coordinates s

theorem equalityCartierProduct_slice_order {n : ℕ} {ι L : Type*} [Fintype L]
    (E : Finset ι) (q : L → ι → ℚ≥0) (A : CartierDivisor X) {j r a b : ℕ}
    (l : L) (hq : (∑ i ∈ E, q l i) = 1) (x : X) (f : X.functionFieldˣ)
    (hf : A.IsLocalEquationAt x f)
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (s : ι → Γ((j • A).sheaf, ⊤)) (p : ι → Fin n →₀ ℕ)
    (hp : ∀ i ∈ E, IsInitialMonomial (MonomialOrder.degLex (σ := Fin n))
      (cartierTaylorCoordinates (j • A) x (f ^ j) (cartierLocalEquation_pow A x f hf j)
        coordinates (s i)) (p i))
    (β : Fin n →₀ ℕ) (hβ : (∑ i ∈ E, sharedRationalMultiplicity E q l i • p i) = β)
    {δ : ℚ} (k v : Fin n) (hr : 0 < r) (hj : 0 < j) (ha : 0 < a) (hb : 0 < b)
    (hslice : ∀ i, (β i : ℚ) / ((sharedRationalDenominator E q : ℚ) * j) =
      rationalSliceTarget (fun _ => (b : ℚ) / a) δ k v i) :
    (cartierTaylorCoordinates _ x
      (f ^ equalitySectionDegree r j (sharedRationalDenominator E q) a)
      (cartierLocalEquation_pow A x f hf _) coordinates
      (equalityCartierProduct E q A j r a l hq s)).order =
        (n * equalityHeight r j (sharedRationalDenominator E q) b : ℕ) := by
  have h := equalityCartierProduct_initialMonomial E q A j r a l hq x f hf
    coordinates s p (MonomialOrder.degLex (σ := Fin n)) hp
  rw [hβ] at h
  rw [degreeLex_initial_order h, Finsupp.degree_eq_sum,
    equality_slice_totalDegree β k v hr hj (sharedRationalDenominator_pos E q) ha hb hslice]

theorem equalityCartierProduct_slice_vanishingOrder {n : ℕ} {ι L : Type*} [Fintype L]
    (E : Finset ι) (q : L → ι → ℚ≥0) (A : CartierDivisor X) {j r a b : ℕ}
    (l : L) (hq : (∑ i ∈ E, q l i) = 1) (x : X) [IsNoetherianRing (X.presheaf.stalk x)]
    (f : X.functionFieldˣ) (hf : A.IsLocalEquationAt x f)
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (s : ι → Γ((j • A).sheaf, ⊤)) (p : ι → Fin n →₀ ℕ)
    (hp : ∀ i ∈ E, IsInitialMonomial (MonomialOrder.degLex (σ := Fin n))
      (cartierTaylorCoordinates (j • A) x (f ^ j) (cartierLocalEquation_pow A x f hf j)
        coordinates (s i)) (p i))
    (β : Fin n →₀ ℕ) (hβ : (∑ i ∈ E, sharedRationalMultiplicity E q l i • p i) = β)
    {δ : ℚ} (k v : Fin n) (hr : 0 < r) (hj : 0 < j) (ha : 0 < a) (hb : 0 < b)
    (hslice : ∀ i, (β i : ℚ) / ((sharedRationalDenominator E q : ℚ) * j) =
      rationalSliceTarget (fun _ => (b : ℚ) / a) δ k v i) :
    cartierSectionVanishingOrder _ x (equalityCartierProduct E q A j r a l hq s) =
      (n * equalityHeight r j (sharedRationalDenominator E q) b : ℕ) := by
  rw [← cartierTaylorCoordinates_order_eq_vanishingOrder _ x
    (f ^ equalitySectionDegree r j (sharedRationalDenominator E q) a)
    (cartierLocalEquation_pow A x f hf _) coordinates]
  exact equalityCartierProduct_slice_order E q A l hq x f hf coordinates s p hp
    β hβ k v hr hj ha hb hslice

end Coordinates
end MixedFujita
