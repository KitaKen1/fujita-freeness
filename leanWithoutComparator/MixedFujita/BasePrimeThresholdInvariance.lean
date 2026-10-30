/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.BasePrimeCartierCoefficientInvariance
public import MixedFujita.BasePointRationalLogCanonical

/-!
Rational pullback perturbations at a normal base prime depend only on the base
Cartier coefficient there. This proves local-uniformizer independence of the
all-model klt/lc tests and every finite exact rational threshold, without
presuming a global discriminant divisor.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] {n : ℕ} {X Y : Scheme.{u}}
  [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
  [X.Over (Spec (CommRingCat.of K))]
  (g : X ⟶ Y) [IsDominant g] (η : CodimensionOnePoint Y)
  [IsIntegrallyClosed (Y.presheaf.stalk (η : Y))]
  (H₁ H₂ : CartierDivisor Y)
  (hH : cartierCoefficient H₁ (η : Y) = cartierCoefficient H₂ (η : Y))

include hH

/-- Actual discrepancy coefficients of the two perturbations agree at every relevant prime. -/
theorem logDiscrepancy_rational_pullback_coefficient_eq_of_base_prime_coefficient_eq
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X) (p q : ℕ)
    {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T]
    [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (cT : EtaleChart K T n) (t : CodimensionOnePoint T)
    (htη : (η : Y) ∈ closure ({(ρ ≫ g) (t : T)} : Set Y)) :
    cartierCoefficient (logDiscrepancyDivisor n ρ hρ c f (q * d)
      (q • D + (d * p) • cartierPullback g H₁) cT etaleCharts_cover) (t : T) =
    cartierCoefficient (logDiscrepancyDivisor n ρ hρ c f (q * d)
      (q • D + (d * p) • cartierPullback g H₂) cT etaleCharts_cover) (t : T) := by
  simp only [logDiscrepancyDivisor_rational_perturbation, cartierCoefficient_sub,
    cartierCoefficient_nsmul, ← cartierPullback_comp]
  rw [cartierCoefficient_pullback_eq_of_base_prime_coefficient_eq (ρ ≫ g) η H₁ H₂ hH t htη]

theorem logPairIsKltOverBasePoint_rational_pullback_iff_of_base_prime_coefficient_eq
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X) (p q : ℕ) :
    LogPairIsKltOverBasePoint g (η : Y) c f (q * d)
      (q • D + (d * p) • cartierPullback g H₁) ↔
    LogPairIsKltOverBasePoint g (η : Y) c f (q * d)
      (q • D + (d * p) • cartierPullback g H₂) := by
  constructor
  · intro h T _ _ _ _ ρ _ _ _ hρ cT t ht htη
    rw [← logDiscrepancy_rational_pullback_coefficient_eq_of_base_prime_coefficient_eq
      g η H₁ H₂ hH c f d D p q ρ hρ cT ⟨t, ht⟩ htη]
    exact h T ρ hρ cT t ht htη
  · intro h T _ _ _ _ ρ _ _ _ hρ cT t ht htη
    rw [logDiscrepancy_rational_pullback_coefficient_eq_of_base_prime_coefficient_eq
      g η H₁ H₂ hH c f d D p q ρ hρ cT ⟨t, ht⟩ htη]
    exact h T ρ hρ cT t ht htη

theorem logPairIsLogCanonicalOverBasePoint_rational_pullback_iff_of_base_prime_coefficient_eq
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X) (p q : ℕ) :
    LogPairIsLogCanonicalOverBasePoint g (η : Y) c f (q * d)
      (q • D + (d * p) • cartierPullback g H₁) ↔
    LogPairIsLogCanonicalOverBasePoint g (η : Y) c f (q * d)
      (q • D + (d * p) • cartierPullback g H₂) := by
  constructor
  · intro h T _ _ _ _ ρ _ _ _ hρ cT t ht htη
    rw [← logDiscrepancy_rational_pullback_coefficient_eq_of_base_prime_coefficient_eq
      g η H₁ H₂ hH c f d D p q ρ hρ cT ⟨t, ht⟩ htη]
    exact h T ρ hρ cT t ht htη
  · intro h T _ _ _ _ ρ _ _ _ hρ cT t ht htη
    rw [logDiscrepancy_rational_pullback_coefficient_eq_of_base_prime_coefficient_eq
      g η H₁ H₂ hH c f d D p q ρ hρ cT ⟨t, ht⟩ htη]
    exact h T ρ hρ cT t ht htη

/-- Equal base-prime coefficients give the same exact finite rational threshold. -/
theorem rational_klt_base_prime_threshold_eq_of_base_prime_coefficient_eq
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X)
    (a b q s : ℕ) (hq : 1 ≤ q) (hs : 1 ≤ s)
    (ha : ∀ (p r : ℕ), 1 ≤ r →
      (LogPairIsKltOverBasePoint g (η : Y) c f (r * d)
        (r • D + (d * p) • cartierPullback g H₁) ↔ (p : ℚ) / r < (a : ℚ) / q))
    (hb : ∀ (p r : ℕ), 1 ≤ r →
      (LogPairIsKltOverBasePoint g (η : Y) c f (r * d)
        (r • D + (d * p) • cartierPullback g H₂) ↔ (p : ℚ) / r < (b : ℚ) / s)) :
    (a : ℚ) / q = (b : ℚ) / s := by
  apply rational_threshold_eq_of_natural_tests a b q s hq hs
  intro p r hr
  exact (ha p r hr).symm.trans
    ((logPairIsKltOverBasePoint_rational_pullback_iff_of_base_prime_coefficient_eq
      g η H₁ H₂ hH c f d D p r).trans (hb p r hr))

end MixedFujita
