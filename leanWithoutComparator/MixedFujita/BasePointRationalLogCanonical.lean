/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LogPairOverBasePoint
public import MixedFujita.FiniteSNCThresholdArithmetic

/-!
Rational endpoint and uniqueness arguments for base-point-filtered all-model
predicates. Every rational test is evaluated on the same relevant actual prime,
so the affine discrepancy argument preserves the base-point guard.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] {n : ℕ} {X Y : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]


variable (g : X ⟶ Y) (η : Y)

/-- Every rational klt test below a positive endpoint forces log-canonicity there. -/
theorem logPairIsLogCanonicalOverBasePoint_at_rational_klt_endpoint
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D G : CartierDivisor X)
    (a q₀ : ℕ) (ha : 1 ≤ a) (hq₀ : 1 ≤ q₀)
    (hbelow : ∀ (p q : ℕ), 1 ≤ q → (p : ℚ) / q < (a : ℚ) / q₀ →
      LogPairIsKltOverBasePoint g η c f (q * d) (q • D + (d * p) • G)) :
    LogPairIsLogCanonicalOverBasePoint g η c f (q₀ * d) (q₀ • D + (d * a) • G) := by
  intro T _ _ _ _ ρ _ _ _ hρ cT t ht hη
  rw [logDiscrepancyDivisor_rational_perturbation, cartierCoefficient_sub,
    cartierCoefficient_nsmul, cartierCoefficient_nsmul]
  let A := cartierCoefficient (logDiscrepancyDivisor n ρ hρ c f d D cT etaleCharts_cover) t
  let g := cartierCoefficient (cartierPullback ρ G) t
  obtain ⟨m, hm⟩ := exists_nat_gt ((d : ℤ) * (a : ℤ) * g)
  have hq : 1 ≤ (m + 1) * q₀ := Nat.mul_pos (by omega) (by omega)
  have hratio : ((m * a : ℕ) : ℚ) / ((m + 1) * q₀ : ℕ) < (a : ℚ) / q₀ := by
    have haQ : (0 : ℚ) < a := by exact_mod_cast ha
    have hqQ : (0 : ℚ) < q₀ := by exact_mod_cast hq₀
    apply (div_lt_div_iff₀ (by exact_mod_cast hq) hqQ).mpr
    push_cast
    nlinarith [mul_pos haQ hqQ]
  have htest := hbelow (m * a) ((m + 1) * q₀) hq hratio
  have hbound := htest T ρ hρ cT t ht hη
  rw [logDiscrepancyDivisor_rational_perturbation, cartierCoefficient_sub,
    cartierCoefficient_nsmul, cartierCoefficient_nsmul] at hbound
  change -((((m + 1) * q₀) * d : ℕ) : ℤ) <
    (((m + 1) * q₀ : ℕ) : ℤ) * A - ((d * (m * a) : ℕ) : ℤ) * g at hbound
  change -((q₀ * d : ℕ) : ℤ) ≤ (q₀ : ℤ) * A - ((d * a : ℕ) : ℤ) * g
  push_cast at hbound ⊢
  by_contra hbad
  have hneg : (q₀ : ℤ) * A - (d : ℤ) * a * g ≤ -((q₀ : ℤ) * d) - 1 := by omega
  have hmul := mul_le_mul_of_nonneg_left hneg (by omega : (0 : ℤ) ≤ (m : ℤ) + 1)
  nlinarith


/-- Exact finite endpoints at the same base point are independent of the model. -/
theorem rational_klt_overBasePoint_threshold_unique
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D G : CartierDivisor X)
    (a b q s : ℕ) (hq : 1 ≤ q) (hs : 1 ≤ s)
    (ha : ∀ (p r : ℕ), 1 ≤ r →
      (LogPairIsKltOverBasePoint g η c f (r * d) (r • D + (d * p) • G) ↔ (p : ℚ) / r < (a : ℚ) / q))
    (hb : ∀ (p r : ℕ), 1 ≤ r →
      (LogPairIsKltOverBasePoint g η c f (r * d) (r • D + (d * p) • G) ↔ (p : ℚ) / r < (b : ℚ) / s)) :
    (a : ℚ) / q = (b : ℚ) / s := by
  apply rational_threshold_eq_of_natural_tests a b q s hq hs
  intro p r hr
  exact (ha p r hr).symm.trans (hb p r hr)

end MixedFujita
