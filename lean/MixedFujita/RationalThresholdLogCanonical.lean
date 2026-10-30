/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FixedDivisorSmallKltPerturbations

/-!
The all-test-model log-canonical predicate and rational perturbation endpoints.
Klt at every rational coefficient below a positive rational endpoint forces
log-canonicity at the endpoint, by the affine discrepancy formula and integer
bounds. No new common-model or SNC log-canonicity comparison is assumed.
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

variable {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]

/-- Log-canonicity tested on all actual proper smooth birational models,
with the same denominator-cleared Cartier presentation as the klt predicate. -/
def LogPairIsLogCanonical (c : EtaleChart K X n) (f : X.functionFieldˣ)
    (d : ℕ) (D : CartierDivisor X) : Prop :=
  ∀ (T : Scheme.{u}) [IsIntegral T] [IsLocallyNoetherian T] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))] (ρ : T ⟶ X) [IsDominant ρ]
    [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ)) (cT : EtaleChart K T n)
    (t : T), Order.coheight t = 1 →
      -(d : ℤ) ≤ cartierCoefficient (logDiscrepancyDivisor n ρ hρ c f d D cT etaleCharts_cover) t

/-- Every all-model klt pair is all-model log canonical. -/
theorem logPairIsKlt_logCanonical (c : EtaleChart K X n) (f : X.functionFieldˣ)
    (d : ℕ) (D : CartierDivisor X) (h : LogPairIsKlt c f d D) :
    LogPairIsLogCanonical c f d D := by
  intro T _ _ _ _ ρ _ _ _ hρ cT t ht
  exact (h T ρ hρ cT t ht).le

/-- Actual discrepancies are affine in the rational perturbation coefficient. -/
theorem logDiscrepancyDivisor_rational_perturbation {T : Scheme.{u}} [IsIntegral T]
    [T.Over (Spec (CommRingCat.of K))]
    (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d p q : ℕ)
    (D G : CartierDivisor X) (cT : EtaleChart K T n)
    (hT : iSup (fun e : EtaleChart K T n => e.U) = ⊤) :
    logDiscrepancyDivisor n ρ hρ c f (q * d) (q • D + (d * p) • G) cT hT =
      q • logDiscrepancyDivisor n ρ hρ c f d D cT hT - (d * p) • cartierPullback ρ G := by
  unfold logDiscrepancyDivisor
  rw [cartierPullback_add, cartierPullback_nsmul, cartierPullback_nsmul, smul_sub, smul_smul]
  abel

/-- An all-model klt interval with positive rational endpoint is all-model log
canonical at that endpoint. The proof uses only rational tests below it. -/
theorem logPairIsLogCanonical_at_rational_klt_endpoint
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D G : CartierDivisor X)
    (a q₀ : ℕ) (ha : 1 ≤ a) (hq₀ : 1 ≤ q₀)
    (hbelow : ∀ (p q : ℕ), 1 ≤ q → (p : ℚ) / q < (a : ℚ) / q₀ →
      LogPairIsKlt c f (q * d) (q • D + (d * p) • G)) :
    LogPairIsLogCanonical c f (q₀ * d) (q₀ • D + (d * a) • G) := by
  intro T _ _ _ _ ρ _ _ _ hρ cT t ht
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
  have hbound := htest T ρ hρ cT t ht
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

end MixedFujita
