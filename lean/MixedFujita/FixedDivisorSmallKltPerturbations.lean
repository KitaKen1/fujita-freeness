/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ArbitrarilySmallKltPerturbations

/-!
A fixed actual Cartier divisor admits an arbitrarily small rational klt
perturbation, given an actual proper smooth model with joint SNC support for
its pullback and the original crepant boundary. No global generation of this
fixed divisor is required. Finite integer coefficients supply an explicit
denominator bound; the all-test-model klt conclusion uses local SNC descent.
Existence of the joint SNC model remains explicit.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme
open scoped BigOperators

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- A finite signed coefficient list supplies a sufficiently large denominator
with both the strict coefficient bounds and any prescribed positive rational margin. -/
theorem finite_integer_coefficients_small_scaling {r : ℕ} (b g : Fin r → ℤ)
    (d : ℕ) (hd : 1 ≤ d) (hb : ∀ i, b i < (d : ℤ)) (ε : ℚ) (hε : 0 < ε) :
    ∃ m : ℕ, 2 ≤ m ∧ 0 < 1 / ((m * d : ℕ) : ℚ) ∧
      1 / ((m * d : ℕ) : ℚ) < ε ∧
      (∀ i, (m : ℤ) * b i + g i < ((m * d : ℕ) : ℤ)) := by
  classical
  let M := ∑ i, (g i).natAbs
  obtain ⟨j, hj⟩ := exists_nat_gt (1 / ε)
  let m := j + M + 2
  have hm : 2 ≤ m := by omega
  have hmd : m ≤ m * d := by simpa using Nat.mul_le_mul_left m hd
  have hmdpos : (0 : ℚ) < (m * d : ℕ) := by exact_mod_cast (by omega : 0 < m * d)
  have hlt : 1 / ε < ((m * d : ℕ) : ℚ) := by
    have hjm : (j : ℚ) < m := by
      have hM0 : (0 : ℚ) ≤ M := Nat.cast_nonneg M
      dsimp [m]
      push_cast
      linarith
    exact (hj.trans hjm).trans_le (by exact_mod_cast hmd)
  refine ⟨m, hm, div_pos zero_lt_one hmdpos, ?_, ?_⟩
  · apply (div_lt_iff₀ hmdpos).mpr
    simpa only [mul_comm] using (div_lt_iff₀ hε).mp hlt
  · intro i
    have hgi : (g i).natAbs ≤ M := by
      change (g i).natAbs ≤ ∑ j : Fin r, (g j).natAbs
      exact Finset.single_le_sum (fun j _ => Nat.zero_le (g j).natAbs) (Finset.mem_univ i)
    have habs : g i ≤ ((g i).natAbs : ℤ) := by
      simpa only [Int.natCast_natAbs] using le_abs_self (g i)
    have hgi' : g i ≤ (M : ℤ) := habs.trans (by exact_mod_cast hgi)
    have hMm : (M : ℤ) < m := by dsimp [m]; push_cast; omega
    have hgap : b i + 1 ≤ (d : ℤ) := by have := hb i; omega
    have hmul := mul_le_mul_of_nonneg_left hgap (Nat.cast_nonneg m : (0 : ℤ) ≤ m)
    rw [Nat.cast_mul]
    nlinarith

variable {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

/-- A fixed actual Cartier divisor has an arbitrarily small all-model klt perturbation
given joint SNC support on the original actual proper smooth model. -/
theorem logPairIsKlt_exists_arbitrarily_small_fixed_divisor_perturbation
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D G : CartierDivisor X) (hklt : LogPairIsKlt c f d D) (cT : EtaleChart K T n)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) = 0)
    (hGsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback ρ G) (t : T) = 0)
    (ε : ℚ) (hε : 0 < ε) :
    ∃ m : ℕ, 2 ≤ m ∧ 0 < 1 / ((m * d : ℕ) : ℚ) ∧
      1 / ((m * d : ℕ) : ℚ) < ε ∧ LogPairIsKlt c f (m * d) (m • D + G) := by
  let B := crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover
  obtain ⟨m, hm, hpos, hsmall, hupper⟩ := finite_integer_coefficients_small_scaling
    (fun i => cartierCoefficient B (ξ i)) (fun i => cartierCoefficient (cartierPullback ρ G) (ξ i))
    d hd (fun i => logPairIsKlt_crepantBoundary_coefficient_lt ρ hρ c f d D hklt cT
      ⟨ξ i, hξ i⟩) ε hε
  refine ⟨m, hm, hpos, hsmall, ?_⟩
  apply logPairIsKlt_of_crepant_snc_model ρ hρ c f (m * d)
    (by have := Nat.mul_le_mul hm hd; omega) (m • D + G) cT ξ hinj hξ hsnc
  · intro t ht
    rw [crepantBoundaryCartier_add_source, crepantBoundaryCartier_scale_denominator,
      cartierCoefficient_add, cartierCoefficient_nsmul, hsupport t ht,
      hGsupport t ht, mul_zero, add_zero]
  · intro i
    rw [crepantBoundaryCartier_add_source, crepantBoundaryCartier_scale_denominator,
      cartierCoefficient_add, cartierCoefficient_nsmul]
    exact hupper i

variable [IsLocallyNoetherian X]

/-- Adding a sufficiently small fixed effective actual Cartier divisor preserves
source effectivity as well as all-model klt, given the original joint SNC model. -/
theorem logPairIsKlt_exists_arbitrarily_small_fixed_effective_divisor_perturbation
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D G : CartierDivisor X) (hklt : LogPairIsKlt c f d D)
    (heff : LogPairBoundaryEffective c f d D) (hG : G.IsEffective) (cT : EtaleChart K T n)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) = 0)
    (hGsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback ρ G) (t : T) = 0)
    (ε : ℚ) (hε : 0 < ε) :
    ∃ m : ℕ, 2 ≤ m ∧ 0 < 1 / ((m * d : ℕ) : ℚ) ∧
      1 / ((m * d : ℕ) : ℚ) < ε ∧
      LogPairBoundaryEffective c f (m * d) (m • D + G) ∧
      LogPairIsKlt c f (m * d) (m • D + G) := by
  obtain ⟨m, hm, hpos, hsmall, hklt'⟩ :=
    logPairIsKlt_exists_arbitrarily_small_fixed_divisor_perturbation ρ hρ c f d hd
      D G hklt cT ξ hinj hξ hsnc hsupport hGsupport ε hε
  refine ⟨m, hm, hpos, hsmall, ?_, hklt'⟩
  exact logPairBoundaryEffective_add_effective c f (m * d) (m • D) G
    ((logPairBoundaryEffective_scale_denominator_iff c f d m (by omega) D).mpr heff) hG

end MixedFujita
