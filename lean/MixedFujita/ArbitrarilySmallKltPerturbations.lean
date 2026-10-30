/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CrepantAvoidingPerturbationDescent
public import MixedFujita.LogPairDenominatorScaling

/-!
An actual source section gives an arbitrarily small rational klt perturbation,
simultaneously avoiding finitely many source points. The denominator-cleared
presentation is constructed by scaling the original one. Existence of the
original proper SNC model, and normality of the singular source, remain explicit.
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

/-- Denominator enlargement realizes a positive rational weight below any given margin. -/
theorem exists_small_scaled_denominator (d : ℕ) (hd : 1 ≤ d)
    (ε : ℚ) (hε : 0 < ε) :
    ∃ m : ℕ, 2 ≤ m ∧ 1 < m * d ∧ 0 < 1 / ((m * d : ℕ) : ℚ) ∧
      1 / ((m * d : ℕ) : ℚ) < ε := by
  obtain ⟨j, hj⟩ := exists_nat_gt (1 / ε)
  let m := j + 2
  have hm : 2 ≤ m := by omega
  have hmd : m ≤ m * d := by simpa using Nat.mul_le_mul_left m hd
  have hmd1 : 1 < m * d := by omega
  have hmdpos : (0 : ℚ) < (m * d : ℕ) := by exact_mod_cast (by omega : 0 < m * d)
  have hlt : 1 / ε < ((m * d : ℕ) : ℚ) := by
    have hjm : (j : ℚ) < m := by dsimp [m]; push_cast; linarith
    exact (hj.trans hjm).trans_le (by exact_mod_cast hmd)
  refine ⟨m, hm, hmd1, div_pos zero_lt_one hmdpos, ?_⟩
  apply (div_lt_iff₀ hmdpos).mpr
  have h := (div_lt_iff₀ hε).mp hlt
  simpa only [mul_comm] using h

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {X T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian X] [IsNoetherian T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

/-- Given the original SNC model, an actual section yields a klt perturbation of
arbitrarily small positive rational weight and avoids any finite set of source points. -/
theorem logPairIsKlt_exists_arbitrarily_small_source_perturbation_avoiding
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (hklt : LogPairIsKlt c f d D) (cT : EtaleChart K T n)
    (H : CartierDivisor X) (hH : CartierIsGloballyGenerated H)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) = 0)
    (Z : Set X) (hZ : Z.Finite) (ε : ℚ) (hε : 0 < ε) :
    ∃ (m : ℕ) (s : Γ(H.sheaf, ⊤)) (hs : s ≠ 0),
      2 ≤ m ∧ 0 < 1 / ((m * d : ℕ) : ℚ) ∧ 1 / ((m * d : ℕ) : ℚ) < ε ∧
      LogPairIsKlt c f (m * d) (m • D + cartierSectionZeroDivisor H s hs) ∧
      (∀ x ∈ Z, x ∉ cartierSectionZeroLocus H s) := by
  obtain ⟨m, hm, hmd, hpos, hsmall⟩ := exists_small_scaled_denominator d hd ε hε
  have hscaled := (logPairIsKlt_scale_denominator_iff c f d m (by omega) D).mpr hklt
  have hsupp : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f (m * d) (m • D)
        cT etaleCharts_cover) (t : T) = 0 := by
    intro t ht
    rw [crepantBoundaryCartier_scale_denominator, cartierCoefficient_nsmul,
      hsupport t ht, mul_zero]
  obtain ⟨s, hs, hklt', havoid⟩ :=
    logPairIsKlt_exists_source_perturbation_avoiding_of_crepant_snc_model ρ hρ
      hnorm c f (m * d) (m • D) hscaled cT H hH ξ hinj hξ hsnc hsupp 1 hmd Z hZ
  exact ⟨m, s, hs, hm, hpos, hsmall, by simpa only [one_nsmul] using hklt', havoid⟩

/-- For an effective original boundary, the arbitrarily small actual perturbation
preserves both source effectivity and all-model klt. -/
theorem logPairIsKlt_exists_arbitrarily_small_effective_source_perturbation_avoiding
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (hklt : LogPairIsKlt c f d D)
    (heff : LogPairBoundaryEffective c f d D) (cT : EtaleChart K T n)
    (H : CartierDivisor X) (hH : CartierIsGloballyGenerated H)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) = 0)
    (Z : Set X) (hZ : Z.Finite) (ε : ℚ) (hε : 0 < ε) :
    ∃ (m : ℕ) (s : Γ(H.sheaf, ⊤)) (hs : s ≠ 0),
      2 ≤ m ∧ 0 < 1 / ((m * d : ℕ) : ℚ) ∧ 1 / ((m * d : ℕ) : ℚ) < ε ∧
      LogPairBoundaryEffective c f (m * d) (m • D + cartierSectionZeroDivisor H s hs) ∧
      LogPairIsKlt c f (m * d) (m • D + cartierSectionZeroDivisor H s hs) ∧
      (∀ x ∈ Z, x ∉ cartierSectionZeroLocus H s) := by
  obtain ⟨m, s, hs, hm, hpos, hsmall, hklt', havoid⟩ :=
    logPairIsKlt_exists_arbitrarily_small_source_perturbation_avoiding ρ hρ hnorm
      c f d hd D hklt cT H hH ξ hinj hξ hsnc hsupport Z hZ ε hε
  refine ⟨m, s, hs, hm, hpos, hsmall, ?_, hklt', havoid⟩
  have hscaled := (logPairBoundaryEffective_scale_denominator_iff c f d m (by omega) D).mpr heff
  simpa only [one_nsmul] using
    logPairBoundaryEffective_section_perturbation c f (m * d) 1 (m • D) H s hs hscaled

end MixedFujita
