/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.BasePointRationalKltThreshold
public import MixedFujita.ProperSNCPositiveBaseCoefficient
public import MixedFujita.HironakaSNCModelExistence

/-!
For a proper dominant map, a base effective Cartier divisor of positive order
at the specified base prime has a finite positive rational pullback threshold.
The joint model and relevant positive prime are constructed internally. The finite
SNC coefficient minimum supplies the attained endpoint directly, allowing negative
crepant boundary coefficients and requiring no boundary-effectivity hypothesis.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {X Y : Scheme.{u}}
  [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [IsSeparated (X ↘ Spec (CommRingCat.of K))]


variable [IsIntegral Y] [IsLocallyNoetherian Y]

/-- A klt pair, including a crepant boundary with negative coefficients, has an attained positive
finite base-prime threshold. No boundary effectivity is needed. -/
theorem exists_exact_rational_klt_threshold_over_base_prime_of_klt
    (g : X ⟶ Y) [IsDominant g] [IsProper g] (η : CodimensionOnePoint Y)
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X)
    (hklt : LogPairIsKlt c f d D)
    (H : CartierDivisor Y) (hH : H.IsEffective)
    (hη : 0 < cartierCoefficient H (η : Y)) :
    ∃ (a q₀ : ℕ), 1 ≤ a ∧ 1 ≤ q₀ ∧ 0 < (a : ℚ) / q₀ ∧
      LogPairIsLogCanonicalOverBasePoint g (η : Y) c f (q₀ * d) (q₀ • D + (d * a) • (cartierPullback g H)) ∧
      (¬ LogPairIsKltOverBasePoint g (η : Y) c f (q₀ * d) (q₀ • D + (d * a) • (cartierPullback g H))) ∧
      ∃ (T : Scheme.{u}) (_ : IsIntegral T) (_ : T.Over (Spec (CommRingCat.of K)))
        (_ : IsNoetherian T) (_ : SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K)))
        (ρ : T ⟶ X) (_ : IsDominant ρ) (_ : ρ.IsOver (Spec (CommRingCat.of K))) (_ : IsProper ρ)
        (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
        (cT : EtaleChart K T n) (t : CodimensionOnePoint T),
        (η : Y) ∈ closure ({(ρ ≫ g) (t : T)} : Set Y) ∧
        0 < cartierCoefficient (cartierPullback ρ (cartierPullback g H)) (t : T) ∧
        (a : ℚ) / q₀ =
          ((d : ℚ) - cartierCoefficient
            (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T)) /
            ((d : ℚ) * cartierCoefficient (cartierPullback ρ (cartierPullback g H)) (t : T)) ∧
        cartierCoefficient (logDiscrepancyDivisor n ρ hρ c f (q₀ * d)
          (q₀ • D + (d * a) • (cartierPullback g H)) cT etaleCharts_cover) (t : T) = -((q₀ * d : ℕ) : ℤ) ∧
        ∀ (p q : ℕ), 1 ≤ q →
          (LogPairIsKltOverBasePoint g (η : Y) c f (q * d) (q • D + (d * p) • (cartierPullback g H)) ↔
            (p : ℚ) / q < (a : ℚ) / q₀) ∧
          (LogPairIsLogCanonicalOverBasePoint g (η : Y) c f (q * d) (q • D + (d * p) • (cartierPullback g H)) ↔
            (p : ℚ) / q ≤ (a : ℚ) / q₀) := by
  classical
  let G := cartierPullback g H
  have hG : G.IsEffective := cartierPullback_effective_of_effective g H hH
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hρ, cT, r, ξ,
    hinj, hcoh, hsnc, hsupp, hGsupp⟩ :=
    exists_proper_snc_model_with c f d D (fun _ : PUnit.{1} => G)
  letI := hTi
  letI := hTo
  letI := hTN
  letI := hTs
  letI := hdom
  letI := hover
  letI := hprop
  have hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback (ρ ≫ g) H) (t : T) = 0 := by
    intro t ht
    rw [cartierPullback_comp]
    exact hGsupp PUnit.unit t ht
  have hpos : ∃ i, (η : Y) ∈ closure ({(ρ ≫ g) (ξ i)} : Set Y) ∧
      0 < cartierCoefficient (cartierPullback ρ (cartierPullback g H)) (ξ i) := by
    simpa only [cartierPullback_comp] using
      proper_snc_pullback_exists_positive_coefficient_over_prime
        (ρ ≫ g) H hH η hη ξ hinj hcoh hsnc hsupport
  obtain ⟨a, q₀, i₀, ha, hq₀, hi₀, hgi, hratio, hendpoint, htest⟩ :=
    exists_snc_rational_klt_overBasePoint_threshold ρ hρ g (η : Y) c f d hd D G hklt hG cT
      ξ hinj hcoh hsnc hsupp (hGsupp PUnit.unit) hpos
  have hnot : ¬ LogPairIsKltOverBasePoint g (η : Y) c f (q₀ * d)
      (q₀ • D + (d * a) • G) := by
    intro h
    have hbound := h T ρ hρ cT (ξ i₀) (hcoh i₀) hi₀
    rw [hendpoint] at hbound
    exact lt_irrefl _ hbound
  have hlc := logPairIsLogCanonicalOverBasePoint_at_rational_klt_endpoint
    g (η : Y) c f d D G a q₀ ha hq₀ (fun p q hq hp => (htest p q hq).mpr hp)
  have hthresholdpos : (0 : ℚ) < (a : ℚ) / q₀ :=
    div_pos (by exact_mod_cast ha) (by exact_mod_cast hq₀)
  refine ⟨a, q₀, ha, hq₀, hthresholdpos, hlc, hnot,
    T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hρ, cT, ⟨ξ i₀, hcoh i₀⟩,
    hi₀, hgi, hratio, hendpoint, ?_⟩
  intro p q hq
  refine ⟨htest p q hq, ?_⟩
  constructor
  · intro h
    have hbound := h T ρ hρ cT (ξ i₀) (hcoh i₀) hi₀
    have hB : cartierCoefficient (crepantBoundaryCartier ρ hρ c f (q * d)
        (q • D + (d * p) • G) cT etaleCharts_cover) (ξ i₀) ≤ ((q * d : ℕ) : ℤ) := by
      rw [crepantBoundaryCartier_eq_neg_discrepancy, cartierCoefficient_neg]
      dsimp only [G] at hbound ⊢
      omega
    rw [crepantBoundaryCartier_add_source, crepantBoundaryCartier_scale_denominator,
      cartierPullback_nsmul, cartierCoefficient_add, cartierCoefficient_nsmul,
      cartierCoefficient_nsmul] at hB
    rw [hratio]
    exact (integer_perturbation_coefficient_le_iff _ _ d p q hd hq hgi).mp hB
  · intro hpq
    by_cases hp : 1 ≤ p
    · apply logPairIsLogCanonicalOverBasePoint_at_rational_klt_endpoint g (η : Y) c f d D G p q hp hq
      intro x y hy hxy
      exact (htest x y hy).mpr (hxy.trans_le hpq)
    · have hpzero : p = 0 := by omega
      apply logPairIsKltOverBasePoint_logCanonical g (η : Y) c f (q * d) (q • D + (d * p) • G)
      apply (htest p q hq).mpr
      simpa only [hpzero, Nat.cast_zero, zero_div] using hthresholdpos

end MixedFujita
