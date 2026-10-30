/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCBasePointRationalThreshold
public import MixedFujita.HironakaSNCModelExistence

/-!
Construct exact rational klt/lc thresholds at every specified base point from
the original pair and effective Cartier perturbation. The joint SNC model is
constructed internally. The threshold is either infinite, or positive rational
and computed by an actual relevant prime; no positivity witness is assumed.
These are valuative base-point predicates. The dictionary for actual open
restrictions, generic-prime finiteness for pulled local uniformizers, global
discriminant gluing and the moduli part remain separate geometric obligations.
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

/-- Every base point has either an infinite interval or an attained positive rational endpoint. -/
theorem rational_klt_overBasePoint_finite_or_infinite (g : X ⟶ Y) (η : Y)
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (heff : LogPairBoundaryEffective c f d D)
    (hklt : LogPairIsKlt c f d D)
    (G : CartierDivisor X) (hG : G.IsEffective) :
    (∀ (p q : ℕ), 1 ≤ q →
      LogPairBoundaryEffective c f (q * d) (q • D + (d * p) • G)) ∧
    ((∀ (p q : ℕ), 1 ≤ q →
      LogPairIsKltOverBasePoint g η c f (q * d) (q • D + (d * p) • G)) ∨
    ∃ (a q₀ : ℕ), 1 ≤ a ∧ 1 ≤ q₀ ∧ 0 < (a : ℚ) / q₀ ∧
      LogPairIsLogCanonicalOverBasePoint g η c f (q₀ * d) (q₀ • D + (d * a) • G) ∧
      (¬ LogPairIsKltOverBasePoint g η c f (q₀ * d) (q₀ • D + (d * a) • G)) ∧
      ∃ (T : Scheme.{u}) (_ : IsIntegral T) (_ : T.Over (Spec (CommRingCat.of K)))
        (_ : IsNoetherian T) (_ : SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K)))
        (ρ : T ⟶ X) (_ : IsDominant ρ) (_ : ρ.IsOver (Spec (CommRingCat.of K))) (_ : IsProper ρ)
        (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
        (cT : EtaleChart K T n) (t : CodimensionOnePoint T),
        η ∈ closure ({(ρ ≫ g) (t : T)} : Set Y) ∧
        0 < cartierCoefficient (cartierPullback ρ G) (t : T) ∧
        (a : ℚ) / q₀ =
          ((d : ℚ) - cartierCoefficient
            (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T)) /
            ((d : ℚ) * cartierCoefficient (cartierPullback ρ G) (t : T)) ∧
        cartierCoefficient (logDiscrepancyDivisor n ρ hρ c f (q₀ * d)
          (q₀ • D + (d * a) • G) cT etaleCharts_cover) (t : T) = -((q₀ * d : ℕ) : ℤ) ∧
        ∀ (p q : ℕ), 1 ≤ q →
          (LogPairIsKltOverBasePoint g η c f (q * d) (q • D + (d * p) • G) ↔
            (p : ℚ) / q < (a : ℚ) / q₀) ∧
          (LogPairIsLogCanonicalOverBasePoint g η c f (q * d) (q • D + (d * p) • G) ↔
            (p : ℚ) / q ≤ (a : ℚ) / q₀)) := by
  classical
  have heffall : ∀ (p q : ℕ), 1 ≤ q →
      LogPairBoundaryEffective c f (q * d) (q • D + (d * p) • G) := by
    intro p q hq
    have hGmul : ((d * p) • G).IsEffective :=
      (CartierDivisor.mem_effectiveSubmonoid ((d * p) • G)).mp
        ((CartierDivisor.effectiveSubmonoid X).nsmul_mem
          ((CartierDivisor.mem_effectiveSubmonoid G).mpr hG) (d * p))
    exact logPairBoundaryEffective_add_effective c f (q * d) (q • D) ((d * p) • G)
      ((logPairBoundaryEffective_scale_denominator_iff c f d q hq D).mpr heff) hGmul
  refine ⟨heffall, ?_⟩
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
  by_cases hpos : ∃ i, η ∈ closure ({(ρ ≫ g) (ξ i)} : Set Y) ∧
      0 < cartierCoefficient (cartierPullback ρ G) (ξ i)
  · apply Or.inr
    obtain ⟨a, q₀, i₀, ha, hq₀, hi₀, hgi, hratio, hendpoint, htest⟩ :=
      exists_snc_rational_klt_overBasePoint_threshold ρ hρ g η c f d hd D G hklt hG cT
        ξ hinj hcoh hsnc hsupp (hGsupp PUnit.unit) hpos
    have hnot : ¬ LogPairIsKltOverBasePoint g η c f (q₀ * d)
        (q₀ • D + (d * a) • G) := by
      intro h
      have hbound := h T ρ hρ cT (ξ i₀) (hcoh i₀) hi₀
      rw [hendpoint] at hbound
      exact lt_irrefl _ hbound
    have hlc := logPairIsLogCanonicalOverBasePoint_at_rational_klt_endpoint
      g η c f d D G a q₀ ha hq₀ (fun p q hq hp => (htest p q hq).mpr hp)
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
        omega
      rw [crepantBoundaryCartier_add_source, crepantBoundaryCartier_scale_denominator,
        cartierPullback_nsmul, cartierCoefficient_add, cartierCoefficient_nsmul,
        cartierCoefficient_nsmul] at hB
      rw [hratio]
      exact (integer_perturbation_coefficient_le_iff _ _ d p q hd hq hgi).mp hB
    · intro hpq
      by_cases hp : 1 ≤ p
      · apply logPairIsLogCanonicalOverBasePoint_at_rational_klt_endpoint g η c f d D G p q hp hq
        intro x y hy hxy
        exact (htest x y hy).mpr (hxy.trans_le hpq)
      · have hpzero : p = 0 := by omega
        apply logPairIsKltOverBasePoint_logCanonical g η c f (q * d) (q • D + (d * p) • G)
        apply (htest p q hq).mpr
        simpa only [hpzero, Nat.cast_zero, zero_div] using hthresholdpos
  · exact Or.inl (snc_rational_klt_overBasePoint_all_of_no_positive_coefficient
      ρ hρ g η c f d hd D G hklt hG cT ξ hinj hcoh hsnc hsupp (hGsupp PUnit.unit) hpos)

/-- Openness on the base with the SNC model supplied internally by resolution. -/
theorem isOpen_logPairIsKltOverBasePoint_of_resolution (g : X ⟶ Y)
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) :
    IsOpen {η : Y | LogPairIsKltOverBasePoint g η c f d D} := by
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hρ, cT, r, ξ,
    hinj, hcoh, hsnc, hsupp⟩ := exists_proper_snc_model c f d D
  letI := hTi
  letI := hTo
  letI := hTN
  letI := hTs
  letI := hdom
  letI := hover
  letI := hprop
  exact isOpen_logPairIsKltOverBasePoint ρ hρ g c f d hd D cT ξ hinj hcoh hsnc hsupp

end MixedFujita
