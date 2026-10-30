/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CrepantSNCBasePointKlt
public import MixedFujita.BasePointRationalLogCanonical
public import MixedFujita.FixedDivisorSmallKltPerturbations
public import MixedFujita.NormalEffectiveCartierPrime

/-!
The exact finite-or-infinite rational perturbation threshold over a specified
base point, on one actual joint SNC model. Components whose base images do not
specialize to that point impose no condition. A finite threshold is attained
by an actual relevant prime of positive perturbing coefficient.
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

variable {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))


variable {Y : Scheme.{u}} (g : X ⟶ Y) (η : Y)

/-- Rational klt tests over the base point are finite relevant coefficient inequalities. -/
theorem logPairIsKltOverBasePoint_rational_perturbation_iff_snc_coefficients
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D G : CartierDivisor X) (cT : EtaleChart K T n)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) = 0)
    (hGsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback ρ G) (t : T) = 0)
    (p q : ℕ) (hq : 1 ≤ q) :
    LogPairIsKltOverBasePoint g η c f (q * d) (q • D + (d * p) • G) ↔
      ∀ i, η ∈ closure ({(ρ ≫ g) (ξ i)} : Set Y) → (q : ℤ) * cartierCoefficient
        (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ i) +
        ((d * p : ℕ) : ℤ) * cartierCoefficient (cartierPullback ρ G) (ξ i) <
          ((q * d : ℕ) : ℤ) := by
  have hqd : 1 ≤ q * d := Nat.mul_pos (by omega) (by omega)
  have hsupport' (t : CodimensionOnePoint T) (ht : (t : T) ∉ Set.range ξ) :
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f (q * d)
        (q • D + (d * p) • G) cT etaleCharts_cover) (t : T) = 0 := by
    rw [crepantBoundaryCartier_add_source, crepantBoundaryCartier_scale_denominator,
      cartierPullback_nsmul, cartierCoefficient_add, cartierCoefficient_nsmul,
      cartierCoefficient_nsmul, hsupport t ht, hGsupport t ht, mul_zero, mul_zero, add_zero]
  have h := logPairIsKltOverBasePoint_iff_crepant_snc_coefficients ρ hρ g η c f (q * d) hqd
    (q • D + (d * p) • G) cT ξ hinj hξ hsnc hsupport'
  simpa only [crepantBoundaryCartier_add_source, crepantBoundaryCartier_scale_denominator,
    cartierPullback_nsmul, cartierCoefficient_add, cartierCoefficient_nsmul] using h


/-- The finite endpoint is attained by an actual relevant positive-coefficient prime. -/
theorem exists_snc_rational_klt_overBasePoint_threshold
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D G : CartierDivisor X) (hklt : LogPairIsKlt c f d D) (hG : G.IsEffective)
    (cT : EtaleChart K T n) {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) = 0)
    (hGsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback ρ G) (t : T) = 0)
    (hpos : ∃ i, η ∈ closure ({(ρ ≫ g) (ξ i)} : Set Y) ∧
      0 < cartierCoefficient (cartierPullback ρ G) (ξ i)) :
    ∃ (a q₀ : ℕ) (i₀ : Fin r), 1 ≤ a ∧ 1 ≤ q₀ ∧
      η ∈ closure ({(ρ ≫ g) (ξ i₀)} : Set Y) ∧ 0 < cartierCoefficient (cartierPullback ρ G) (ξ i₀) ∧
      (a : ℚ) / q₀ =
        ((d : ℚ) - cartierCoefficient
          (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ i₀)) /
          ((d : ℚ) * cartierCoefficient (cartierPullback ρ G) (ξ i₀)) ∧
      cartierCoefficient (logDiscrepancyDivisor n ρ hρ c f (q₀ * d)
        (q₀ • D + (d * a) • G) cT etaleCharts_cover) (ξ i₀) = -((q₀ * d : ℕ) : ℤ) ∧
      ∀ (p q : ℕ), 1 ≤ q →
        (LogPairIsKltOverBasePoint g η c f (q * d) (q • D + (d * p) • G) ↔ (p : ℚ) / q < (a : ℚ) / q₀) := by
  classical
  let B := crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover
  let v : Fin r → ℤ := fun i => if η ∈ closure ({(ρ ≫ g) (ξ i)} : Set Y)
    then cartierCoefficient (cartierPullback ρ G) (ξ i) else 0
  have hb : ∀ i, cartierCoefficient B (ξ i) < (d : ℤ) :=
    fun i => logPairIsKlt_crepantBoundary_coefficient_lt ρ hρ c f d D hklt cT ⟨ξ i, hξ i⟩
  have hv : ∀ i, 0 ≤ v i := by
    intro i
    dsimp [v]
    split_ifs
    · exact cartierCoefficient_nonneg_of_isEffective _
        (cartierPullback_effective_of_effective ρ G hG) (ξ i)
    · exact le_rfl
  have hvpos : ∃ i, 0 < v i := by
    obtain ⟨i, hi, hgi⟩ := hpos
    exact ⟨i, by simpa only [v, if_pos hi] using hgi⟩
  obtain ⟨a, q₀, i₀, ha, hq₀, hvi, hratio, hendpoint, htest⟩ :=
    finite_integer_coefficients_exact_threshold
      (fun i => cartierCoefficient B (ξ i)) v d hd hb hv hvpos
  have hi₀ : η ∈ closure ({(ρ ≫ g) (ξ i₀)} : Set Y) := by
    by_contra hnot
    simpa only [v, if_neg hnot, lt_self_iff_false] using hvi
  have hgi : 0 < cartierCoefficient (cartierPullback ρ G) (ξ i₀) := by
    simpa only [v, if_pos hi₀] using hvi
  simp only [v, if_pos hi₀] at hratio hendpoint
  refine ⟨a, q₀, i₀, ha, hq₀, hi₀, hgi, hratio, ?_, ?_⟩
  · have hB : cartierCoefficient (crepantBoundaryCartier ρ hρ c f (q₀ * d)
        (q₀ • D + (d * a) • G) cT etaleCharts_cover) (ξ i₀) = ((q₀ * d : ℕ) : ℤ) := by
      rw [crepantBoundaryCartier_add_source, crepantBoundaryCartier_scale_denominator,
        cartierPullback_nsmul, cartierCoefficient_add, cartierCoefficient_nsmul,
        cartierCoefficient_nsmul]
      exact hendpoint
    rw [crepantBoundaryCartier_eq_neg_discrepancy, cartierCoefficient_neg] at hB
    omega
  · intro p q hq
    rw [logPairIsKltOverBasePoint_rational_perturbation_iff_snc_coefficients ρ hρ g η
      c f d hd D G cT ξ hinj hξ hsnc hsupport hGsupport p q hq]
    apply Iff.trans _ (htest p q hq)
    constructor
    · intro h i
      by_cases hi : η ∈ closure ({(ρ ≫ g) (ξ i)} : Set Y)
      · simpa only [v, if_pos hi] using h i hi
      · simp only [v, if_neg hi, mul_zero, add_zero, Nat.cast_mul]
        exact mul_lt_mul_of_pos_left (hb i) (by exact_mod_cast hq : (0 : ℤ) < q)
    · intro h i hi
      simpa only [v, if_pos hi] using h i

/-- Without a relevant positive coefficient, every nonnegative rational perturbation is klt. -/
theorem snc_rational_klt_overBasePoint_all_of_no_positive_coefficient
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D G : CartierDivisor X) (hklt : LogPairIsKlt c f d D) (hG : G.IsEffective)
    (cT : EtaleChart K T n) {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) = 0)
    (hGsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback ρ G) (t : T) = 0)
    (hno : ¬ ∃ i, η ∈ closure ({(ρ ≫ g) (ξ i)} : Set Y) ∧
      0 < cartierCoefficient (cartierPullback ρ G) (ξ i)) :
    ∀ (p q : ℕ), 1 ≤ q →
      LogPairIsKltOverBasePoint g η c f (q * d) (q • D + (d * p) • G) := by
  intro p q hq
  apply (logPairIsKltOverBasePoint_rational_perturbation_iff_snc_coefficients ρ hρ g η
    c f d hd D G cT ξ hinj hξ hsnc hsupport hGsupport p q hq).mpr
  intro i hi
  have hgi : cartierCoefficient (cartierPullback ρ G) (ξ i) = 0 := by
    have hnonneg := cartierCoefficient_nonneg_of_isEffective _
      (cartierPullback_effective_of_effective ρ G hG) (ξ i)
    have hnot : ¬ 0 < cartierCoefficient (cartierPullback ρ G) (ξ i) :=
      fun hpos => hno ⟨i, hi, hpos⟩
    omega
  rw [hgi, mul_zero, add_zero, Nat.cast_mul]
  exact mul_lt_mul_of_pos_left
    (logPairIsKlt_crepantBoundary_coefficient_lt ρ hρ c f d D hklt cT ⟨ξ i, hξ i⟩)
    (by exact_mod_cast hq : (0 : ℤ) < q)

end MixedFujita
