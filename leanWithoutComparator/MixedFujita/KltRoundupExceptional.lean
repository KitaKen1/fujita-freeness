/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCBoundaryRoundup
public import MixedFujita.KltIsolationGeneration
public import MixedFujita.NormalBirationalPrimeLifts

/-!
For an effective klt pair, the negative crepant boundary rounded up on an actual
SNC resolution is an effective exceptional Cartier divisor. Nonexceptional
boundary coefficients lie in [0,d), by actual stalk and top-form comparisons.
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

variable {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian X] [IsLocallyNoetherian T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (π : T ⟶ X) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))]
  (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π))

/-- Above a normal codimension-one point, the actual crepant boundary coefficient
is nonnegative when the source boundary is effective. -/
theorem crepantBoundary_coefficient_nonneg_over_normal_prime
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hcov : CodimOneChartCovered n K X)
    (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X)
    (heff : LogPairBoundaryEffective cX fX d D) (cT : EtaleChart K T n)
    (t : CodimensionOnePoint T) (ht : Order.coheight (π (t : T)) = 1) :
    0 ≤ cartierCoefficient
      (crepantBoundaryCartier π hπ cX fX d D cT etaleCharts_cover) (t : T) := by
  letI := hnorm (π (t : T))
  letI := normal_codimensionOne_stalk_DVR (⟨π (t : T), ht⟩ : CodimensionOnePoint X)
  letI : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  letI := smoothOverField_codimensionOne_stalk_DVR (K := K) t
  have hb := stalkMap_bijective_of_birational_over_normal_prime hnorm π hπ (t : T) ht
  obtain ⟨c, hc⟩ := hcov (π (t : T)) ht
  rw [crepantBoundaryCartier_coefficient_of_stalkMap_bijective π hπ cX fX d D cT t ht hb c hc]
  exact sub_nonneg.mpr (heff c (π (t : T)) hc ht)

/-- Construct ceil(-B_T/d) as an actual effective exceptional Cartier divisor
on the supplied actual SNC model, without rounded-divisor or exceptionality inputs. -/
theorem exists_effective_exceptional_klt_boundary_roundup [IsProper π]
    [IsSeparated (T ↘ Spec (CommRingCat.of K))]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hcov : CodimOneChartCovered n K X)
    (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (heff : LogPairBoundaryEffective cX fX d D)
    (hklt : LogPairIsKlt cX fX d D) (cT : EtaleChart K T n)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier π hπ cX fX d D cT etaleCharts_cover)
        (t : T) = 0) :
    ∃ E : CartierDivisor T, E.IsEffective ∧
      (∀ t : CodimensionOnePoint T, cartierCoefficient E (t : T) =
        ⌈-((cartierCoefficient (crepantBoundaryCartier π hπ cX fX d D cT etaleCharts_cover)
          (t : T) : ℝ) / (d : ℝ))⌉) ∧
      ∀ t : CodimensionOnePoint T, Order.coheight (π (t : T)) = 1 →
        cartierCoefficient E (t : T) = 0 := by
  letI : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hb (t : CodimensionOnePoint T) :=
    logPairIsKlt_crepantBoundary_coefficient_lt π hπ cX fX d D hklt cT t
  obtain ⟨E, hE, hEc⟩ := exists_effective_snc_boundary_roundup
    (crepantBoundaryCartier π hπ cX fX d D cT etaleCharts_cover) d hd
    ξ hinj hξ hsnc hsupport (fun i => hb ⟨ξ i, hξ i⟩)
  refine ⟨E, hE, hEc, fun t ht => ?_⟩
  have h0 := crepantBoundary_coefficient_nonneg_over_normal_prime π hπ hnorm hcov
    cX fX d D heff cT t ht
  have hden : (0 : ℝ) < d := by exact_mod_cast hd
  have hlo : 0 ≤ (cartierCoefficient
      (crepantBoundaryCartier π hπ cX fX d D cT etaleCharts_cover) (t : T) : ℝ) / d :=
    div_nonneg (by exact_mod_cast h0) hden.le
  have hhi : (cartierCoefficient
      (crepantBoundaryCartier π hπ cX fX d D cT etaleCharts_cover) (t : T) : ℝ) / d < 1 :=
    (div_lt_one hden).mpr (by exact_mod_cast hb t)
  rw [hEc t, Int.ceil_neg, Int.floor_eq_zero_iff.mpr ⟨hlo, hhi⟩, neg_zero]

end MixedFujita
