/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCKltDiscrepancyComparison
public import MixedFujita.AmpleModelOrderBound
public import MixedFujita.RealizedProfiles

/-!
Lemma 1 and the lower discrepancy window for actual SNC klt pairs (section 3.1, step 15).

The section divisor L may be arbitrary: only an ample divisor H on the smooth source is needed.
This matters on a projective resolution, where the pullback of an ample divisor need not be ample.
The uniform order bound for L and the actual prime-divisor Taylor comparison give
ord_E(div s) ≤ c j A_X(E). The integral SNC gap gives A_X(E) ≤ d A_(X,B/d)(E).
Thus one constant bounds all sections on all smooth birational models, and supplies the lower
discrepancy bound for all nonnegative SNC weights. The singular-source comparison and the upper
discrepancy window are separate obligations.
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

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} {X : Scheme.{u}}
  [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]

/-- One constant gives Lemma 1 for every prime on every actual smooth birational model of a
signed SNC klt pair. L is arbitrary; H supplies the projective order bound. -/
theorem isSNCFamily_model_coefficient_le
    (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    {H : CartierDivisor X} (hH : CartierIsAmpleProj K H) (L : CartierDivisor X)
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (B : CartierDivisor X) {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ z : CodimensionOnePoint X,
      (z : X) ∉ Set.range ξ → cartierCoefficient B (z : X) = 0)
    (hb : ∀ i, cartierCoefficient B (ξ i) < (d : ℤ)) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (T : Scheme.{u}) [IsIntegral T] [IsLocallyNoetherian T]
      [T.Over (Spec (CommRingCat.of K))]
      [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
      (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
      (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
      (cT : EtaleChart K T n) (z : CodimensionOnePoint T) (j : ℕ), 1 ≤ j →
      ∀ (s : Γ((j • L).sheaf, ⊤)) (hs : s ≠ 0),
        (0 : ℝ) ≤ ((d : ℝ) - cartierCoefficient (crepantBoundaryCartier ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          cT etaleCharts_cover) (z : T)) / d ∧
        (cartierCoefficient (cartierPullback ρ (cartierSectionZeroDivisor (j • L) s hs))
          (z : T) : ℝ) ≤ (C : ℝ) * j *
          (((d : ℝ) - cartierCoefficient (crepantBoundaryCartier ρ hρ c₀ f₀ d
            (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
            cT etaleCharts_cover) (z : T)) / d) := by
  have hsm : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  obtain ⟨c, hc⟩ := vanishingOrder_le_of_ample_model hdim hn hH L
  refine ⟨(c + 1) * d, by simpa using Nat.mul_le_mul (by omega : 1 ≤ c + 1) hd,
    fun T _ _ _ _ ρ _ _ hρ cT z j hj s hs => ?_⟩
  obtain ⟨x, hx, -, hK0, hle⟩ := exists_closedPoint_cartierPullback_coefficient_le ρ hρ c₀ cT z
  have hmult : (cartierSectionVanishingOrder (j • L) x s).toNat ≤ (c + 1) * j :=
    (ENat.toNat_le_of_le_natCast (hc x hx j hj s hs)).trans
      (Nat.mul_le_mul_right j (Nat.le_add_right c 1))
  have hmult' : ((cartierSectionVanishingOrder (j • L) x s).toNat : ℤ) ≤
      (((c + 1) * j : ℕ) : ℤ) := by exact_mod_cast hmult
  have hcoef : (cartierCoefficient (cartierPullback ρ (cartierSectionZeroDivisor (j • L) s hs))
      (z : T) : ℝ) ≤ ((c + 1 : ℕ) : ℝ) * j *
        (1 + cartierCoefficient (birationalRelativeCanonicalDivisor n ρ hρ c₀ etaleCharts_cover
          cT etaleCharts_cover) (z : T)) := by
    have h := (hle (j • L) s hs).trans
      (mul_le_mul_of_nonneg_left hmult' (by linarith :
        0 ≤ 1 + cartierCoefficient (birationalRelativeCanonicalDivisor n ρ hρ c₀ etaleCharts_cover
          cT etaleCharts_cover) (z : T)))
    push_cast at h ⊢
    exact_mod_cast (by nlinarith [h] :
      cartierCoefficient (cartierPullback ρ (cartierSectionZeroDivisor (j • L) s hs)) (z : T) ≤
        (((c : ℤ) + 1) * j) * (1 + cartierCoefficient
          (birationalRelativeCanonicalDivisor n ρ hρ c₀ etaleCharts_cover cT etaleCharts_cover)
          (z : T)))
  have hcomp := isSNCFamily_logDiscrepancy_comparison ρ hρ c₀ f₀ d hd B ξ hinj hξ hsnc
    hsupport hb cT z
  have hK0' : (0 : ℝ) ≤ (cartierCoefficient (birationalRelativeCanonicalDivisor n ρ hρ c₀
      etaleCharts_cover cT etaleCharts_cover) (z : T) : ℝ) := by exact_mod_cast hK0
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  refine ⟨by nlinarith [hcomp], hcoef.trans ?_⟩
  calc ((c + 1 : ℕ) : ℝ) * j *
      (1 + cartierCoefficient (birationalRelativeCanonicalDivisor n ρ hρ c₀ etaleCharts_cover
        cT etaleCharts_cover) (z : T)) ≤
      ((c + 1 : ℕ) : ℝ) * j * ((d : ℝ) *
        (((d : ℝ) - cartierCoefficient (crepantBoundaryCartier ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          cT etaleCharts_cover) (z : T)) / d)) :=
    mul_le_mul_of_nonneg_left hcomp (by positivity)
    _ = _ := by push_cast; ring

/-- For every actual profile of a tuple, Lemma 1 bounds all values and gives the uniform lower
end of the discrepancy window. The constant is independent of the point, degree and tuple. -/
theorem isSNCFamily_sncWeightProfiles_lower_bounds
    (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    {H : CartierDivisor X} (hH : CartierIsAmpleProj K H) (L : CartierDivisor X)
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (B : CartierDivisor X) {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ z : CodimensionOnePoint X,
      (z : X) ∉ Set.range ξ → cartierCoefficient B (z : X) = 0)
    (hb : ∀ i, cartierCoefficient B (ξ i) < (d : ℤ)) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (j : ℕ), 1 ≤ j → ∀ (x : X) {N : ℕ}, 0 < N →
      ∀ (s : Fin N → Γ((j • L).sheaf, ⊤)) p,
        p ∈ sncWeightProfiles c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B) (j • L) x s →
        ∀ {t δ : ℝ}, 0 < t →
          (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤ (N : ℝ) * (1 - δ) →
          -Real.log (1 - δ) / C ≤ p.1 ∧
            ∀ i, 0 ≤ p.2 i ∧ p.2 i ≤ (C : ℝ) * j * p.1 := by
  obtain ⟨C, hC, hc⟩ := isSNCFamily_model_coefficient_le hdim hn hH L c₀ f₀ d hd B ξ hinj hξ
    hsnc hsupport hb
  refine ⟨C, hC, fun j hj x N hN s p hp t δ ht hF => ?_⟩
  obtain ⟨hs, T, hTi, hTN, hTo, hTs, ρ, hρd, hρo, hρp, hρ, cT, q, η, w, hηinj, hη, hηsnc,
    hTB, hTG, hw, hwΦ, hA, hv⟩ := hp
  let a : Fin q → ℝ := fun k => ((d : ℝ) - cartierCoefficient (crepantBoundaryCartier ρ hρ c₀
    f₀ d (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
    cT etaleCharts_cover) (η k)) / d
  let e : Fin N → Fin q → ℝ := fun i k => cartierCoefficient
    (cartierPullback ρ (cartierSectionZeroDivisor (j • L) (s i) (hs i))) (η k)
  have ha : ∀ k, 0 ≤ a k := fun k =>
    (hc T ρ hρ cT ⟨η k, hη k⟩ j hj (s ⟨0, hN⟩) (hs ⟨0, hN⟩)).1
  have he : ∀ i k, e i k ≤ (C : ℝ) * j * a k := fun i k =>
    (hc T ρ hρ cT ⟨η k, hη k⟩ j hj (s i) (hs i)).2
  have hobj : weightExponentialObjective a e t j w =
      ∑ i, Real.exp (p.1 / t - p.2 i / j) := by
    unfold weightExponentialObjective
    rw [hA]
    exact Finset.sum_congr rfl fun i _ => by rw [hv i]
  refine ⟨?_, fun i => ⟨?_, ?_⟩⟩
  · rw [hA]
    exact weight_logDiscrepancy_ge_of_objective_le hN a e ht
      (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hj))
      (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hC)) ha he w hw
      (by rw [hobj]; exact hF)
  · rw [hv i]
    refine Finset.sum_nonneg fun k _ => mul_nonneg (hw k) ?_
    exact_mod_cast cartierCoefficient_nonneg_of_isEffective _
      (cartierPullback_isEffective ρ _ (cartierSectionZeroDivisor_isEffective _ (s i) (hs i))) _
  · rw [hv i, hA, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    calc w k * e i k ≤ w k * ((C : ℝ) * j * a k) :=
          mul_le_mul_of_nonneg_left (he i k) (hw k)
      _ = (C : ℝ) * j * (w k * a k) := by ring

end MixedFujita
