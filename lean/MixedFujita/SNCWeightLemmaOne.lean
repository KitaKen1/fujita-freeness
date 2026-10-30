/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PrimeDivisorTaylorTest
public import MixedFujita.IsolationWeightMinimizer

/-!
Lemma 1 and the lower end of the discrepancy interval for the weights of simple normal crossing
models (step 11, sections 1.1 and 3.1 of the manuscript: the bounds (1), (9) and the constant a_*
of (10)), for a smooth variety with zero boundary and an ample divisor A.

* Analysis. If the values e_ik and the log discrepancies a_k ≥ 0 of the members satisfy
  e_ik ≤ C j a_k, then for every weight w ≥ 0 and t > 0 the objective satisfies
  F(w) ≥ N exp(−C A(w)), with A(w) = Σ_k w_k a_k; hence F(w) ≤ N (1 − δ) forces
  A(w) ≥ −log(1 − δ)/C.
* Geometry. There is one constant c ≥ 1, depending only on the smooth variety Y and the ample
  divisor A, such that for every smooth birational model π : X → Y, every prime divisor z of X,
  every j ≥ 1 and every nonzero section s of j A the coefficient at z of π*(div s) is at most
  c j times the log discrepancy of z for the zero boundary, written with the crepant boundary of
  the model. This is Lemma 1 for the members of all simple normal crossing models at once.
* Consequence. With the same constant, on every model, for every family of nonzero sections of
  j A, every t > 0 and every weight w ≥ 0 on codimension-one points of the model: if
  F(w) ≤ N (1 − δ), then A(w) ≥ −log(1 − δ)/c. The constant does not depend on the
  degree, the sections, the model, t or the weight: it is the constant a_* which section 5.3 of
  the manuscript fixes before t.
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

section Analysis

variable {N r : ℕ}

/-- The bound (9): if e_ik ≤ C j a_k with a_k ≥ 0, then the objective of every weight w ≥ 0 is at
least N exp(−C A(w)). -/
theorem weightExponentialObjective_ge_of_coefficient_le (a : Fin r → ℝ)
    (e : Fin N → Fin r → ℝ) {t j C : ℝ} (ht : 0 < t) (hj : 0 < j) (ha : ∀ k, 0 ≤ a k)
    (hbound : ∀ i k, e i k ≤ C * j * a k) (w : Fin r → ℝ) (hw : ∀ k, 0 ≤ w k) :
    (N : ℝ) * Real.exp (-(C * ∑ k, w k * a k)) ≤ weightExponentialObjective a e t j w := by
  unfold weightExponentialObjective
  have hA : 0 ≤ ∑ k, w k * a k := Finset.sum_nonneg fun k _ => mul_nonneg (hw k) (ha k)
  have hterm : ∀ i : Fin N, Real.exp (-(C * ∑ k, w k * a k)) ≤
      Real.exp ((∑ k, w k * a k) / t - (∑ k, w k * e i k) / j) := by
    intro i
    apply Real.exp_le_exp.mpr
    have hv : ∑ k, w k * e i k ≤ C * j * ∑ k, w k * a k := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      calc w k * e i k ≤ w k * (C * j * a k) := mul_le_mul_of_nonneg_left (hbound i k) (hw k)
        _ = C * j * (w k * a k) := by ring
    have hv' : (∑ k, w k * e i k) / j ≤ C * ∑ k, w k * a k := by
      rw [div_le_iff₀ hj]
      calc ∑ k, w k * e i k ≤ C * j * ∑ k, w k * a k := hv
        _ = C * (∑ k, w k * a k) * j := by ring
    have hpos : 0 ≤ (∑ k, w k * a k) / t := div_nonneg hA ht.le
    linarith
  calc (N : ℝ) * Real.exp (-(C * ∑ k, w k * a k)) =
      ∑ _i : Fin N, Real.exp (-(C * ∑ k, w k * a k)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ ∑ i, Real.exp ((∑ k, w k * a k) / t - (∑ k, w k * e i k) / j) :=
        Finset.sum_le_sum fun i _ => hterm i

/-- The lower end a_* of the discrepancy interval (10): under the bound of Lemma 1, a weight whose
objective is at most N (1 − δ) has log discrepancy at least −log(1 − δ)/C. -/
theorem weight_logDiscrepancy_ge_of_objective_le (hN : 0 < N) (a : Fin r → ℝ)
    (e : Fin N → Fin r → ℝ) {t j C : ℝ} (ht : 0 < t) (hj : 0 < j) (hC : 0 < C)
    (ha : ∀ k, 0 ≤ a k) (hbound : ∀ i k, e i k ≤ C * j * a k) (w : Fin r → ℝ)
    (hw : ∀ k, 0 ≤ w k) {δ : ℝ}
    (hF : weightExponentialObjective a e t j w ≤ N * (1 - δ)) :
    -Real.log (1 - δ) / C ≤ ∑ k, w k * a k := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := (weightExponentialObjective_ge_of_coefficient_le a e ht hj ha hbound w hw).trans hF
  have h2 : Real.exp (-(C * ∑ k, w k * a k)) ≤ 1 - δ := le_of_mul_le_mul_left h1 hNpos
  have h3 : -(C * ∑ k, w k * a k) ≤ Real.log (1 - δ) := by
    have h := Real.log_le_log (Real.exp_pos _) h2
    rwa [Real.log_exp] at h
  rw [div_le_iff₀ hC]
  linarith

end Analysis

section Geometry

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} {Y : Scheme.{u}}
  [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of K))]

/-- Lemma 1 for the prime divisors of the smooth birational models of a smooth variety with zero
boundary: one constant c ≥ 1 bounds the coefficient at every prime divisor z of every model of the
pullback of the zero divisor of every nonzero section of j A by c j times the log discrepancy of
z, written with the crepant boundary of the model. -/
theorem cartierIsAmpleProj_model_coefficient_le {d : ℕ} (hn : topologicalKrullDim Y = d)
    (hd : 1 ≤ d) {A : CartierDivisor Y} (hA : CartierIsAmpleProj K A) :
    ∃ c : ℕ, 1 ≤ c ∧ ∀ (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
      [X.Over (Spec (CommRingCat.of K))]
      [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
      (π : X ⟶ Y) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))]
      (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π))
      (cY : EtaleChart K Y n) (cX : EtaleChart K X n) (z : CodimensionOnePoint X) (j : ℕ),
      1 ≤ j → ∀ (s : Γ((j • A).sheaf, ⊤)) (hs : s ≠ 0),
        (0 : ℝ) ≤ (((1 : ℕ) : ℝ) - cartierCoefficient (crepantBoundaryCartier π hπ cY
          (1 : Y.functionFieldˣ) 1 (1 • (smoothCanonicalDivisor cY +
            principalCartierDivisor Y (1 : Y.functionFieldˣ))) cX etaleCharts_cover) (z : X)) /
          ((1 : ℕ) : ℝ) ∧
        (cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor (j • A) s hs))
            (z : X) : ℝ) ≤
          (c : ℝ) * (j : ℝ) * ((((1 : ℕ) : ℝ) - cartierCoefficient (crepantBoundaryCartier π hπ cY
            (1 : Y.functionFieldˣ) 1 (1 • (smoothCanonicalDivisor cY +
              principalCartierDivisor Y (1 : Y.functionFieldˣ))) cX etaleCharts_cover) (z : X)) /
            ((1 : ℕ) : ℝ)) := by
  obtain ⟨c, hc1, hc⟩ := cartierIsAmpleProj_prime_coefficient_le (K := K) (n := n) hn hd hA
  refine ⟨c, hc1, fun X _ _ _ _ π _ _ hπ cY cX z j hj s hs => ?_⟩
  have hB : cartierCoefficient (crepantBoundaryCartier π hπ cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) cX
      etaleCharts_cover) (z : X) =
      -cartierCoefficient (birationalRelativeCanonicalDivisor n π hπ cY etaleCharts_cover cX
        etaleCharts_cover) (z : X) := by
    rw [crepantBoundaryCartier_eq_neg_discrepancy, cartierCoefficient_neg,
      logDiscrepancyDivisor_boundary_zero π hπ cY (1 : Y.functionFieldˣ) 1 cX, one_nsmul]
  obtain ⟨x, -, -, hK0, -⟩ := exists_closedPoint_cartierPullback_coefficient_le π hπ cY cX z
  have hle := hc X π hπ cY cX z j hj s hs
  have hK0' : (0 : ℝ) ≤ (cartierCoefficient (birationalRelativeCanonicalDivisor n π hπ cY
      etaleCharts_cover cX etaleCharts_cover) (z : X) : ℝ) := by exact_mod_cast hK0
  have hle' : (cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor (j • A) s hs))
      (z : X) : ℝ) ≤ (c : ℝ) * (j : ℝ) * (1 + (cartierCoefficient
        (birationalRelativeCanonicalDivisor n π hπ cY etaleCharts_cover cX etaleCharts_cover)
        (z : X) : ℝ)) := by
    exact_mod_cast hle
  rw [hB]
  push_cast
  constructor
  · rw [div_one]
    linarith
  · rw [div_one]
    calc (cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor (j • A) s hs))
        (z : X) : ℝ) ≤ (c : ℝ) * (j : ℝ) * (1 + (cartierCoefficient
          (birationalRelativeCanonicalDivisor n π hπ cY etaleCharts_cover cX etaleCharts_cover)
          (z : X) : ℝ)) := hle'
      _ = (c : ℝ) * (j : ℝ) * (1 - -(cartierCoefficient
          (birationalRelativeCanonicalDivisor n π hπ cY etaleCharts_cover cX etaleCharts_cover)
          (z : X) : ℝ)) := by ring

/-- The constant a_* of (10) for the weights of all models: one constant c ≥ 1 such that on every
smooth birational model, for every family of nonzero sections of j A, every t > 0 and every weight
w ≥ 0 on codimension-one points of the model, an objective at most N (1 − δ) forces
A(w) ≥ −log(1 − δ)/c. -/
theorem cartierIsAmpleProj_weight_logDiscrepancy_ge {d : ℕ} (hn : topologicalKrullDim Y = d)
    (hd : 1 ≤ d) {A : CartierDivisor Y} (hA : CartierIsAmpleProj K A) :
    ∃ c : ℕ, 1 ≤ c ∧ ∀ (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
      [X.Over (Spec (CommRingCat.of K))]
      [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
      (π : X ⟶ Y) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))]
      (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π))
      (cY : EtaleChart K Y n) (cX : EtaleChart K X n) {r : ℕ} (ξ : Fin r → X),
      (∀ k, Order.coheight (ξ k) = 1) → ∀ (j : ℕ), 1 ≤ j → ∀ {N : ℕ}, 0 < N →
      ∀ (s : Fin N → Γ((j • A).sheaf, ⊤)) (hs : ∀ i, s i ≠ 0) {t : ℝ}, 0 < t →
      ∀ w : Fin r → ℝ, (∀ k, 0 ≤ w k) → ∀ {δ : ℝ},
        weightExponentialObjective
            (fun k => (((1 : ℕ) : ℝ) - cartierCoefficient (crepantBoundaryCartier π hπ cY
              (1 : Y.functionFieldˣ) 1 (1 • (smoothCanonicalDivisor cY +
                principalCartierDivisor Y (1 : Y.functionFieldˣ))) cX etaleCharts_cover) (ξ k)) /
              ((1 : ℕ) : ℝ))
            (fun i k => (cartierCoefficient (cartierPullback π
              (cartierSectionZeroDivisor (j • A) (s i) (hs i))) (ξ k) : ℝ)) t j w ≤
          N * (1 - δ) →
        -Real.log (1 - δ) / c ≤ ∑ k, w k * ((((1 : ℕ) : ℝ) - cartierCoefficient
          (crepantBoundaryCartier π hπ cY (1 : Y.functionFieldˣ) 1 (1 • (smoothCanonicalDivisor cY +
            principalCartierDivisor Y (1 : Y.functionFieldˣ))) cX etaleCharts_cover) (ξ k)) /
          ((1 : ℕ) : ℝ)) := by
  obtain ⟨c, hc1, hc⟩ := cartierIsAmpleProj_model_coefficient_le (K := K) (n := n) hn hd hA
  refine ⟨c, hc1, fun X _ _ _ _ π _ _ hπ cY cX r ξ hξ j hj N hN s hs t ht w hw δ hF => ?_⟩
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc1
  -- one section gives the nonnegativity of the log discrepancies
  have ha : ∀ k, (0 : ℝ) ≤ (((1 : ℕ) : ℝ) - cartierCoefficient (crepantBoundaryCartier π hπ cY
      (1 : Y.functionFieldˣ) 1 (1 • (smoothCanonicalDivisor cY +
        principalCartierDivisor Y (1 : Y.functionFieldˣ))) cX etaleCharts_cover) (ξ k)) /
      ((1 : ℕ) : ℝ) := fun k =>
    (hc X π hπ cY cX ⟨ξ k, hξ k⟩ j hj (s ⟨0, hN⟩) (hs ⟨0, hN⟩)).1
  exact weight_logDiscrepancy_ge_of_objective_le hN _ _ ht hjpos hcpos ha
    (fun i k => (hc X π hπ cY cX ⟨ξ k, hξ k⟩ j hj (s i) (hs i)).2) w hw hF

end Geometry

end MixedFujita
