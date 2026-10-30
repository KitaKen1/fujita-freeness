/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveMinimizationInterval
public import MixedFujita.RealWeightedOrderProperties

/-!
§3.1 and the attainment of §3.2 on a fixed layer with real weights. Fix a morphism ρ : T' → Y over
the base field, a point p over a closed point, completion coordinates at ρ(p) and at p with
nonzero Jacobian determinant. For real weights u ≥ 0 the real valuation v_u(ρ^* s) of the Taylor
expansion and the real log discrepancy A(u) = Σ u + v_u(det J) agree with the natural ones at
natural weights, and both are continuous and homogeneous in u. Hence Lemma 1 (v_u(ρ^* s) ≤ A(u) c j)
and Lemma 2 (v_u ≤ A(u) ⌊ε j⌋ on the subspace U) hold for all real u ≥ 0, and with them the bounds
(8)-(10). If det J is a unit times a monomial z^κ, then A(u) = Σ (1 + κ_i) u_i, and the functional
over the scaled valuations λ u with u in the simplex Σ (1 + κ_i) u_i = 1 attains its infimum on
[a_*, a^*] × simplex; every other scale gives a value above 1 - δ/2. This is §3.2 on a fixed SNC
layer; the reduction to finitely many layers by a log resolution is the remaining input.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial Filter
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

section Taylor

variable {K : Type u} [Field K] {T T' : Scheme.{u}} [T.Over (Spec (CommRingCat.of K))]
  [T'.Over (Spec (CommRingCat.of K))] [IsIntegral T]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

/-- The Taylor expansion at p of the pullback of a section. -/
noncomputable def cartierPullbackTaylor (D : CartierDivisor T) (ρ : T' ⟶ T) (p : T') {n : ℕ}
    (ep : AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
      (T'.presheaf.stalk p) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (s : Γ(D.sheaf, ⊤)) : MvPowerSeries (Fin n) K :=
  ep (algebraMap _ (AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
    (T'.presheaf.stalk p)) (cartierStalkPullbackCoefficient D ρ p
      (Classical.choose (D.exists_isLocalEquationAt (ρ p)))
      (Classical.choose_spec (D.exists_isLocalEquationAt (ρ p))) s))

omit [T.Over (Spec (CommRingCat.of K))] in
theorem cartierPullbackMonomialValuation_eq_taylor (D : CartierDivisor T) (ρ : T' ⟶ T) (p : T')
    {n : ℕ}
    (ep : AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
      (T'.presheaf.stalk p) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (w : Fin n → ℕ) (s : Γ(D.sheaf, ⊤)) :
    cartierPullbackMonomialValuation D ρ p ep w s =
      (cartierPullbackTaylor D ρ p ep s).weightedOrder w := rfl

omit [T.Over (Spec (CommRingCat.of K))] in
theorem cartierPullbackTaylor_add (D : CartierDivisor T) (ρ : T' ⟶ T) (p : T') {n : ℕ}
    (ep : AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
      (T'.presheaf.stalk p) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (s s' : Γ(D.sheaf, ⊤)) :
    cartierPullbackTaylor D ρ p ep (s + s') =
      cartierPullbackTaylor D ρ p ep s + cartierPullbackTaylor D ρ p ep s' := by
  unfold cartierPullbackTaylor
  rw [map_add, map_add, map_add]

theorem cartierPullbackTaylor_smul (D : CartierDivisor T) (ρ : T' ⟶ T)
    [ρ.IsOver (Spec (CommRingCat.of K))] (p : T') {n : ℕ}
    (ep : AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
      (T'.presheaf.stalk p) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (c : K) (s : Γ(D.sheaf, ⊤)) :
    cartierPullbackTaylor D ρ p ep (c • s) =
      algebraMap K (MvPowerSeries (Fin n) K) c * cartierPullbackTaylor D ρ p ep s := by
  unfold cartierPullbackTaylor
  rw [cartierStalkPullbackCoefficient_smul, map_mul, map_mul]
  congr 1
  exact ep.commutes c

/-- The real valuation with weights u of the pullback of a section. -/
noncomputable def cartierPullbackRealValuation (D : CartierDivisor T) (ρ : T' ⟶ T) (p : T')
    {n : ℕ}
    (ep : AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
      (T'.presheaf.stalk p) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (u : Fin n → ℝ) (s : Γ(D.sheaf, ⊤)) : ℝ :=
  realWeightedOrder u (cartierPullbackTaylor D ρ p ep s)

/-- The sections whose pulled-back real valuation exceeds c, or whose Taylor expansion vanishes,
form a subspace. -/
noncomputable def cartierPullbackRealValuationAbove (D : CartierDivisor T) (ρ : T' ⟶ T)
    [ρ.IsOver (Spec (CommRingCat.of K))] (p : T') {n : ℕ}
    (ep : AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
      (T'.presheaf.stalk p) ≃ₐ[K] MvPowerSeries (Fin n) K)
    {u : Fin n → ℝ} (hu : ∀ i, 0 ≤ u i) (c : ℝ) : Submodule K Γ(D.sheaf, ⊤) where
  carrier := {s | cartierPullbackTaylor D ρ p ep s = 0 ∨
    c < cartierPullbackRealValuation D ρ p ep u s}
  add_mem' := fun {s s'} hs hs' => by
    simp only [Set.mem_ofPred_eq, cartierPullbackRealValuation, cartierPullbackTaylor_add] at hs hs' ⊢
    by_cases hsum : cartierPullbackTaylor D ρ p ep s + cartierPullbackTaylor D ρ p ep s' = 0
    · exact Or.inl hsum
    right
    rcases hs with hs | hs
    · rw [hs, zero_add] at hsum ⊢
      rcases hs' with hs' | hs'
      · exact absurd hs' hsum
      · exact hs'
    rcases hs' with hs' | hs'
    · rw [hs', add_zero]
      exact hs
    by_cases h0 : cartierPullbackTaylor D ρ p ep s = 0
    · rw [h0, zero_add]
      exact hs'
    by_cases h0' : cartierPullbackTaylor D ρ p ep s' = 0
    · rw [h0', add_zero]
      exact hs
    exact lt_of_lt_of_le (lt_min hs hs') (realWeightedOrder_add_ge hu h0 h0' hsum)
  zero_mem' := by
    left
    change cartierPullbackTaylor D ρ p ep 0 = 0
    unfold cartierPullbackTaylor
    rw [map_zero, map_zero, map_zero]
  smul_mem' := fun a s hs => by
    simp only [Set.mem_ofPred_eq, cartierPullbackRealValuation] at hs ⊢
    rw [cartierPullbackTaylor_smul]
    by_cases ha : a = 0
    · left
      rw [ha, map_zero, zero_mul]
    rcases hs with hs | hs
    · left
      rw [hs, mul_zero]
    right
    have hunit : IsUnit (algebraMap K (MvPowerSeries (Fin n) K) a) := by
      rw [MvPowerSeries.isUnit_iff_constantCoeff]
      simpa [MvPowerSeries.algebraMap_apply] using Ne.isUnit ha
    rw [realWeightedOrder_unit_mul hu hunit]
    exact hs

end Taylor

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} {Y : Scheme.{u}}
  [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))] [Smooth (Y ↘ Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

/-- The real log discrepancy Σ u + v_u(det J) of a test valuation with real weights. -/
noncomputable def testValuationRealLogDiscrepancy {T' : Scheme.{u}}
    [T'.Over (Spec (CommRingCat.of K))] (ρ : T' ⟶ Y) [ρ.IsOver (Spec (CommRingCat.of K))]
    (p : T') {m : ℕ}
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk (ρ p)))
      (Y.presheaf.stalk (ρ p)) ≃ₐ[K] MvPowerSeries (Fin m) K)
    (ep : AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
      (T'.presheaf.stalk p) ≃ₐ[K] MvPowerSeries (Fin m) K) (u : Fin m → ℝ) : ℝ :=
  ∑ i, u i + realWeightedOrder u (powerSeriesJacobian (schemeCompletedStalkMap ρ p ez ep)).det

omit [IsAlgClosed K] [CharZero K] [IsIntegral Y] [Smooth (Y ↘ Spec (CommRingCat.of K))] in
theorem continuous_testValuationRealLogDiscrepancy {T' : Scheme.{u}}
    [T'.Over (Spec (CommRingCat.of K))] (ρ : T' ⟶ Y) [ρ.IsOver (Spec (CommRingCat.of K))]
    (p : T') {m : ℕ}
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk (ρ p)))
      (Y.presheaf.stalk (ρ p)) ≃ₐ[K] MvPowerSeries (Fin m) K)
    (ep : AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
      (T'.presheaf.stalk p) ≃ₐ[K] MvPowerSeries (Fin m) K) :
    Continuous (testValuationRealLogDiscrepancy ρ p ez ep) := by
  unfold testValuationRealLogDiscrepancy
  exact (continuous_finsetSum _ fun i _ => continuous_apply i).add
    (continuous_realWeightedOrder _)

omit [IsAlgClosed K] [CharZero K] [IsIntegral Y] [Smooth (Y ↘ Spec (CommRingCat.of K))] in
theorem testValuationRealLogDiscrepancy_smul {T' : Scheme.{u}}
    [T'.Over (Spec (CommRingCat.of K))] (ρ : T' ⟶ Y) [ρ.IsOver (Spec (CommRingCat.of K))]
    (p : T') {m : ℕ}
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk (ρ p)))
      (Y.presheaf.stalk (ρ p)) ≃ₐ[K] MvPowerSeries (Fin m) K)
    (ep : AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
      (T'.presheaf.stalk p) ≃ₐ[K] MvPowerSeries (Fin m) K) {c : ℝ} (hc : 0 ≤ c)
    (u : Fin m → ℝ) :
    testValuationRealLogDiscrepancy ρ p ez ep (c • u) =
      c * testValuationRealLogDiscrepancy ρ p ez ep u := by
  unfold testValuationRealLogDiscrepancy
  rw [realWeightedOrder_smul hc, mul_add, Finset.mul_sum]
  simp only [Pi.smul_apply, smul_eq_mul]

omit [IsAlgClosed K] [CharZero K] [IsIntegral Y] [Smooth (Y ↘ Spec (CommRingCat.of K))] in
theorem testValuationRealLogDiscrepancy_natCast {T' : Scheme.{u}}
    [T'.Over (Spec (CommRingCat.of K))] (ρ : T' ⟶ Y) [ρ.IsOver (Spec (CommRingCat.of K))]
    (p : T') {m : ℕ}
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk (ρ p)))
      (Y.presheaf.stalk (ρ p)) ≃ₐ[K] MvPowerSeries (Fin m) K)
    (ep : AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
      (T'.presheaf.stalk p) ≃ₐ[K] MvPowerSeries (Fin m) K)
    (hdet : (powerSeriesJacobian (schemeCompletedStalkMap ρ p ez ep)).det ≠ 0) (w : Fin m → ℕ) :
    testValuationRealLogDiscrepancy ρ p ez ep (fun i => (w i : ℝ)) =
      ((testValuationLogDiscrepancy ρ p ez ep w).toNat : ℝ) := by
  unfold testValuationRealLogDiscrepancy testValuationLogDiscrepancy
  rw [realWeightedOrder_natCast w hdet]
  have hfin := (MvPowerSeries.ne_zero_iff_weightedOrder_finite w).mp hdet
  have hsum : ((∑ i, w i : ℕ) : ℕ∞) +
      (powerSeriesJacobian (schemeCompletedStalkMap ρ p ez ep)).det.weightedOrder w =
        ((∑ i, w i + ((powerSeriesJacobian (schemeCompletedStalkMap ρ p ez ep)).det.weightedOrder
          w).toNat : ℕ) : ℕ∞) := by
    rw [Nat.cast_add, hfin]
  rw [hsum, ENat.toNat_natCast]
  push_cast
  rfl

omit [IsAlgClosed K] [CharZero K] [IsIntegral Y] [Smooth (Y ↘ Spec (CommRingCat.of K))] in
theorem testValuationLogDiscrepancy_ne_top {T' : Scheme.{u}}
    [T'.Over (Spec (CommRingCat.of K))] (ρ : T' ⟶ Y) [ρ.IsOver (Spec (CommRingCat.of K))]
    (p : T') {m : ℕ}
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk (ρ p)))
      (Y.presheaf.stalk (ρ p)) ≃ₐ[K] MvPowerSeries (Fin m) K)
    (ep : AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
      (T'.presheaf.stalk p) ≃ₐ[K] MvPowerSeries (Fin m) K)
    (hdet : (powerSeriesJacobian (schemeCompletedStalkMap ρ p ez ep)).det ≠ 0) (w : Fin m → ℕ) :
    testValuationLogDiscrepancy ρ p ez ep w ≠ ⊤ := by
  unfold testValuationLogDiscrepancy
  exact WithTop.add_ne_top.mpr ⟨ENat.natCast_ne_top _,
    (MvPowerSeries.weightedOrder_eq_top_iff w).not.mpr hdet⟩

omit [IsAlgClosed K] [CharZero K] [IsIntegral Y] [Smooth (Y ↘ Spec (CommRingCat.of K))] in
theorem testValuationRealLogDiscrepancy_nonneg {T' : Scheme.{u}}
    [T'.Over (Spec (CommRingCat.of K))] (ρ : T' ⟶ Y) [ρ.IsOver (Spec (CommRingCat.of K))]
    (p : T') {m : ℕ}
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk (ρ p)))
      (Y.presheaf.stalk (ρ p)) ≃ₐ[K] MvPowerSeries (Fin m) K)
    (ep : AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
      (T'.presheaf.stalk p) ≃ₐ[K] MvPowerSeries (Fin m) K) {u : Fin m → ℝ} (hu : ∀ i, 0 ≤ u i) :
    0 ≤ testValuationRealLogDiscrepancy ρ p ez ep u :=
  add_nonneg (Finset.sum_nonneg fun i _ => hu i) (realWeightedOrder_nonneg hu _)

omit [IsAlgClosed K] [CharZero K] [IsIntegral Y] [Smooth (Y ↘ Spec (CommRingCat.of K))] in
/-- Bounds at all natural weights pass to all nonnegative real weights. -/
theorem realWeightedOrder_le_of_natural {T' : Scheme.{u}}
    [T'.Over (Spec (CommRingCat.of K))] (ρ : T' ⟶ Y) [ρ.IsOver (Spec (CommRingCat.of K))]
    (p : T') {m : ℕ}
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk (ρ p)))
      (Y.presheaf.stalk (ρ p)) ≃ₐ[K] MvPowerSeries (Fin m) K)
    (ep : AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
      (T'.presheaf.stalk p) ≃ₐ[K] MvPowerSeries (Fin m) K)
    (hdet : (powerSeriesJacobian (schemeCompletedStalkMap ρ p ez ep)).det ≠ 0)
    {F : MvPowerSeries (Fin m) K} {c : ℕ}
    (hnat : ∀ w : Fin m → ℕ, F.weightedOrder w ≤ testValuationLogDiscrepancy ρ p ez ep w * (c : ℕ∞))
    {u : Fin m → ℝ} (hu : ∀ i, 0 ≤ u i) :
    realWeightedOrder u F ≤ testValuationRealLogDiscrepancy ρ p ez ep u * c := by
  apply le_of_natural_weights (φ := fun u => realWeightedOrder u F)
    (ψ := fun u => testValuationRealLogDiscrepancy ρ p ez ep u * (c : ℝ))
    (continuous_realWeightedOrder F)
    ((continuous_testValuationRealLogDiscrepancy ρ p ez ep).mul continuous_const)
    (fun c' hc' u => realWeightedOrder_smul hc' u F)
    (fun c' hc' u => by
      simp only [testValuationRealLogDiscrepancy_smul ρ p ez ep hc' u]
      ring) _ hu
  intro w
  have hnat' := hnat w
  have hAeq : ((testValuationLogDiscrepancy ρ p ez ep w).toNat : ℕ∞) =
      testValuationLogDiscrepancy ρ p ez ep w :=
    ENat.natCast_toNat (testValuationLogDiscrepancy_ne_top ρ p ez ep hdet w)
  rw [testValuationRealLogDiscrepancy_natCast ρ p ez ep hdet w]
  by_cases hF0 : F = 0
  · rw [hF0, realWeightedOrder, dite_eq_left rfl]
    positivity
  rw [realWeightedOrder_natCast w hF0]
  rw [← hAeq] at hnat'
  have h' : (F.weightedOrder w).toNat ≤ (testValuationLogDiscrepancy ρ p ez ep w).toNat * c := by
    apply ENat.toNat_le_of_le_natCast
    push_cast
    exact hnat'
  exact_mod_cast h'

omit [IsAlgClosed K] [CharZero K] [IsIntegral Y] [Smooth (Y ↘ Spec (CommRingCat.of K))] in
theorem realWeightedOrder_monomial_one {m : ℕ} (u : Fin m → ℝ) (κ : Fin m →₀ ℕ) :
    realWeightedOrder u (MvPowerSeries.monomial κ (1 : K)) = ∑ i, u i * κ i := by
  classical
  have hne : (MvPowerSeries.monomial κ (1 : K)) ≠ 0 := by
    intro h
    have h' := congrArg (MvPowerSeries.coeff κ) h
    rw [MvPowerSeries.coeff_monomial_same, map_zero] at h'
    exact one_ne_zero h'
  obtain ⟨β, hβ, heq⟩ := exists_coeff_realWeightedOrder u hne
  rw [← heq]
  rw [MvPowerSeries.coeff_monomial] at hβ
  by_cases h : β = κ
  · rw [h]
  · rw [ite_eq_right h] at hβ
    exact absurd rfl hβ

omit [IsAlgClosed K] [CharZero K] [IsIntegral Y] [Smooth (Y ↘ Spec (CommRingCat.of K))] in
/-- In adapted coordinates the real log discrepancy is linear: A(u) = Σ (1 + κ_i) u_i. -/
theorem testValuationRealLogDiscrepancy_of_monomial {T' : Scheme.{u}}
    [T'.Over (Spec (CommRingCat.of K))] (ρ : T' ⟶ Y) [ρ.IsOver (Spec (CommRingCat.of K))]
    (p : T') {m : ℕ}
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk (ρ p)))
      (Y.presheaf.stalk (ρ p)) ≃ₐ[K] MvPowerSeries (Fin m) K)
    (ep : AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
      (T'.presheaf.stalk p) ≃ₐ[K] MvPowerSeries (Fin m) K)
    {g' : MvPowerSeries (Fin m) K} (hg' : IsUnit g') {κ : Fin m →₀ ℕ}
    (hdet : (powerSeriesJacobian (schemeCompletedStalkMap ρ p ez ep)).det =
      g' * MvPowerSeries.monomial κ (1 : K)) {u : Fin m → ℝ} (hu : ∀ i, 0 ≤ u i) :
    testValuationRealLogDiscrepancy ρ p ez ep u = ∑ i, (1 + (κ i : ℝ)) * u i := by
  unfold testValuationRealLogDiscrepancy
  rw [hdet, realWeightedOrder_unit_mul hu hg', realWeightedOrder_monomial_one,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

variable (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

/-- Lemma 1 with real weights on a fixed layer. -/
theorem projectiveHyperplane_lemma1_realWeights
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    {d : ℕ} (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d) :
    ∃ c : ℕ, ∀ (T' : Scheme.{u}) [T'.Over (Spec (CommRingCat.of K))] (ρ : T' ⟶ Y)
      [ρ.IsOver (Spec (CommRingCat.of K))] (p : T'), IsClosed {ρ p} → ∀ {m : ℕ}
      (ez : AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk (ρ p)))
        (Y.presheaf.stalk (ρ p)) ≃ₐ[K] MvPowerSeries (Fin m) K)
      (ep : AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
        (T'.presheaf.stalk p) ≃ₐ[K] MvPowerSeries (Fin m) K),
      (powerSeriesJacobian (schemeCompletedStalkMap ρ p ez ep)).det ≠ 0 →
      ∀ (j : ℕ), 1 ≤ j → ∀ s : Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤), s ≠ 0 →
        ∀ u : Fin m → ℝ, (∀ i, 0 ≤ u i) →
          cartierPullbackRealValuation (j • projectiveHyperplaneCartier e g hg hggen) ρ p ep u s ≤
            testValuationRealLogDiscrepancy ρ p ez ep u * ((c * j : ℕ) : ℝ) := by
  obtain ⟨c, hc⟩ := projectiveHyperplane_lemma1_testValuation e g hg hggen he hn hd
  refine ⟨c, fun T' _ ρ _ p hp m ez ep hdet j hj s hs u hu => ?_⟩
  set F := cartierPullbackTaylor (j • projectiveHyperplaneCartier e g hg hggen) ρ p ep s with hF
  apply le_of_natural_weights (φ := fun u => realWeightedOrder u F)
    (ψ := fun u => testValuationRealLogDiscrepancy ρ p ez ep u * ((c * j : ℕ) : ℝ))
    (continuous_realWeightedOrder F)
    ((continuous_testValuationRealLogDiscrepancy ρ p ez ep).mul continuous_const)
    (fun c' hc' u => realWeightedOrder_smul hc' u F)
    (fun c' hc' u => by
      simp only [testValuationRealLogDiscrepancy_smul ρ p ez ep hc' u]
      ring) _ hu
  intro w
  have hnat := hc T' ρ p hp ez ep w j hj s hs
  rw [cartierPullbackMonomialValuation_eq_taylor] at hnat
  change F.weightedOrder w ≤ testValuationLogDiscrepancy ρ p ez ep w * _ at hnat
  have hA : testValuationLogDiscrepancy ρ p ez ep w ≠ ⊤ := by
    unfold testValuationLogDiscrepancy
    exact WithTop.add_ne_top.mpr ⟨ENat.natCast_ne_top _,
      (MvPowerSeries.weightedOrder_eq_top_iff w).not.mpr hdet⟩
  have hAeq : ((testValuationLogDiscrepancy ρ p ez ep w).toNat : ℕ∞) =
      testValuationLogDiscrepancy ρ p ez ep w := ENat.natCast_toNat hA
  rw [testValuationRealLogDiscrepancy_natCast ρ p ez ep hdet w]
  by_cases hF0 : F = 0
  · rw [hF0, realWeightedOrder, dite_eq_left rfl]
    positivity
  rw [realWeightedOrder_natCast w hF0]
  rw [← hAeq] at hnat
  have h' : (F.weightedOrder w).toNat ≤ (testValuationLogDiscrepancy ρ p ez ep w).toNat * (c * j) := by
    apply ENat.toNat_le_of_le_natCast
    push_cast
    exact hnat
  exact_mod_cast h'

/-- The bounds (8) and (9) of §3.1 with real weights. -/
theorem projectiveHyperplane_minimization_bounds_realWeights
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    {d : ℕ} (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d) {b : ℝ} (hb : 0 < b) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ C : ℝ, 0 < C ∧ ∀ᶠ j : ℕ in atTop,
      0 < Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) ∧
      ∀ x : Y, IsClosed {x} →
      ∀ (bs : Module.Basis (Fin (Module.finrank K
          Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))) K
          Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))
        (T' : Scheme.{u}) [T'.Over (Spec (CommRingCat.of K))] (ρ : T' ⟶ Y)
        [ρ.IsOver (Spec (CommRingCat.of K))] (p : T'), ρ p = x → ∀ {m : ℕ}
        (ez : AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk (ρ p)))
          (Y.presheaf.stalk (ρ p)) ≃ₐ[K] MvPowerSeries (Fin m) K)
        (ep : AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
          (T'.presheaf.stalk p) ≃ₐ[K] MvPowerSeries (Fin m) K),
        (powerSeriesJacobian (schemeCompletedStalkMap ρ p ez ep)).det ≠ 0 →
        ∀ u : Fin m → ℝ, (∀ i, 0 ≤ u i) → ∀ t : ℝ, 0 < t → t ≤ b →
          κ * Real.exp (testValuationRealLogDiscrepancy ρ p ez ep u / (2 * t)) ≤
              minimizationFunctional j t (testValuationRealLogDiscrepancy ρ p ez ep u)
                (fun k => cartierPullbackRealValuation
                  (j • projectiveHyperplaneCartier e g hg hggen) ρ p ep u (bs k)) ∧
            Real.exp (testValuationRealLogDiscrepancy ρ p ez ep u / t -
                C * testValuationRealLogDiscrepancy ρ p ez ep u) ≤
              minimizationFunctional j t (testValuationRealLogDiscrepancy ρ p ez ep u)
                (fun k => cartierPullbackRealValuation
                  (j • projectiveHyperplaneCartier e g hg hggen) ρ p ep u (bs k)) := by
  set ε : ℝ := 1 / (2 * b) with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨κ, hκ, hL2⟩ := projectiveHyperplane_lemma2_testValuation_uniform e g hg hggen he hn hd ε hε
  obtain ⟨c₁, hL1⟩ := projectiveHyperplane_lemma1_testValuation e g hg hggen he hn hd
  obtain ⟨r, hr, -, hlim⟩ := projectiveHyperplane_hilbert_leading e g hg hggen he hn hd
  have hℓ : (0 : ℝ) < r / d.factorial := by
    have : (0 : ℝ) < r := by exact_mod_cast hr
    positivity
  have hNev : ∀ᶠ j : ℕ in atTop,
      0 < Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) := by
    filter_upwards [hlim.eventually (lt_mem_nhds (half_lt_self hℓ))] with j hj
    rcases Nat.eq_zero_or_pos (Module.finrank K
      Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) with h | h
    · rw [h, Nat.cast_zero, zero_div] at hj
      linarith
    · exact h
  refine ⟨κ, hκ, (c₁ : ℝ) + 1, by positivity, ?_⟩
  filter_upwards [hL2, hNev, eventually_ge_atTop 1] with j hU hN hj
  refine ⟨hN, fun x hx bs T' _ ρ _ p hpx m ez ep hdet u hu t ht htb => ?_⟩
  obtain ⟨U, hUdim, hUval⟩ := hU x hx
  have hxc : IsClosed {ρ p} := by rw [hpx]; exact hx
  set A := testValuationRealLogDiscrepancy ρ p ez ep u with hAdef
  have hA0 : 0 ≤ A := testValuationRealLogDiscrepancy_nonneg ρ p ez ep hu
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  set q := ⌊ε * (j : ℝ)⌋₊ with hq
  have hU2 : ∀ s ∈ U, s ≠ 0 → cartierPullbackTaylor (j • projectiveHyperplaneCartier e g hg hggen) ρ p ep s ≠ 0 ∧
      cartierPullbackRealValuation (j • projectiveHyperplaneCartier e g hg hggen) ρ p ep u s ≤ A * q := by
    intro s hs hs0
    have hnat : ∀ w, (cartierPullbackTaylor (j • projectiveHyperplaneCartier e g hg hggen) ρ p ep s).weightedOrder w ≤
        testValuationLogDiscrepancy ρ p ez ep w * (q : ℕ∞) :=
      fun w => (hUval s hs hs0).2 T' ρ p hpx ez ep w
    refine ⟨fun h0 => ?_, realWeightedOrder_le_of_natural ρ p ez ep hdet hnat hu⟩
    have h := hnat 0
    rw [h0, MvPowerSeries.weightedOrder_zero, top_le_iff] at h
    exact WithTop.mul_ne_top (testValuationLogDiscrepancy_ne_top ρ p ez ep hdet 0)
      (ENat.natCast_ne_top q) h
  set W := cartierPullbackRealValuationAbove (j • projectiveHyperplaneCartier e g hg hggen) ρ p ep hu (A * q) with hW
  have hUW : U ⊓ W = ⊥ := by
    rw [eq_bot_iff]
    rintro s ⟨hsU, hsW⟩
    by_contra hs0
    obtain ⟨hne, hle⟩ := hU2 s hsU hs0
    rcases hsW with h | h
    · exact hne h
    · change A * q < cartierPullbackRealValuation (j • projectiveHyperplaneCartier e g hg hggen) ρ p ep u s at h
      linarith
  have : FiniteDimensional K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) := Module.Finite.of_basis bs
  obtain ⟨S, hSU, hSW⟩ := basis_exists_card_not_mem bs U W hUW
  set vals : Fin (Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) → ℝ :=
    fun k => cartierPullbackRealValuation (j • projectiveHyperplaneCartier e g hg hggen) ρ p ep u (bs k) with hvals
  have hthr : ∀ k, bs k ∉ W → vals k ≤ (j : ℝ) * A / (2 * t) := by
    intro k hk
    have hle : cartierPullbackRealValuation (j • projectiveHyperplaneCartier e g hg hggen) ρ p ep u (bs k) ≤ A * q := by
      by_contra hlt
      exact hk (Or.inr (not_le.mp hlt))
    have hfl : (q : ℝ) ≤ ε * j := Nat.floor_le (by positivity)
    have h2 : A * (q : ℝ) ≤ A * (ε * j) := mul_le_mul_of_nonneg_left hfl hA0
    have h3 : A * (ε * j) ≤ (j : ℝ) * A / (2 * t) := by
      rw [hεdef]
      have hbt : 1 / (2 * b) ≤ 1 / (2 * t) := one_div_le_one_div_of_le (by positivity) (by linarith)
      calc A * (1 / (2 * b) * j) ≤ A * (1 / (2 * t) * j) := by gcongr
        _ = (j : ℝ) * A / (2 * t) := by ring
    simp only [hvals]
    linarith
  have hcount2 : Module.finrank K U ≤
      (Finset.univ.filter (fun k => vals k ≤ (j : ℝ) * A / (2 * t))).card :=
    hSU.trans (Finset.card_le_card (fun k hk =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ k, hthr k (hSW k hk)⟩))
  have hcount' : κ * (Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) : ℝ) ≤
      ((Finset.univ.filter (fun k => vals k ≤ (j : ℝ) * A / (2 * t))).card : ℝ) := by
    have h2 : (Module.finrank K U : ℝ) ≤
        ((Finset.univ.filter (fun k => vals k ≤ (j : ℝ) * A / (2 * t))).card : ℝ) := by
      exact_mod_cast hcount2
    linarith
  have h8 := minimizationFunctional_ge_of_count hN j (t := t) (A := A) vals hcount'
  have hsimp : A / t - (j : ℝ) * A / (2 * t) / j = A / (2 * t) := by
    field_simp
    ring
  rw [hsimp] at h8
  have hall : ∀ k, vals k ≤ ((c₁ : ℝ) + 1) * j * A := by
    intro k
    have hnat : ∀ w, (cartierPullbackTaylor (j • projectiveHyperplaneCartier e g hg hggen) ρ p ep (bs k)).weightedOrder w ≤
        testValuationLogDiscrepancy ρ p ez ep w * ((c₁ * j : ℕ) : ℕ∞) :=
      fun w => hL1 T' ρ p hxc ez ep w j hj (bs k) (bs.ne_zero k)
    have h := realWeightedOrder_le_of_natural ρ p ez ep hdet hnat hu
    change vals k ≤ A * ((c₁ * j : ℕ) : ℝ) at h
    push_cast at h
    have hj0' : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    nlinarith
  have h9 := minimizationFunctional_ge_of_all hN j (t := t) (A := A) vals hall
  have hsimp9 : A / t - ((c₁ : ℝ) + 1) * j * A / j = A / t - ((c₁ : ℝ) + 1) * A := by
    field_simp
  rw [hsimp9] at h9
  exact ⟨h8, h9⟩

/-- §3.2 on a fixed adapted layer: with det J a unit times a monomial z^κ, the functional over the
scaled valuations λ u with u in the simplex Σ (1 + κ_i) u_i = 1 either stays above 1 - δ/2, or
attains its infimum at some (λ₀, u₀) with λ₀ ∈ [a_*, a^*]; every scale outside [a_*, a^*] gives a
value above 1 - δ/2. -/
theorem projectiveHyperplane_fixedLayer_attainment
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    {d : ℕ} (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d) {b : ℝ} (hb : 0 < b) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ C : ℝ, 0 < C ∧ ∀ᶠ j : ℕ in atTop, ∀ x : Y, IsClosed {x} →
      ∀ (bs : Module.Basis (Fin (Module.finrank K
          Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))) K
          Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))
        (T' : Scheme.{u}) [T'.Over (Spec (CommRingCat.of K))] (ρ : T' ⟶ Y)
        [ρ.IsOver (Spec (CommRingCat.of K))] (p : T'), ρ p = x → ∀ {m : ℕ}
        (ez : AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk (ρ p)))
          (Y.presheaf.stalk (ρ p)) ≃ₐ[K] MvPowerSeries (Fin m) K)
        (ep : AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
          (T'.presheaf.stalk p) ≃ₐ[K] MvPowerSeries (Fin m) K)
        {g' : MvPowerSeries (Fin m) K}, IsUnit g' → ∀ {κ' : Fin m →₀ ℕ},
        (powerSeriesJacobian (schemeCompletedStalkMap ρ p ez ep)).det =
          g' * MvPowerSeries.monomial κ' (1 : K) →
        ∀ t : ℝ, 0 < t → t ≤ b → ∀ δ : ℝ, 0 < δ → δ < 2 →
          (∀ lam : ℝ, 0 ≤ lam → ∀ v ∈ normalizedWeights (fun i => 1 + (κ' i : ℝ)),
              1 - δ / 2 < minimizationFunctional j t lam (fun k => lam *
                cartierPullbackRealValuation (j • projectiveHyperplaneCartier e g hg hggen)
                  ρ p ep v (bs k))) ∨
          ∃ p₀ ∈ Set.Icc (-Real.log (1 - δ / 2) / C) (2 * b * Real.log (1 / κ)) ×ˢ
              normalizedWeights (fun i => 1 + (κ' i : ℝ)),
            ∀ lam : ℝ, 0 ≤ lam → ∀ v ∈ normalizedWeights (fun i => 1 + (κ' i : ℝ)),
              minimizationFunctional j t p₀.1 (fun k => p₀.1 *
                  cartierPullbackRealValuation (j • projectiveHyperplaneCartier e g hg hggen)
                    ρ p ep p₀.2 (bs k)) ≤
                minimizationFunctional j t lam (fun k => lam *
                  cartierPullbackRealValuation (j • projectiveHyperplaneCartier e g hg hggen)
                    ρ p ep v (bs k)) ∨
              1 - δ / 2 < minimizationFunctional j t lam (fun k => lam *
                cartierPullbackRealValuation (j • projectiveHyperplaneCartier e g hg hggen)
                  ρ p ep v (bs k)) := by
  obtain ⟨κ, hκ, C, hC, hev⟩ := projectiveHyperplane_minimization_bounds_realWeights e g hg hggen
    he hn hd hb
  refine ⟨κ, hκ, C, hC, ?_⟩
  filter_upwards [hev] with j hj
  intro x hx bs T' _ ρ _ p hpx m ez ep g' hg' κ' hdet t ht htb δ hδ hδ2
  have hdet0 : (powerSeriesJacobian (schemeCompletedStalkMap ρ p ez ep)).det ≠ 0 := by
    rw [hdet]
    refine mul_ne_zero hg'.ne_zero fun h => ?_
    have h' := congrArg (MvPowerSeries.coeff κ') h
    classical
    rw [MvPowerSeries.coeff_monomial_same, map_zero] at h'
    exact one_ne_zero h'
  set aLow := -Real.log (1 - δ / 2) / C with haLow
  set aHigh := 2 * b * Real.log (1 / κ) with haHigh
  -- the functional at (lam, v) is the functional of the real weights lam • v
  have hscale : ∀ lam : ℝ, 0 ≤ lam → ∀ v ∈ normalizedWeights (fun i => 1 + (κ' i : ℝ)),
      minimizationFunctional j t lam (fun k => lam * cartierPullbackRealValuation (j • projectiveHyperplaneCartier e g hg hggen) ρ p ep v (bs k)) =
        minimizationFunctional j t (testValuationRealLogDiscrepancy ρ p ez ep (lam • v))
          (fun k => cartierPullbackRealValuation (j • projectiveHyperplaneCartier e g hg hggen) ρ p ep (lam • v) (bs k)) := by
    intro lam hlam v hv
    have hA : testValuationRealLogDiscrepancy ρ p ez ep (lam • v) = lam := by
      rw [testValuationRealLogDiscrepancy_smul ρ p ez ep hlam,
        testValuationRealLogDiscrepancy_of_monomial ρ p ez ep hg' hdet hv.1, hv.2, mul_one]
    rw [hA]
    congr 1
    funext k
    unfold cartierPullbackRealValuation
    rw [realWeightedOrder_smul hlam]
  -- (10): a value at most 1 - δ/2 forces the scale into [a_*, a^*]
  have hinterval : ∀ lam : ℝ, 0 ≤ lam → ∀ v ∈ normalizedWeights (fun i => 1 + (κ' i : ℝ)),
      minimizationFunctional j t lam (fun k => lam * cartierPullbackRealValuation (j • projectiveHyperplaneCartier e g hg hggen) ρ p ep v (bs k)) ≤
        1 - δ / 2 → lam ∈ Set.Icc aLow aHigh := by
    intro lam hlam v hv hF
    have hlv : ∀ i, 0 ≤ (lam • v) i := fun i => by
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg hlam (hv.1 i)
    obtain ⟨h8, h9⟩ := hj.2 x hx bs T' ρ p hpx ez ep hdet0 (lam • v) hlv t ht htb
    rw [hscale lam hlam v hv] at hF
    have hA : testValuationRealLogDiscrepancy ρ p ez ep (lam • v) = lam := by
      rw [testValuationRealLogDiscrepancy_smul ρ p ez ep hlam,
        testValuationRealLogDiscrepancy_of_monomial ρ p ez ep hg' hdet hv.1, hv.2, mul_one]
    have hb10 := logDiscrepancy_bounds_of_functional hκ hC hδ hδ2
      (testValuationRealLogDiscrepancy_nonneg ρ p ez ep hlv) ht htb h8 h9 hF
    rw [hA] at hb10
    exact ⟨hb10.1, hb10.2⟩
  by_cases hne : (Set.Icc aLow aHigh ×ˢ normalizedWeights (fun i => 1 + (κ' i : ℝ))).Nonempty
  · right
    obtain ⟨⟨l₀, v₀⟩, hl₀, hv₀⟩ := hne
    have hlh : aLow ≤ aHigh := le_trans hl₀.1 hl₀.2
    have : Nonempty (Fin m) := by
      by_contra hm
      rw [not_nonempty_iff] at hm
      have h := hv₀.2
      simp only [Finset.univ_eq_empty, Finset.sum_empty] at h
      exact zero_ne_one h
    obtain ⟨p₀, hp₀, hmin⟩ := exists_minimizer_scale_weights
      (fun k => cartierPullbackTaylor (j • projectiveHyperplaneCartier e g hg hggen) ρ p ep (bs k))
      (a := fun i => 1 + (κ' i : ℝ)) (fun i => by positivity) j t hlh
    refine ⟨p₀, hp₀, fun lam hlam v hv => ?_⟩
    by_cases hF : minimizationFunctional j t lam
        (fun k => lam * cartierPullbackRealValuation (j • projectiveHyperplaneCartier e g hg hggen) ρ p ep v (bs k)) ≤ 1 - δ / 2
    · left
      have hmem : (lam, v) ∈ Set.Icc aLow aHigh ×ˢ normalizedWeights (fun i => 1 + (κ' i : ℝ)) :=
        ⟨hinterval lam hlam v hv hF, hv⟩
      have h := hmin (lam, v) hmem
      unfold minimizationFunctional cartierPullbackRealValuation
      simp only [Fintype.card_fin] at h
      exact h
    · right
      exact not_le.mp hF
  · left
    intro lam hlam v hv
    by_contra hF
    exact hne ⟨(lam, v), hinterval lam hlam v hv (not_lt.mp hF), hv⟩

end MixedFujita
