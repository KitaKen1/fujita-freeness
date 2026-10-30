/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltSmoothPointInterior
public import MixedFujita.GlobalMinimizerHyperplane

/-!
From the ordinary-point objective to actual SNC profiles and their infimum on a possibly singular
source. The point lies in the reference chart and the boundary vanishes locally there. Extraction
has normalized discrepancy n, vanishing orders dominate ordinary multiplicity, and retraction to
a proper SNC model cannot increase the objective. The model is constructed by resolution.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter Topology
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

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsSeparated (Y ↘ Spec (CommRingCat.of K))]

/-- The ordinary-point objective bounds an actual profile objective on a constructed SNC model.
The source is only required to be smooth and boundary-free near the chosen point. -/
theorem exists_sncWeightProfile_le_of_chart_point (hn : 1 ≤ n)
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D₀ D : CartierDivisor Y) {N : ℕ} (s : Fin N → Γ(D.sheaf, ⊤)) (hs : ∀ i, s i ≠ 0)
    (x : Y) (hx : x ∈ cY.U) (β : Y.presheaf.stalk x →ₐ[K] K)
    (hD : D₀.IsLocalEquationAt x (fY ^ d))
    {t j lam : ℝ} (ht : 0 < t) (hj : 0 < j) (hlam : 0 ≤ lam) :
    ∃ p ∈ sncWeightProfiles cY fY d D₀ D x s,
      (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤
        ∑ i, Real.exp (lam * n / t -
          lam * ((cartierSectionVanishingOrder D x (s i)).toNat : ℝ) / j) := by
  obtain ⟨X, hXi, hXo, hXN, hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ, hinj, hξ, hsnc,
    hBsupp, hGsupp⟩ := exists_proper_snc_model_with cY fY d D₀
      (fun i => cartierSectionZeroDivisor D (s i) (hs i))
  obtain ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, he, hecU, hσe, hJ⟩ :=
    exists_extraction_prime_at_chart_rational_point hn cY x hx β
  have hA := logDiscrepancyDivisor_coefficient_of_local_boundary_zero σ hσ cY fY d D₀
    cU e hecU (by simpa only [hσe] using hD)
  rw [hJ] at hA
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hAnorm : ((d : ℝ) + cartierCoefficient
      (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU etaleCharts_cover) e) / d = n := by
    rw [hA]
    push_cast
    field_simp
    ring
  obtain ⟨w, hw0, hwΦ, hle⟩ := exists_sncWeight_objective_le_of_test_prime π hπ cY fY d hd D₀
    cX ξ hinj hξ hsnc hBsupp (fun i => cartierSectionZeroDivisor D (s i) (hs i)) hGsupp
    σ hσ cU ⟨e, he⟩ x (by rw [hσe]; exact subset_closure rfl) ht j lam hlam
  have hsm : Smooth (U ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have := smoothOverField_codimensionOne_stalk_DVR (K := K) (⟨e, he⟩ : CodimensionOnePoint U)
  have hbound : weightExponentialObjective
      (fun k => ((d : ℝ) - cartierCoefficient
        (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d)
      (fun i k => (cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor D (s i) (hs i))) (ξ k) : ℝ)) t j w ≤
      ∑ i, Real.exp (lam * n / t -
        lam * ((cartierSectionVanishingOrder D x (s i)).toNat : ℝ) / j) := by
    refine hle.trans (Finset.sum_le_sum fun i _ => Real.exp_le_exp.mpr ?_)
    have hv := cartierPullback_sectionZeroDivisor_coefficient_ge_vanishingOrder σ D
      (s i) (hs i) (⟨e, he⟩ : CodimensionOnePoint U)
    change ((cartierSectionVanishingOrder D (σ e) (s i)).toNat : ℤ) ≤
      cartierCoefficient (cartierPullback σ (cartierSectionZeroDivisor D (s i) (hs i))) e at hv
    rw [hσe] at hv
    have hv' : ((cartierSectionVanishingOrder D x (s i)).toNat : ℝ) ≤
        (cartierCoefficient (cartierPullback σ (cartierSectionZeroDivisor D (s i) (hs i))) e : ℝ) := by
      exact_mod_cast hv
    rw [hAnorm]
    exact sub_le_sub_left
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hv' hlam) hj.le) _
  exact ⟨(∑ k, w k * (((d : ℝ) - cartierCoefficient
      (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d),
    fun i => ∑ k, w k * (cartierCoefficient (cartierPullback π
      (cartierSectionZeroDivisor D (s i) (hs i))) (ξ k) : ℝ)),
    ⟨hs, X, hXi, inferInstance, hXo, hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ, w, hinj, hξ, hsnc,
      hBsupp, hGsupp, hw0, hwΦ, rfl, fun i => rfl⟩, hbound⟩

/-- At a boundary-free chart point the infimum is at most the ordinary-point objective. -/
theorem sncWeightInfimum_le_of_chart_point (hn : 1 ≤ n)
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D₀ D : CartierDivisor Y) {N : ℕ} (B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤))
    (x : Y) (hx : x ∈ cY.U) (β : Y.presheaf.stalk x →ₐ[K] K)
    (hD : D₀.IsLocalEquationAt x (fY ^ d))
    {t j lam : ℝ} (ht : 0 < t) (hj : 0 < j) (hlam : 0 ≤ lam) :
    sncWeightInfimum cY fY d D₀ D x N t j ≤
      ∑ i, Real.exp (lam * n / t -
        lam * ((cartierSectionVanishingOrder D x (B i)).toNat : ℝ) / j) := by
  obtain ⟨p, hp, hle⟩ := exists_sncWeightProfile_le_of_chart_point hn cY fY d hd D₀ D B B.ne_zero
    x hx β hD ht hj hlam
  exact (sncWeightInfimum_le cY fY d D₀ D x t j B hp).trans hle

/-- The normalized ordinary-point inequality (7) yields the corresponding infimum gap. -/
theorem sncWeightInfimum_le_of_chart_interior (hn : 1 ≤ n)
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D₀ D : CartierDivisor Y) {N : ℕ} (hN : 0 < N)
    (B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤)) (x : Y) (hx : x ∈ cY.U)
    (β : Y.presheaf.stalk x →ₐ[K] K) (hD : D₀.IsLocalEquationAt x (fY ^ d))
    {j : ℕ} (hj : 0 < j) {t lam δ : ℝ} (ht : 0 < t) (hlam : 0 ≤ lam)
    (hstart : minimizationFunctional j t (lam * n)
      (fun i => lam * ((cartierSectionVanishingOrder D x (B i)).toNat : ℝ)) ≤ 1 - δ) :
    sncWeightInfimum cY fY d D₀ D x N t j ≤ (N : ℝ) * (1 - δ) := by
  have hjr : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have h := sncWeightInfimum_le_of_chart_point hn cY fY d hd D₀ D B x hx β hD ht hjr hlam
  rw [sum_exp_eq_mul_minimizationFunctional hN] at h
  exact h.trans (mul_le_mul_of_nonneg_left hstart (Nat.cast_nonneg N))

end MixedFujita
