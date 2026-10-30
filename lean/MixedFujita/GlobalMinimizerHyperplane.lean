/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.BasisAttainment
public import MixedFujita.SNCWeightDiscrepancyInterval
public import MixedFujita.SmoothPointInteriorWeight
public import MixedFujita.EtaleChartDimension

/-!
The global minimizing pair for the hyperplane class of a smooth closed subvariety of projective
space with zero boundary (step 11, section 3 of the manuscript), from the closedness of the
realization sets and the interior condition (7).

Fix b > 0. There are κ ∈ (0, 1) and c ≥ 1 such that for all large j, every closed point x, every
t ∈ (0, b] and δ ∈ (0, 1): if the realization sets of the tuples of sections of j J at x are
Zariski closed (`RealizationSetsZariskiClosed`, the content of Lemma 3 of the manuscript; a
hypothesis) and some basis of the sections of j J satisfies the interior condition (7) for the
valuation ζ ord_x,

  (1/N) Σ_i exp(ζ m/t − ζ mult_x(s_i)/j) ≤ 1 − δ,

then some basis B* and some weight over the fibre of x on a proper simple normal crossing model
of B* minimize the objective Σ_i exp(A(w)/t − v_i(w)/j) over all bases and all weights on all
their proper simple normal crossing models. The minimum is at most N (1 − δ) and the log
discrepancy of the minimizer lies in the interval
−log(1 − δ/2)/c ≤ A ≤ 2 b log(1/κ) of (10), whose ends do not depend on j, x, t or the basis.

The inputs of the abstract attainment theorem are supplied by the earlier files: the uniform
bounds of section 3.1 for the weights (Lemma 1, the bound (8)), the interior weight from the
exceptional prime of the blow-up of x, and resolution for the models.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial Filter Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Analysis

/-- The sum of the exponentials is N times the functional of section 2.3. -/
theorem sum_exp_eq_mul_minimizationFunctional {N : ℕ} (hN : 0 < N) (j : ℕ) (t A : ℝ)
    (vals : Fin N → ℝ) :
    ∑ i, Real.exp (A / t - vals i / j) = (N : ℝ) * minimizationFunctional j t A vals := by
  unfold minimizationFunctional
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

end Analysis

section Interior

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {m : ℕ} {Y : Scheme.{u}}
  [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension m (Y ↘ Spec (CommRingCat.of K))]
  [IsProper (Y ↘ Spec (CommRingCat.of K))]

/-- The interior datum: on a smooth proper variety with zero boundary, for nonzero sections s_i of
a Cartier divisor, a closed point x and ζ ≥ 0, some profile datum of the tuple (a weight over the
fibre of x on a proper simple normal crossing model constructed by resolution) has objective at
most Σ_i exp(ζ m/t − ζ mult_x(s_i)/j), the objective of the valuation ζ ord_x. -/
theorem exists_sncWeightProfile_le_of_smooth_point (hm : 1 ≤ m) (cY : EtaleChart K Y m)
    (D : CartierDivisor Y) {N : ℕ} (s : Fin N → Γ(D.sheaf, ⊤)) (hs : ∀ i, s i ≠ 0) (x : Y)
    (hx : IsClosed ({x} : Set Y)) {t : ℝ} (ht : 0 < t) {j : ℝ} (hj : 0 < j) {ζ : ℝ}
    (hζ : 0 ≤ ζ) :
    ∃ p ∈ sncWeightProfiles cY (1 : Y.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) D x s,
      (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤
        ∑ i, Real.exp (ζ * m / t - ζ * ((cartierSectionVanishingOrder D x (s i)).toNat : ℝ) / j) := by
  have hsm : Smooth (Y ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth m _
  obtain ⟨β⟩ := smoothScheme_closedPoint_has_localEvaluation (K := K) x hx
  obtain ⟨X, hXi, hXo, hXN, hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ, hinj, hξ, hsnc, hBsupp,
    hGsupp⟩ := exists_proper_snc_model_with cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
      (fun i => cartierSectionZeroDivisor D (s i) (hs i))
  obtain ⟨w, hw0, hwΦ, hle⟩ := exists_sncWeight_objective_le_of_smooth_point π hπ hm cY cX ξ
    hinj hξ hsnc hBsupp D s hs hGsupp x β ht hj hζ
  exact ⟨(∑ k, w k * ((((1 : ℕ) : ℝ) - cartierCoefficient (crepantBoundaryCartier π hπ cY
      (1 : Y.functionFieldˣ) 1 (1 • (smoothCanonicalDivisor cY +
        principalCartierDivisor Y (1 : Y.functionFieldˣ))) cX etaleCharts_cover) (ξ k)) /
      ((1 : ℕ) : ℝ)), fun i => ∑ k, w k * (cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor D (s i) (hs i))) (ξ k) : ℝ)),
    ⟨hs, X, hXi, inferInstance, hXo, hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ, w, hinj, hξ, hsnc,
      hBsupp, hGsupp, hw0, hwΦ, rfl, fun i => rfl⟩, hle⟩

end Interior

section Hyperplane

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n m : ℕ} {Y : Scheme.{u}}
  [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension m (Y ↘ Spec (CommRingCat.of K))]
  (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

/-- The uniform bounds of section 3.1 for the profile data of the bases of the sections of j J:
constants κ ∈ (0, 1) and c₁, c₂ ≥ 1 such that for all large j, every point, every basis and every
datum (a, v) whose objective is at most N (1 − δ) with δ ≥ 0 and t ∈ (0, b],
−log(1 − δ)/c₁ ≤ a ≤ 2 b log(1/κ) and 0 ≤ v_i ≤ c₂ j a. -/
theorem projectiveHyperplane_sncWeightProfiles_bounds
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K)) (hm : 1 ≤ m)
    (cY : EtaleChart K Y m) {b : ℝ} (hb : 0 < b) :
    ∃ κ : ℝ, 0 < κ ∧ κ < 1 ∧ ∃ c₁ c₂ : ℕ, 1 ≤ c₁ ∧ ∀ᶠ j : ℕ in atTop, ∀ (x : Y) {N : ℕ},
      0 < N → ∀ (B : Module.Basis (Fin N) K
        Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)),
      ∀ p ∈ sncWeightProfiles cY (1 : Y.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
        (j • projectiveHyperplaneCartier e g hg hggen) x B,
      ∀ {t δ : ℝ}, 0 < t → t ≤ b → 0 ≤ δ →
        (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤ (N : ℝ) * (1 - δ) →
        -Real.log (1 - δ) / c₁ ≤ p.1 ∧ p.1 ≤ 2 * b * Real.log (1 / κ) ∧
          ∀ i, 0 ≤ p.2 i ∧ p.2 i ≤ (c₂ : ℝ) * j * p.1 := by
  have hsm : Smooth (Y ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth m _
  have hdim : topologicalKrullDim Y = m := etaleChart_topologicalKrullDim cY
  have hAmple : CartierIsAmpleProj K (projectiveHyperplaneCartier e g hg hggen) :=
    projectiveHyperplaneCartier_isAmpleProj e g hg hggen he
  obtain ⟨κ, hκ, hκ1, hev⟩ := projectiveHyperplane_weightExponentialObjective_ge (m := m) e g hg
    hggen he hdim hm hb
  obtain ⟨c₁, hc₁, hlow⟩ := cartierIsAmpleProj_weight_logDiscrepancy_ge (K := K) (n := m) hdim hm
    hAmple
  obtain ⟨c₂, -, hcoef⟩ := cartierIsAmpleProj_model_coefficient_le (K := K) (n := m) hdim hm
    hAmple
  refine ⟨κ, hκ, hκ1, c₁, c₂, hc₁, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with j hj hj1
  intro x N hN B p hp t δ ht htb hδ hL
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  obtain ⟨hs, X, hXi, hXn, hXo, hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ, w, hinj, hξ, hsnc, hBsupp,
    hGsupp, hw0, hwΦ, hA, hv⟩ := hp
  have hobj : weightExponentialObjective
      (fun k => (((1 : ℕ) : ℝ) - cartierCoefficient (crepantBoundaryCartier π hπ cY
        (1 : Y.functionFieldˣ) 1 (1 • (smoothCanonicalDivisor cY +
          principalCartierDivisor Y (1 : Y.functionFieldˣ))) cX etaleCharts_cover) (ξ k)) /
        ((1 : ℕ) : ℝ))
      (fun i k => (cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor
        (j • projectiveHyperplaneCartier e g hg hggen) (B i) (hs i))) (ξ k) : ℝ)) t j w =
      ∑ i, Real.exp (p.1 / t - p.2 i / j) := by
    unfold weightExponentialObjective
    rw [hA]
    exact Finset.sum_congr rfl fun i _ => by rw [hv i]
  refine ⟨?_, ?_, fun i => ⟨?_, ?_⟩⟩
  · rw [hA]
    exact hlow X π hπ cY cX ξ hξ j hj1 hN (fun i => B i) hs ht w hw0 (by rw [hobj]; exact hL)
  · rw [hA]
    have h8 := hj x X π hπ cY cX ξ hinj hξ hsnc hBsupp B hGsupp w hw0 hwΦ ht htb
    exact weight_logDiscrepancy_le_of_exp_bound hκ hκ1 hNpos ht htb hδ h8
      (by rw [hobj]; exact hL)
  · rw [hv i]
    refine Finset.sum_nonneg fun k _ => mul_nonneg (hw0 k) ?_
    exact_mod_cast cartierCoefficient_nonneg_of_isEffective _
      (cartierPullback_isEffective π _ (cartierSectionZeroDivisor_isEffective _ (B i) (hs i))) _
  · rw [hv i, hA, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have h := (hcoef X π hπ cY cX ⟨ξ k, hξ k⟩ j hj1 (B i) (hs i)).2
    calc w k * (cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor
          (j • projectiveHyperplaneCartier e g hg hggen) (B i) (hs i))) (ξ k) : ℝ)
        ≤ w k * ((c₂ : ℝ) * (j : ℝ) * ((((1 : ℕ) : ℝ) - cartierCoefficient
          (crepantBoundaryCartier π hπ cY (1 : Y.functionFieldˣ) 1 (1 • (smoothCanonicalDivisor cY +
            principalCartierDivisor Y (1 : Y.functionFieldˣ))) cX etaleCharts_cover) (ξ k)) /
          ((1 : ℕ) : ℝ))) := mul_le_mul_of_nonneg_left h (hw0 k)
      _ = _ := by ring

/-- Existence of the global minimizing pair for the hyperplane class: see the file header. -/
theorem projectiveHyperplane_exists_global_sncWeight_minimizer
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K)) (hm : 1 ≤ m)
    (cY : EtaleChart K Y m) {b : ℝ} (hb : 0 < b) :
    ∃ κ : ℝ, 0 < κ ∧ κ < 1 ∧ ∃ c : ℕ, 1 ≤ c ∧ ∀ᶠ j : ℕ in atTop, ∀ x : Y,
      IsClosed ({x} : Set Y) → ∀ {t δ : ℝ}, 0 < t → t ≤ b → 0 < δ → δ < 1 →
      RealizationSetsZariskiClosed cY (1 : Y.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
        (j • projectiveHyperplaneCartier e g hg hggen) x →
      (∃ (B₀ : Module.Basis (Fin (Module.finrank K
          Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))) K
          Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) (ζ : ℝ), 0 ≤ ζ ∧
        minimizationFunctional j t (ζ * m) (fun i => ζ * ((cartierSectionVanishingOrder
          (j • projectiveHyperplaneCartier e g hg hggen) x (B₀ i)).toNat : ℝ)) ≤ 1 - δ) →
      ∃ (B : Module.Basis (Fin (Module.finrank K
          Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))) K
          Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)),
        ∃ p ∈ sncWeightProfiles cY (1 : Y.functionFieldˣ) 1
          (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
          (j • projectiveHyperplaneCartier e g hg hggen) x B,
          (∀ (B' : Module.Basis (Fin (Module.finrank K
              Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))) K
              Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)),
            ∀ p' ∈ sncWeightProfiles cY (1 : Y.functionFieldˣ) 1
              (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
              (j • projectiveHyperplaneCartier e g hg hggen) x B',
              (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤ ∑ i, Real.exp (p'.1 / t - p'.2 i / j)) ∧
          (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤ (Module.finrank K
            Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) : ℝ) * (1 - δ) ∧
          -Real.log (1 - δ / 2) / c ≤ p.1 ∧ p.1 ≤ 2 * b * Real.log (1 / κ) := by
  have hsm : Smooth (Y ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth m _
  have hprop : IsProper (Y ↘ Spec (CommRingCat.of K)) := by
    have := polynomialProjectiveToBase_isProper n K
    rw [← he]
    infer_instance
  have hdim : topologicalKrullDim Y = m := etaleChart_topologicalKrullDim cY
  obtain ⟨κ, hκ, hκ1, c₁, c₂, hc₁, hev⟩ := projectiveHyperplane_sncWeightProfiles_bounds e g hg
    hggen he hm cY hb
  obtain ⟨r₀, -, hfin, -⟩ := projectiveHyperplane_hilbert_leading e g hg hggen he hdim hm
  refine ⟨κ, hκ, hκ1, c₁, hc₁, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with j hj hj1
  intro x hx t δ ht htb hδ hδ1 hclosed hstart
  obtain ⟨B₀, ζ, hζ, hF⟩ := hstart
  have hfinj : FiniteDimensional K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) :=
    hfin j
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
  have hc₁pos : (0 : ℝ) < (c₁ : ℝ) := by exact_mod_cast hc₁
  -- the space of sections is not zero
  have hN : 0 < Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) := by
    obtain ⟨σ₀, hσ₀⟩ := projectiveHyperplane_exists_section_nonvanishing e g hg hggen x j
    have hσ₀0 : σ₀ ≠ 0 := by
      rintro rfl
      obtain ⟨f, hf, hu⟩ := (mem_cartierSectionNonvanishingOpen _ 0 x).mp hσ₀
      rw [map_zero] at hu
      exact not_isUnit_zero hu
    exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨σ₀, hσ₀0⟩
  generalize hNdef : Module.finrank K
    Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) = N at B₀ hF hN ⊢
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hklt := smooth_logPairIsKlt_boundary_zero cY (1 : Y.functionFieldˣ) 1 le_rfl
  have hlog : 0 < -Real.log (1 - δ / 2) / c₁ := by
    have h : Real.log (1 - δ / 2) < 0 := Real.log_neg (by linarith) (by linarith)
    exact div_pos (by linarith) hc₁pos
  -- the interior datum from the valuation ζ ord_x
  obtain ⟨p₁, hp₁, hle₁⟩ := exists_sncWeightProfile_le_of_smooth_point hm cY
    (j • projectiveHyperplaneCartier e g hg hggen) (fun i => B₀ i) B₀.ne_zero x hx ht hjpos hζ
  have hval₁ : (∑ i, Real.exp (p₁.1 / t - p₁.2 i / j)) ≤ (N : ℝ) * (1 - δ) :=
    (hle₁.trans_eq (sum_exp_eq_mul_minimizationFunctional hN j t (ζ * m) (fun i =>
      ζ * ((cartierSectionVanishingOrder (j • projectiveHyperplaneCartier e g hg hggen) x
        (B₀ i)).toNat : ℝ)))).trans (mul_le_mul_of_nonneg_left hF hNpos.le)
  have hlevel : (N : ℝ) * (1 - δ) < (N : ℝ) * (1 - δ / 2) := by nlinarith
  obtain ⟨B, p, hp, hmin⟩ := exists_basis_sncWeightProfile_minimizer cY (1 : Y.functionFieldˣ) 1
    le_rfl (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
    hklt (j • projectiveHyperplaneCartier e g hg hggen) x hN B₀ hclosed ht hjpos hlog
    (L := (N : ℝ) * (1 - δ / 2)) (aHigh := 2 * b * Real.log (1 / κ)) (Cq := (c₂ : ℝ) * j)
    (fun B p hp hL => hj x hN B p hp ht htb (by linarith) hL)
    ⟨B₀, p₁, hp₁, lt_of_le_of_lt hval₁ hlevel, lt_of_le_of_lt hval₁ (by nlinarith)⟩
  have hpval : (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤ (N : ℝ) * (1 - δ) :=
    (hmin B₀ p₁ hp₁).trans hval₁
  have hpbd := hj x hN B p hp ht htb (by linarith : (0 : ℝ) ≤ δ / 2) (hpval.trans hlevel.le)
  exact ⟨B, p, hp, hmin, hpval, hpbd.1, hpbd.2.1⟩

end Hyperplane

end MixedFujita
