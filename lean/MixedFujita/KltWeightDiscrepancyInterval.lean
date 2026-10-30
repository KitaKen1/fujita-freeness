/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltWeightLemmaTwo
public import MixedFujita.AmpleSectionFraction
public import MixedFujita.SNCWeightDiscrepancyInterval
public import MixedFujita.SNCWeightSpecializationComparison

/-!
The klt form of (8) and both ends of the discrepancy window, for every ample Cartier divisor
(section 3.1, step 15). A small degree q carries a fixed positive fraction of all sections,
the complementary degree is globally generated, and C q/j ≤ 1/(2b). Lemma 2 gives

  sum_i exp(A/t − v_i/j) ≥ kappa N exp(A/(2t)).

For an objective at most N(1−delta), A ≤ 2 b log(1/kappa). Together with Lemma 1 this supplies
the full uniform compactness bounds used by global minimization. Neither source smoothness nor
a Hilbert limit for the ample divisor is required. Closedness, the interior condition and
the point-centre property remain separate obligations.
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

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} {Y : Scheme.{u}}
  [IsIntegral Y] [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]

/-- The final klt form of (8), uniformly in the point, degree, basis, proper SNC model and real
weight, for an arbitrary ample Cartier divisor. -/
theorem klt_ample_weightExponentialObjective_ge (hn : 1 ≤ n)
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D₀ A : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D₀) (hA : CartierIsAmpleProj K A)
    {b : ℝ} (hb : 0 < b) :
    ∃ κ : ℝ, 0 < κ ∧ κ < 1 ∧ ∀ᶠ j : ℕ in atTop, ∀ x : Y,
      ∀ (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
        [X.Over (Spec (CommRingCat.of K))]
        [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
        (π : X ⟶ Y) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))] [IsProper π]
        (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π))
        (cX : EtaleChart K X n) {r : ℕ} (ξ : Fin r → X),
        Function.Injective ξ → (∀ i, Order.coheight (ξ i) = 1) → IsSNCFamily K n ξ →
        (∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
          cartierCoefficient (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover)
            (z : X) = 0) →
        ∀ {N : ℕ} (B : Module.Basis (Fin N) K Γ((j • A).sheaf, ⊤)),
        (∀ i, ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
          cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor
            (j • A) (B i) (B.ne_zero i))) (z : X) = 0) →
        ∀ w : Fin r → ℝ, (∀ k, 0 ≤ w k) →
        (∃ p ∈ π ⁻¹' ({x} : Set Y), ∀ k, w k ≠ 0 → p ∈ closure ({ξ k} : Set X)) →
        ∀ {t : ℝ}, 0 < t → t ≤ b →
          κ * (N : ℝ) * Real.exp ((∑ k, w k * (((d : ℝ) - cartierCoefficient
              (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d)) / (2 * t)) ≤
            weightExponentialObjective
              (fun k => ((d : ℝ) - cartierCoefficient
                (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d)
              (fun i k => (cartierCoefficient (cartierPullback π
                (cartierSectionZeroDivisor (j • A) (B i) (B.ne_zero i))) (ξ k) : ℝ)) t j w := by
  obtain ⟨C, hC, hc⟩ := klt_weightExponentialObjective_ge hn cY fY d hd D₀ A hklt hA
  obtain ⟨κ, hκ, hκ1, hfrac⟩ := cartierIsAmpleProj_exists_section_fraction
    (etaleChart_topologicalKrullDim cY) hn hA hC hb
  refine ⟨κ, hκ, hκ1, ?_⟩
  filter_upwards [hfrac] with j hj
  obtain ⟨a, q, rfl, hq, hcq, hGG, hdimq⟩ := hj
  intro x X _ _ _ _ π _ _ _ hπ cX r ξ hinj hξ hsnc hBsupp N B hGsupp w hw0 hwΦ t ht htb
  obtain ⟨σ₀, hσ₀unit⟩ := hGG x
  have hσ₀ : x ∈ cartierSectionNonvanishingOpen (a • A) σ₀ :=
    (mem_cartierSectionNonvanishingOpen _ _ x).mpr ⟨_, _, hσ₀unit⟩
  have hjpos : (0 : ℝ) < ((a + q : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < a + q by omega)
  have hmain := hc x a q hq σ₀ hσ₀ X π hπ cX ξ hinj hξ hsnc hBsupp B hGsupp
    w hw0 hwΦ (t := t) hjpos
  let Aw : ℝ := ∑ k, w k * (((d : ℝ) - cartierCoefficient
    (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d)
  have hAw : 0 ≤ Aw := by
    refine Finset.sum_nonneg fun k _ => mul_nonneg (hw0 k) (div_nonneg ?_ (Nat.cast_nonneg d))
    have h := logPairIsKlt_crepantBoundary_coefficient_lt π hπ cY fY d D₀ hklt cX ⟨ξ k, hξ k⟩
    have h' : (cartierCoefficient (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover)
      (ξ k) : ℝ) < d := by exact_mod_cast h
    linarith
  have hNeq : Module.finrank K Γ(((a + q) • A).sheaf, ⊤) = N := by
    rw [Module.finrank_eq_card_basis B, Fintype.card_fin]
  rw [hNeq] at hdimq
  have hcqt : ((C * q : ℕ) : ℝ) / ((a + q : ℕ) : ℝ) ≤ 1 / (2 * t) :=
    hcq.trans (one_div_le_one_div_of_le (by positivity) (by linarith))
  have hexp : Real.exp (Aw / (2 * t)) ≤
      Real.exp (Aw * (1 / t - ((C * q : ℕ) : ℝ) / ((a + q : ℕ) : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have hhalf : 1 / t - 1 / (2 * t) = 1 / (2 * t) := by field_simp; ring
    have hle : 1 / (2 * t) ≤ 1 / t - ((C * q : ℕ) : ℝ) / ((a + q : ℕ) : ℝ) := by linarith
    calc Aw / (2 * t) = Aw * (1 / (2 * t)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hle hAw
  calc κ * (N : ℝ) * Real.exp (Aw / (2 * t)) ≤
      (Module.finrank K Γ((q • A).sheaf, ⊤) : ℝ) *
        Real.exp (Aw * (1 / t - ((C * q : ℕ) : ℝ) / ((a + q : ℕ) : ℝ))) :=
      mul_le_mul hdimq hexp (Real.exp_pos _).le (Nat.cast_nonneg _)
    _ ≤ _ := hmain

/-- The klt form of (8) for actual profile data, uniformly for every basis. -/
theorem klt_ample_sncWeightProfiles_exponential_bound (hn : 1 ≤ n)
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D₀ A : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D₀) (hA : CartierIsAmpleProj K A)
    {b : ℝ} (hb : 0 < b) :
    ∃ κ : ℝ, 0 < κ ∧ κ < 1 ∧ ∀ᶠ j : ℕ in atTop, ∀ (x : Y) {N : ℕ}
      (B : Module.Basis (Fin N) K Γ((j • A).sheaf, ⊤)) p,
      p ∈ sncWeightProfiles cY fY d D₀ (j • A) x B → ∀ {t : ℝ}, 0 < t → t ≤ b →
        κ * (N : ℝ) * Real.exp (p.1 / (2 * t)) ≤
          ∑ i, Real.exp (p.1 / t - p.2 i / j) := by
  obtain ⟨κ, hκ, hκ1, hev⟩ := klt_ample_weightExponentialObjective_ge hn cY fY d hd D₀ A hklt hA hb
  refine ⟨κ, hκ, hκ1, ?_⟩
  filter_upwards [hev] with j hj
  intro x N B p hp t ht htb
  obtain ⟨hs, X, hXi, hXN, hXo, hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ, w, hinj, hξ, hsnc,
    hBsupp, hGsupp, hw0, hwΦ, hAw, hv⟩ := hp
  have h := hj x X π hπ cX ξ hinj hξ hsnc hBsupp B hGsupp w hw0 hwΦ ht htb
  have hobj : weightExponentialObjective
      (fun k => ((d : ℝ) - cartierCoefficient
        (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d)
      (fun i k => (cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor (j • A) (B i) (B.ne_zero i))) (ξ k) : ℝ)) t j w =
      ∑ i, Real.exp (p.1 / t - p.2 i / j) := by
    unfold weightExponentialObjective
    rw [hAw]
    exact Finset.sum_congr rfl fun i _ => by rw [hv i]
  rw [← hAw, hobj] at h
  exact h

/-- Equation (8) in the manuscript's normalized notation, and the uniform positive lower bound
for the normalized functional at every actual profile. -/
theorem klt_ample_minimizationFunctional_bound (hn : 1 ≤ n)
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D₀ A : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D₀) (hA : CartierIsAmpleProj K A)
    {b : ℝ} (hb : 0 < b) :
    ∃ κ : ℝ, 0 < κ ∧ κ < 1 ∧ ∀ᶠ j : ℕ in atTop, ∀ (x : Y) {N : ℕ}, 0 < N →
      ∀ (B : Module.Basis (Fin N) K Γ((j • A).sheaf, ⊤)) p,
      p ∈ sncWeightProfiles cY fY d D₀ (j • A) x B → ∀ {t : ℝ}, 0 < t → t ≤ b →
        κ * Real.exp (p.1 / (2 * b)) ≤ minimizationFunctional j t p.1 p.2 ∧
          κ ≤ minimizationFunctional j t p.1 p.2 := by
  obtain ⟨κ, hκ, hκ1, hev⟩ := klt_ample_sncWeightProfiles_exponential_bound hn cY fY d hd D₀ A
    hklt hA hb
  refine ⟨κ, hκ, hκ1, ?_⟩
  filter_upwards [hev] with j hj
  intro x N hN B p hp t ht htb
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hApos := (sncWeightProfiles_fst_nonneg cY fY hd D₀ (j • A) hklt x B hp).1
  have hstrong := hj x B p hp ht htb
  have hexp : Real.exp (p.1 / (2 * b)) ≤ Real.exp (p.1 / (2 * t)) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_left hApos (by positivity) (by linarith))
  have hnorm : κ * Real.exp (p.1 / (2 * b)) ≤ minimizationFunctional j t p.1 p.2 := by
    unfold minimizationFunctional
    rw [le_div_iff₀ hNpos]
    calc κ * Real.exp (p.1 / (2 * b)) * N = κ * N * Real.exp (p.1 / (2 * b)) := by ring
      _ ≤ κ * N * Real.exp (p.1 / (2 * t)) :=
        mul_le_mul_of_nonneg_left hexp (mul_nonneg hκ.le hNpos.le)
      _ ≤ _ := hstrong
  refine ⟨hnorm, le_trans ?_ hnorm⟩
  have h1 : (1 : ℝ) ≤ Real.exp (p.1 / (2 * b)) := Real.one_le_exp (div_nonneg hApos (by positivity))
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h1 hκ.le

/-- Both ends of the klt discrepancy window and all value bounds for every ample divisor:
the full uniform bounds of section 3.1. -/
theorem klt_ample_sncWeightProfiles_bounds (hn : 1 ≤ n)
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D₀ A : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D₀) (hA : CartierIsAmpleProj K A)
    {b : ℝ} (hb : 0 < b) :
    ∃ κ : ℝ, 0 < κ ∧ κ < 1 ∧ ∃ C : ℕ, 1 ≤ C ∧ ∀ᶠ j : ℕ in atTop,
      ∀ (x : Y) {N : ℕ}, 0 < N →
      ∀ (B : Module.Basis (Fin N) K Γ((j • A).sheaf, ⊤)) p,
        p ∈ sncWeightProfiles cY fY d D₀ (j • A) x B →
        ∀ {t δ : ℝ}, 0 < t → t ≤ b → 0 ≤ δ →
          (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤ (N : ℝ) * (1 - δ) →
          -Real.log (1 - δ) / C ≤ p.1 ∧ p.1 ≤ 2 * b * Real.log (1 / κ) ∧
            ∀ i, 0 ≤ p.2 i ∧ p.2 i ≤ (C : ℝ) * j * p.1 := by
  obtain ⟨κ, hκ, hκ1, hev⟩ := klt_ample_sncWeightProfiles_exponential_bound hn cY fY d hd D₀ A
    hklt hA hb
  obtain ⟨C, hC, hc⟩ := klt_sncWeightProfiles_lower_bounds hn cY fY d hd D₀ A hklt hA
  refine ⟨κ, hκ, hκ1, C, hC, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with j hj hj1
  intro x N hN B p hp t δ ht htb hδ hF
  have hlow := hc j hj1 x hN B p hp ht hF
  refine ⟨hlow.1, ?_, hlow.2⟩
  exact weight_logDiscrepancy_le_of_exp_bound hκ hκ1 (by exact_mod_cast hN) ht htb hδ
    (hj x B p hp ht htb) hF

end MixedFujita
