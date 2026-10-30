/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.NormalizedProfileRealization
public import MixedFujita.SmoothPointInteriorWeight

/-!
The zero profile is a normalized profile at every closed point of a smooth variety of dimension
n ≥ 1 with zero boundary, for every basis of the sections (step 9). At a closed point y, the
exceptional prime e of the blow-up of y in a centred chart has order one along a centred
coordinate u. On a proper simple normal crossing model of the pair, of the zero divisors of the
sections and of the principal divisor of u, the retraction of e is a weight over the fibre of y
whose value on div u is the order one of u along e; so the weight is not zero and its log
discrepancy is positive (the pair is klt). Hence 0 ∈ Q(y)
(`zero_mem_sncWeightNormalizedProfiles`), and the realization sets of profiles with no positive
entry contain all closed points.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Filter Topology
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
  [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsSeparated (Y ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of K))]

/-- The zero profile is realized at every closed point, for every basis of the sections. -/
theorem zero_mem_sncWeightNormalizedProfiles (hn : 1 ≤ n) (cY : EtaleChart K Y n)
    (D : CartierDivisor Y) {N : ℕ} (B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤)) (y : Y)
    (hy : IsClosed ({y} : Set Y)) :
    (0 : Fin N → ℝ) ∈ sncWeightNormalizedProfiles cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) D N y := by
  classical
  have : Smooth (Y ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  obtain ⟨β⟩ := smoothScheme_closedPoint_has_localEvaluation (K := K) y hy
  obtain ⟨c, hyc⟩ : ∃ c : EtaleChart K Y n, y ∈ c.U :=
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := Y) (n := n)).symm ▸ Opens.mem_top y)
  set c' := etaleChartCentered c (rationalAffineGermPoint y hyc β) with hc'
  have hw : (fun _ : Fin n => 1) ≠ (0 : Fin n → ℕ) := fun h => by
    have h1 := congrFun h ⟨0, hn⟩
    simp at h1
  obtain ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, g, w', hg, hgw, he, hecU, hxe, hord,
    -⟩ := exists_toric_extraction_model c' y hyc (fun _ => 1) hw
      (fun a _ => etaleChartCentered_germ_not_isUnit c y hyc β a)
  set a₀ : Fin n := ⟨0, hn⟩
  have hw'1 : w' a₀ = 1 := Nat.dvd_one.mp ⟨g, (hgw a₀).trans (Nat.mul_comm _ _)⟩
  set u₀ : Y.functionFieldˣ := etaleChartCoordinateRationalUnit c' a₀ with hu₀
  set H : CartierDivisor Y := principalCartierDivisor Y u₀ with hH
  have hBne : ∀ i, B i ≠ 0 := B.ne_zero
  set G : Fin (N + 1) → CartierDivisor Y :=
    Fin.cons H fun i => cartierSectionZeroDivisor D (B i) (hBne i) with hG
  set D₀ := (1 : ℕ) • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))
    with hD₀
  obtain ⟨X, hXi, hXo, hXN, hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ, hinj, hξ, hsnc, hBsupp,
    hGsupp⟩ := exists_proper_snc_model_with cY (1 : Y.functionFieldˣ) 1 D₀ G
  obtain ⟨w, hw0, hwΦ, hval, -⟩ := exists_sncWeight_data_of_test_prime π hπ cY
    (1 : Y.functionFieldˣ) 1 le_rfl D₀ cX ξ hinj hξ hsnc hBsupp G hGsupp σ hσ cU ⟨e, he⟩ y hxe
  -- the value of the retraction on div u₀ is the order one of u₀ along e
  have hHe : cartierCoefficient (cartierPullback σ H) e = 1 := by
    have hloc := cartierPullback_isLocalEquationAt σ H e
      (CartierDivisor.isLocalEquationAt_principalCartierDivisor (σ e) u₀)
    rw [cartierCoefficient_eq_ord hloc]
    have h1 := hord a₀
    rw [hw'1] at h1
    exact_mod_cast h1
  have hwne : ∃ k, w k ≠ 0 := by
    by_contra hno
    push Not at hno
    have h := hval 0
    have hG0 : G 0 = H := rfl
    rw [hG0, hHe] at h
    simp [hno] at h
  -- positivity of the log discrepancy of the weight (klt)
  have hklt := smooth_logPairIsKlt_boundary_zero cY (1 : Y.functionFieldˣ) 1 le_rfl
  have hApos : 0 < ∑ k, w k * ((((1 : ℕ) : ℝ) - cartierCoefficient
      (crepantBoundaryCartier π hπ cY (1 : Y.functionFieldˣ) 1 D₀ cX etaleCharts_cover) (ξ k)) /
        ((1 : ℕ) : ℝ)) := by
    have hpos : ∀ k, 0 < (((1 : ℕ) : ℝ) - cartierCoefficient
        (crepantBoundaryCartier π hπ cY (1 : Y.functionFieldˣ) 1 D₀ cX etaleCharts_cover) (ξ k)) /
          ((1 : ℕ) : ℝ) := by
      intro k
      have h1 := logPairIsKlt_crepantBoundary_coefficient_lt π hπ cY (1 : Y.functionFieldˣ) 1 D₀
        hklt cX ⟨ξ k, hξ k⟩
      have h2 : ((cartierCoefficient (crepantBoundaryCartier π hπ cY (1 : Y.functionFieldˣ) 1 D₀
          cX etaleCharts_cover) (ξ k) : ℤ) : ℝ) < ((1 : ℕ) : ℝ) := by exact_mod_cast h1
      rw [Nat.cast_one, div_one]
      rw [Nat.cast_one] at h2
      linarith
    obtain ⟨k₀, hk₀⟩ := hwne
    have hk₀pos : 0 < w k₀ := lt_of_le_of_ne (hw0 k₀) (Ne.symm hk₀)
    calc (0 : ℝ) < w k₀ * ((((1 : ℕ) : ℝ) - cartierCoefficient
          (crepantBoundaryCartier π hπ cY (1 : Y.functionFieldˣ) 1 D₀ cX etaleCharts_cover)
            (ξ k₀)) / ((1 : ℕ) : ℝ)) := mul_pos hk₀pos (hpos k₀)
      _ ≤ _ := Finset.single_le_sum (fun k _ => mul_nonneg (hw0 k) (hpos k).le)
          (Finset.mem_univ k₀)
  refine ⟨B, (∑ k, w k * ((((1 : ℕ) : ℝ) - cartierCoefficient
      (crepantBoundaryCartier π hπ cY (1 : Y.functionFieldˣ) 1 D₀ cX etaleCharts_cover) (ξ k)) /
        ((1 : ℕ) : ℝ)), fun i => ∑ k, w k * (cartierCoefficient (cartierPullback π
          (cartierSectionZeroDivisor D (B i) (hBne i))) (ξ k) : ℝ)),
    ⟨hBne, X, hXi, inferInstance, hXo, hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ, w, hinj, hξ, hsnc,
      hBsupp, fun i => hGsupp i.succ, hw0, hwΦ, rfl, fun i => rfl⟩, hApos, fun i => ?_⟩
  rw [Pi.zero_apply, zero_mul]
  dsimp only
  refine Finset.sum_nonneg fun k _ => mul_nonneg (hw0 k) ?_
  exact_mod_cast cartierCoefficient_nonneg_of_isEffective _
    (cartierPullback_isEffective π _ (cartierSectionZeroDivisor_isEffective D (B i) (hBne i)))
      (ξ k)

end MixedFujita
