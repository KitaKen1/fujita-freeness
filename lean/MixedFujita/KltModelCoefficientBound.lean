/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCKltWeightLemmaOne
public import MixedFujita.HironakaSNCModelExistence
public import MixedFujita.CrepantSNCLocalDescent
public import MixedFujita.ProjectiveCurveCohomology

/-!
Lemma 1 for actual prime divisors over a projective klt source (section 3.1, step 15).

Resolve the pair once, use the projective SNC model to obtain a uniform bound for every section
of the pullback of L, and compare an arbitrary test prime to that model on an open neighbourhood.
The valuative criterion and spreading give the local map; its open immersion preserves the
prime coefficient and discrepancy. Thus the bound does not require a common dominating model,
smoothness of the source, or ampleness of the pullback of L.
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

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} {Y : Scheme.{u}}
  [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]

/-- A single proper SNC model carrying an ample divisor gives the uniform coefficient bound on
all actual smooth birational test models of the source. -/
theorem klt_model_coefficient_le_of_snc_model
    (hn : 1 ≤ n) (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D L : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D)
    {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T]
    [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (ρ : T ⟶ Y) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (cT : EtaleChart K T n) {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ cY fY d D cT etaleCharts_cover) (z : T) = 0)
    {J : CartierDivisor T} (hJ : CartierIsAmpleProj K J) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (U : Scheme.{u}) [IsIntegral U] [IsLocallyNoetherian U]
      [U.Over (Spec (CommRingCat.of K))]
      [SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K))]
      (σ : U ⟶ Y) [IsDominant σ] [σ.IsOver (Spec (CommRingCat.of K))]
      (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
      (cU : EtaleChart K U n) (z : CodimensionOnePoint U) (j : ℕ), 1 ≤ j →
      ∀ (s : Γ((j • L).sheaf, ⊤)) (hs : s ≠ 0),
        (0 : ℝ) ≤ ((d : ℝ) - cartierCoefficient (crepantBoundaryCartier σ hσ cY fY d D cU
          etaleCharts_cover) (z : U)) / d ∧
        (cartierCoefficient (cartierPullback σ (cartierSectionZeroDivisor (j • L) s hs))
          (z : U) : ℝ) ≤ (C : ℝ) * j *
          (((d : ℝ) - cartierCoefficient (crepantBoundaryCartier σ hσ cY fY d D cU
            etaleCharts_cover) (z : U)) / d) := by
  classical
  have : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  let fT := crepantPullbackFormUnit ρ hρ cY fY cT
  let BT := crepantBoundaryCartier ρ hρ cY fY d D cT etaleCharts_cover
  have hb : ∀ i, cartierCoefficient BT (ξ i) < (d : ℤ) := fun i =>
    logPairIsKlt_crepantBoundary_coefficient_lt ρ hρ cY fY d D hklt cT ⟨ξ i, hξ i⟩
  obtain ⟨C, hC, hc⟩ := isSNCFamily_model_coefficient_le (etaleChart_topologicalKrullDim cT) hn
    hJ (cartierPullback ρ L) cT fT d hd BT ξ hinj hξ hsnc hsupport hb
  refine ⟨C, hC, fun U _ _ _ _ σ _ _ hσ cU z j hj s hs => ?_⟩
  letI : Smooth (U ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  letI := smoothOverField_codimensionOne_stalk_DVR (K := K) z
  obtain ⟨W, hz, hW, α, hdom, hcomm, hα⟩ :=
    proper_birational_exists_local_birational_extension ρ σ hρ hσ (z : U)
  letI : Nonempty W := ⟨⟨(z : U), hz⟩⟩
  letI : IsIntegral W.toScheme := hW
  letI : W.toScheme.Over (Spec (CommRingCat.of K)) := ⟨W.ι ≫ (U ↘ Spec (CommRingCat.of K))⟩
  haveI : W.ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  letI : IsDominant α := hdom
  letI : IsDominant W.ι := ⟨W.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  haveI : SmoothOfRelativeDimension n (W.toScheme ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := W.ι) (S := Spec (CommRingCat.of K))]
    have h : SmoothOfRelativeDimension (0 + n) (W.ι ≫ (U ↘ Spec (CommRingCat.of K))) :=
      inferInstance
    simpa only [Nat.zero_add] using h
  haveI : α.IsOver (Spec (CommRingCat.of K)) := by
    apply (Scheme.Hom.isOver_iff (Spec (CommRingCat.of K))).mpr
    rw [← HomIsOver.comp_over (f := ρ) (S := Spec (CommRingCat.of K)),
      ← Category.assoc, hcomm, Category.assoc,
      HomIsOver.comp_over (f := σ) (S := Spec (CommRingCat.of K)),
      HomIsOver.comp_over (f := W.ι) (S := Spec (CommRingCat.of K))]
  have hι : Function.Bijective (dominantFunctionFieldAlgHom (K := K) W.ι) :=
    dominantFunctionFieldMap_bijective_of_isOpenImmersion W.ι
  let w : W.toScheme := ⟨(z : U), hz⟩
  have hw : Order.coheight w = 1 :=
    (coheight_eq_of_stalkMap_bijective W.ι w
      (ConcreteCategory.bijective_of_isIso (W.ι.stalkMap w))).trans z.property
  let p : CodimensionOnePoint W.toScheme := ⟨w, hw⟩
  haveI : IsDiscreteValuationRing (U.presheaf.stalk (W.ι (p : W.toScheme))) := by
    change IsDiscreteValuationRing (U.presheaf.stalk (z : U))
    infer_instance
  letI : Smooth (W.toScheme ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  letI := smoothOverField_codimensionOne_stalk_DVR (K := K) p
  obtain ⟨cW⟩ : Nonempty (EtaleChart K W.toScheme n) :=
    ⟨Classical.choose (show ∃ e : EtaleChart K W.toScheme n, w ∈ e.U from
      Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := W.toScheme) (n := n)).symm ▸
        Opens.mem_top w))⟩
  let sT := cartierSectionCast (cartierPullback_nsmul ρ L j)
    (cartierDominantPullbackSection ρ (j • L) s)
  have hsT : sT ≠ 0 := cartierSectionCast_ne_zero _ _
    (cartierDominantPullbackSection_ne_zero ρ (j • L) s hs)
  have hZs : cartierSectionZeroDivisor (j • cartierPullback ρ L) sT hsT =
      cartierPullback ρ (cartierSectionZeroDivisor (j • L) s hs) :=
    (cartierSectionCast_zeroDivisor _ _ _).trans
      (cartierDominantPullbackSection_zeroDivisor ρ (j • L) s hs)
  have hdisc : cartierCoefficient (logDiscrepancyDivisor n α hα cT fT d
      (d • (smoothCanonicalDivisor cT + principalCartierDivisor T fT) + BT)
      cW etaleCharts_cover) (p : W.toScheme) =
      cartierCoefficient (logDiscrepancyDivisor n σ hσ cY fY d D cU etaleCharts_cover) (z : U) := by
    change cartierCoefficient (logDiscrepancyDivisor n α hα cT
      (crepantPullbackFormUnit ρ hρ cY fY cT) d
      (d • (smoothCanonicalDivisor cT + principalCartierDivisor T
        (crepantPullbackFormUnit ρ hρ cY fY cT)) +
        crepantBoundaryCartier ρ hρ cY fY d D cT etaleCharts_cover) cW etaleCharts_cover)
      (p : W.toScheme) = _
    rw [crepantBoundaryCartier_smooth_recombine,
      ← logDiscrepancyDivisor_comp ρ α hρ hα cY fY d D cT cW etaleCharts_cover]
    have h' := logDiscrepancyDivisor_comp_coefficient_of_stalkMap_bijective σ W.ι hσ hι
      cY fY d D cU cW p z.property (ConcreteCategory.bijective_of_isIso (W.ι.stalkMap w))
    change cartierCoefficient (logDiscrepancyDivisor n (W.ι ≫ σ)
      (dominantFunctionFieldAlgHom_comp_bijective σ W.ι hσ hι) cY fY d D cW etaleCharts_cover)
      (p : W.toScheme) = cartierCoefficient
        (logDiscrepancyDivisor n σ hσ cY fY d D cU etaleCharts_cover) (z : U) at h'
    simpa only [hcomm] using h'
  have hcrep : cartierCoefficient (crepantBoundaryCartier α hα cT fT d
      (d • (smoothCanonicalDivisor cT + principalCartierDivisor T fT) + BT)
      cW etaleCharts_cover) (p : W.toScheme) =
      cartierCoefficient (crepantBoundaryCartier σ hσ cY fY d D cU etaleCharts_cover) (z : U) := by
    rw [crepantBoundaryCartier_eq_neg_discrepancy, crepantBoundaryCartier_eq_neg_discrepancy,
      cartierCoefficient_neg, cartierCoefficient_neg, hdisc]
  have h := hc W.toScheme α hα cW p j hj sT hsT
  have hdiv : cartierPullback α (cartierPullback ρ (cartierSectionZeroDivisor (j • L) s hs)) =
      cartierPullback W.ι (cartierPullback σ (cartierSectionZeroDivisor (j • L) s hs)) := by
    simp only [← cartierPullback_comp, hcomm]
  rw [hcrep, hZs, hdiv,
    cartierCoefficient_pullback_of_stalkMap_bijective W.ι p z.property
      (ConcreteCategory.bijective_of_isIso (W.ι.stalkMap w))] at h
  exact h

/-- Lemma 1 on a projective klt source: the SNC model and its ample divisor are supplied by the
vendored resolution, and one constant works for every degree, section and actual test prime. -/
theorem klt_model_coefficient_le [IsLocallyNoetherian Y]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
    (hn : 1 ≤ n) (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D L : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D)
    {H : CartierDivisor Y} (hH : CartierIsAmpleProj K H) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (U : Scheme.{u}) [IsIntegral U] [IsLocallyNoetherian U]
      [U.Over (Spec (CommRingCat.of K))]
      [SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K))]
      (σ : U ⟶ Y) [IsDominant σ] [σ.IsOver (Spec (CommRingCat.of K))]
      (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
      (cU : EtaleChart K U n) (z : CodimensionOnePoint U) (j : ℕ), 1 ≤ j →
      ∀ (s : Γ((j • L).sheaf, ⊤)) (hs : s ≠ 0),
        (0 : ℝ) ≤ ((d : ℝ) - cartierCoefficient (crepantBoundaryCartier σ hσ cY fY d D cU
          etaleCharts_cover) (z : U)) / d ∧
        (cartierCoefficient (cartierPullback σ (cartierSectionZeroDivisor (j • L) s hs))
          (z : U) : ℝ) ≤ (C : ℝ) * j *
          (((d : ℝ) - cartierCoefficient (crepantBoundaryCartier σ hσ cY fY d D cU
            etaleCharts_cover) (z : U)) / d) := by
  obtain ⟨-, -, N, e, he, hbase, -⟩ := id hH
  have : IsProper (Y ↘ Spec (CommRingCat.of K)) :=
    polynomialProjective_closedImmersion_isProper_over_field e hbase
  obtain ⟨T, _, _, _, _, ρ, _, _, _, hρ, cT, r, ξ, hinj, hξ, hsnc, hsupport, -, J, hJ⟩ :=
    exists_projective_snc_model_with_ample cY fY d D (fun i : PEmpty.{1} => i.elim) hH
  exact klt_model_coefficient_le_of_snc_model hn cY fY d hd D L hklt ρ hρ cT ξ hinj hξ hsnc
    hsupport (cartierIsAmpleProj_of_veryAmple hJ)

/-- For every actual profile of a tuple, Lemma 1 bounds all values and gives the uniform lower
end of the discrepancy window. The constant is independent of the point, degree and tuple. -/
theorem klt_sncWeightProfiles_lower_bounds
    [IsLocallyNoetherian Y] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
    (hn : 1 ≤ n) (c₀ : EtaleChart K Y n) (f₀ : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D L : CartierDivisor Y) (hklt : LogPairIsKlt c₀ f₀ d D)
    {H : CartierDivisor Y} (hH : CartierIsAmpleProj K H) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (j : ℕ), 1 ≤ j → ∀ (x : Y) {N : ℕ}, 0 < N →
      ∀ (s : Fin N → Γ((j • L).sheaf, ⊤)) p,
        p ∈ sncWeightProfiles c₀ f₀ d
          D (j • L) x s →
        ∀ {t δ : ℝ}, 0 < t →
          (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤ (N : ℝ) * (1 - δ) →
          -Real.log (1 - δ) / C ≤ p.1 ∧
            ∀ i, 0 ≤ p.2 i ∧ p.2 i ≤ (C : ℝ) * j * p.1 := by
  obtain ⟨C, hC, hc⟩ := klt_model_coefficient_le hn c₀ f₀ d hd D L hklt hH
  refine ⟨C, hC, fun j hj x N hN s p hp t δ ht hF => ?_⟩
  obtain ⟨hs, T, hTi, hTN, hTo, hTs, ρ, hρd, hρo, hρp, hρ, cT, q, η, w, hηinj, hη, hηsnc,
    hTB, hTG, hw, hwΦ, hA, hv⟩ := hp
  let a : Fin q → ℝ := fun k => ((d : ℝ) - cartierCoefficient (crepantBoundaryCartier ρ hρ c₀
    f₀ d D
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
