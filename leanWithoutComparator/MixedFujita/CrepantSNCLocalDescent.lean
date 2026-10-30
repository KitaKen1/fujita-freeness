/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.BirationalLocalExtension

/-!
An actual proper smooth model whose crepant boundary has SNC support and
coefficients below the denominator gives klt on the source. Each test prime is
compared on an actual open neighbourhood, using the valuative criterion and
spreading out. No common smooth dominating model is an additional input.
Existence of the original SNC model remains an explicit geometric obligation.
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
  [IsIntegral X] [IsIntegral T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [IsLocallyNoetherian T]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

/-- Every test-prime discrepancy bound follows from the crepant SNC boundary on one actual
proper model, with no common model or local lift supplied. -/
theorem crepant_snc_actual_test_discrepancy_bound
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (cT : EtaleChart K T n)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) = 0)
    (hb : ∀ i, cartierCoefficient
      (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ i) < (d : ℤ))
    {U : Scheme.{u}} [IsIntegral U] [IsLocallyNoetherian U]
    [U.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K))]
    (σ : U ⟶ X) [IsDominant σ] [σ.IsOver (Spec (CommRingCat.of K))]
    (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
    (cU : EtaleChart K U n) (x : CodimensionOnePoint U) :
    -(d : ℤ) < cartierCoefficient
      (logDiscrepancyDivisor n σ hσ c f d D cU etaleCharts_cover) (x : U) := by
  let : Smooth (U ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  let := smoothOverField_codimensionOne_stalk_DVR (K := K) x
  obtain ⟨W, hx, hW, α, hdom, hcomm, hα⟩ :=
    proper_birational_exists_local_birational_extension ρ σ hρ hσ (x : U)
  letI : Nonempty W := ⟨⟨(x : U), hx⟩⟩
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
  let w : W.toScheme := ⟨(x : U), hx⟩
  have hw : Order.coheight w = 1 := by
    exact (coheight_eq_of_stalkMap_bijective W.ι w
      (ConcreteCategory.bijective_of_isIso (W.ι.stalkMap w))).trans x.property
  let p : CodimensionOnePoint W.toScheme := ⟨w, hw⟩
  obtain ⟨cW⟩ : Nonempty (EtaleChart K W.toScheme n) :=
    ⟨Classical.choose (show ∃ e : EtaleChart K W.toScheme n, w ∈ e.U from
      TopologicalSpace.Opens.mem_iSup.mp
        ((etaleCharts_cover (K := K) (X := W.toScheme) (n := n)).symm ▸
          TopologicalSpace.Opens.mem_top w))⟩
  have h := isSNCFamily_actual_discrepancy_bound α hα cT
    (crepantPullbackFormUnit ρ hρ c f cT) d hd
    (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover)
    ξ hinj hξ hsnc hsupport hb cW p
  rw [crepantBoundaryCartier_smooth_recombine,
    ← logDiscrepancyDivisor_comp ρ α hρ hα c f d D cT cW etaleCharts_cover] at h
  have h' : -(d : ℤ) < cartierCoefficient
      (logDiscrepancyDivisor n (W.ι ≫ σ)
        (dominantFunctionFieldAlgHom_comp_bijective σ W.ι hσ hι)
        c f d D cW etaleCharts_cover) (p : W.toScheme) := by
    simpa only [hcomm] using h
  have heq := logDiscrepancyDivisor_comp_coefficient_of_stalkMap_bijective
    σ W.ι hσ hι c f d D cU cW p x.property
      (ConcreteCategory.bijective_of_isIso (W.ι.stalkMap w))
  simpa [heq, p, w] using h'

/-- Given one actual proper SNC model with the strict crepant coefficient bounds, the
source is klt on all actual proper smooth birational test models. -/
theorem logPairIsKlt_of_crepant_snc_model
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (cT : EtaleChart K T n)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) = 0)
    (hb : ∀ i, cartierCoefficient
      (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ i) < (d : ℤ)) :
    LogPairIsKlt c f d D := by
  intro U _ _ _ _ σ _ _ _ hσ cU x hx
  exact crepant_snc_actual_test_discrepancy_bound ρ hρ c f d hd D cT
    ξ hinj hξ hsnc hsupport hb σ hσ cU ⟨x, hx⟩

/-- On one actual proper SNC model, all-model klt is equivalent to finitely many strict
crepant coefficient bounds. Existence of this model is still an explicit input. -/
theorem logPairIsKlt_iff_crepant_snc_coefficients
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (cT : EtaleChart K T n)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) = 0) :
    LogPairIsKlt c f d D ↔ ∀ i, cartierCoefficient
      (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ i) < (d : ℤ) := by
  constructor
  · intro hklt i
    exact logPairIsKlt_crepantBoundary_coefficient_lt ρ hρ c f d D hklt cT ⟨ξ i, hξ i⟩
  · exact logPairIsKlt_of_crepant_snc_model ρ hρ c f d hd D cT ξ hinj hξ hsnc hsupport


end MixedFujita
