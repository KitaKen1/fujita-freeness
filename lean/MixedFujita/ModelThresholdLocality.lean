/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SmoothRestriction

/-!
Locality of the model form of lct_x ≤ 1/M (step 9, restriction theorem).

A bad point of a smooth variety Y lying in an open subscheme V is a bad point of V
(`modelThresholdBadAt_restrict_opens`): restrict the test model to the preimage of V; the prime
stays (its image is a generization of the point), and the log discrepancy and the orders are
computed on the local rings, which do not change. Together with
`modelThresholdBadAt_of_openImmersion` (check-315), badness is local:
`modelThresholdBadAt_opens_iff`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Opens

variable {K : Type u} [Field K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))] [SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of K))]
  (V : Y.Opens) [Nonempty V] [V.toScheme.Over (Spec (CommRingCat.of K))]
  [V.ι.IsOver (Spec (CommRingCat.of K))] [IsDominant V.ι]
  [SmoothOfRelativeDimension n (V.toScheme ↘ Spec (CommRingCat.of K))]

/-- A bad point of Y lying in an open subscheme V is a bad point of V: restrict the test model to
the preimage of V. -/
theorem modelThresholdBadAt_restrict_opens (cY : EtaleChart K Y n) (cV : EtaleChart K V.toScheme n)
    (y : Y) (hy : y ∈ V) {J : Type*} (gY : J → Y.functionField)
    (gV : J → V.toScheme.functionField)
    (hg : ∀ i, (dominantFunctionFieldMap V.ι).hom (gY i) = gV i) (M : ℕ)
    (h : ModelThresholdBadAt cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) y gY
      M) :
    ModelThresholdBadAt cV (1 : V.toScheme.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cV + principalCartierDivisor V.toScheme
        (1 : V.toScheme.functionFieldˣ))) ⟨y, hy⟩ gV M := by
  obtain ⟨T, hTi, hTn, hTo, hTs, σ, hσd, hσo, hσ, cT, e, hye, hApos, hineq⟩ := h
  -- the part of the test model over V
  have heV : σ (e : T) ∈ V := (specializes_iff_mem_closure.mpr hye).mem_open V.isOpen hy
  let T' : T.Opens := σ ⁻¹ᵁ V
  have : Nonempty T' := ⟨⟨(e : T), heV⟩⟩
  have : IsIntegral T'.toScheme := isIntegral_of_isOpenImmersion T'.ι
  let : T'.toScheme.Over (Spec (CommRingCat.of K)) := ⟨T'.ι ≫ (T ↘ Spec (CommRingCat.of K))⟩
  have : T'.ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  have : IsDominant T'.ι := ⟨T'.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  have : SmoothOfRelativeDimension n (T'.toScheme ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := T'.ι) (S := Spec (CommRingCat.of K))]
    have h : SmoothOfRelativeDimension (0 + n) (T'.ι ≫ (T ↘ Spec (CommRingCat.of K))) :=
      inferInstance
    simpa only [Nat.zero_add] using h
  have : IsDominant (σ ∣_ V) := isDominant_morphismRestrict_integral σ V
  have hsq : (σ ∣_ V) ≫ V.ι = T'.ι ≫ σ := morphismRestrict_ι σ V
  have : (σ ∣_ V).IsOver (Spec (CommRingCat.of K)) := by
    constructor
    have h1 := congrArg (· ≫ (Y ↘ Spec (CommRingCat.of K))) hsq
    simp only [Category.assoc, HomIsOver.comp_over] at h1
    exact h1
  have hT'ι : Function.Bijective (dominantFunctionFieldAlgHom (K := K) T'.ι) :=
    dominantFunctionFieldMap_bijective_of_isOpenImmersion T'.ι
  have hVι : Function.Bijective (dominantFunctionFieldAlgHom (K := K) V.ι) :=
    dominantFunctionFieldMap_bijective_of_isOpenImmersion V.ι
  have hσ' : Function.Bijective (dominantFunctionFieldAlgHom (K := K) (σ ∣_ V)) := by
    have h2 := dominantFunctionFieldAlgHom_comp_bijective σ T'.ι hσ hT'ι
    rw [← dominantFunctionFieldAlgHom_congr_hom hsq, dominantFunctionFieldAlgHom_comp,
      AlgHom.coe_comp] at h2
    exact (Function.Bijective.of_comp_iff _ hVι).mp h2
  have hbij : Function.Bijective (T'.ι.stalkMap ⟨(e : T), heV⟩) :=
    ConcreteCategory.bijective_of_isIso _
  let e' : CodimensionOnePoint T'.toScheme :=
    ⟨⟨(e : T), heV⟩, (coheight_eq_of_stalkMap_bijective T'.ι ⟨(e : T), heV⟩ hbij).trans
      e.property⟩
  obtain ⟨cT'⟩ : Nonempty (EtaleChart K T'.toScheme n) := by
    obtain ⟨c, -⟩ := Opens.mem_iSup.mp
      ((etaleCharts_cover (K := K) (X := T'.toScheme) (n := n)).symm ▸
        Opens.mem_top (e' : T'.toScheme))
    exact ⟨c⟩
  -- the log discrepancy along e does not change
  have hlog : cartierCoefficient (logDiscrepancyDivisor n (σ ∣_ V) hσ' cV
      (1 : V.toScheme.functionFieldˣ) 1 (1 • (smoothCanonicalDivisor cV + principalCartierDivisor
        V.toScheme (1 : V.toScheme.functionFieldˣ))) cT' etaleCharts_cover) (e' : T'.toScheme) =
      cartierCoefficient (logDiscrepancyDivisor n σ hσ cY (1 : Y.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) cT
        etaleCharts_cover) (e : T) := by
    rw [← logDiscrepancy_coefficient_comp_openImmersion V.ι hVι cY cV (σ ∣_ V) hσ' cT'
        (e' : T'.toScheme),
      logDiscrepancyDivisor_congr_hom hsq _ (dominantFunctionFieldAlgHom_comp_bijective σ T'.ι hσ hT'ι)]
    exact logDiscrepancyDivisor_comp_coefficient_of_stalkMap_bijective σ T'.ι hσ hT'ι cY 1 1 _ cT
      cT' e' e.property hbij
  -- the orders along e do not change
  have : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have : Smooth (T'.toScheme ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have : IsDiscreteValuationRing (T.presheaf.stalk (T'.ι (e' : T'.toScheme))) :=
    smoothOverField_codimensionOne_stalk_DVR (K := K)
      (⟨T'.ι (e' : T'.toScheme), e.property⟩ : CodimensionOnePoint T)
  have : IsDiscreteValuationRing (T'.toScheme.presheaf.stalk (e' : T'.toScheme)) :=
    smoothOverField_codimensionOne_stalk_DVR (K := K) e'
  have hord : ∀ i, T'.toScheme.ord ((dominantFunctionFieldMap (σ ∣_ V)).hom (gV i))
      (e' : T'.toScheme) = T.ord ((dominantFunctionFieldMap σ).hom (gY i)) (e : T) := by
    intro i
    have h1 : (dominantFunctionFieldMap (σ ∣_ V)).hom (gV i) =
        dominantFunctionFieldAlgHom (K := K) T'.ι (dominantFunctionFieldAlgHom (K := K) σ (gY i)) := by
      rw [← hg i]
      change ((dominantFunctionFieldAlgHom (K := K) (σ ∣_ V)).comp
        (dominantFunctionFieldAlgHom (K := K) V.ι)) (gY i) = _
      rw [← dominantFunctionFieldAlgHom_comp, dominantFunctionFieldAlgHom_congr_hom hsq,
        dominantFunctionFieldAlgHom_comp, AlgHom.comp_apply]
    rw [h1]
    exact scheme_ord_pullback_of_stalkMap_bijective T'.ι e' e.property hbij _
  refine ⟨T'.toScheme, inferInstance, inferInstance, inferInstance, inferInstance, σ ∣_ V,
    inferInstance, inferInstance, hσ', cT', e', ?_, ?_, ?_⟩
  · apply (mem_closure_singleton_open_immersion_iff V.ι ((σ ∣_ V) (e' : T'.toScheme))
      ⟨y, hy⟩).mp
    have h2 : V.ι ((σ ∣_ V) (e' : T'.toScheme)) = σ (e : T) := by
      rw [← Scheme.Hom.comp_apply, hsq]
      rfl
    rw [h2]
    exact hye
  · rw [hlog]
    exact hApos
  · intro i hi
    have hi' : gY i ≠ 0 := fun h0 => hi (by rw [← hg i, h0, map_zero])
    rw [hlog, hord i]
    exact hineq i hi'

/-- Badness is local: a point of an open subscheme V of Y is bad on V if and only if it is bad
on Y. -/
theorem modelThresholdBadAt_opens_iff (cY : EtaleChart K Y n) (cV : EtaleChart K V.toScheme n)
    (y : Y) (hy : y ∈ V) {J : Type*} (gY : J → Y.functionField)
    (gV : J → V.toScheme.functionField)
    (hg : ∀ i, (dominantFunctionFieldMap V.ι).hom (gY i) = gV i) (M : ℕ) :
    ModelThresholdBadAt cV (1 : V.toScheme.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cV + principalCartierDivisor V.toScheme
        (1 : V.toScheme.functionFieldˣ))) ⟨y, hy⟩ gV M ↔
    ModelThresholdBadAt cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) y gY
      M := by
  constructor
  · intro h
    exact modelThresholdBadAt_of_openImmersion V.ι
      (dominantFunctionFieldMap_bijective_of_isOpenImmersion V.ι) cY cV ⟨y, hy⟩ gY gV hg M h
  · exact modelThresholdBadAt_restrict_opens V cY cV y hy gY gV hg M

end Opens

end MixedFujita
