/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CrepantSNCLocalDescent
public import MixedFujita.LogPairOverBasePoint
public import MixedFujita.SNCCenteredDiscrepancyBound

/-!
Finite SNC coefficient tests over a specified base point. The comparison uses
actual local birational extensions and the centre-sensitive discrepancy bound.
The resulting all-model klt locus is open on the base, without presuming a
restriction-of-pairs dictionary or a supplied common model.
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

variable {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [IsLocallyNoetherian T]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))


variable {Y : Scheme.{u}} (g : X ⟶ Y) (η : Y)

/-- Actual test discrepancies from the SNC coefficients relevant to a base point. -/
theorem crepant_snc_actual_test_discrepancy_bound_overBasePoint
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (cT : EtaleChart K T n)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) = 0)
    (hb : ∀ i, η ∈ closure ({(ρ ≫ g) (ξ i)} : Set Y) → cartierCoefficient
      (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ i) < (d : ℤ))
    {U : Scheme.{u}} [IsIntegral U] [IsLocallyNoetherian U]
    [U.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K))]
    (σ : U ⟶ X) [IsDominant σ] [σ.IsOver (Spec (CommRingCat.of K))]
    (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
    (cU : EtaleChart K U n) (x : CodimensionOnePoint U)
    (hxη : η ∈ closure ({(σ ≫ g) (x : U)} : Set Y)) :
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
  have hb' : ∀ i, α (p : W.toScheme) ∈ closure ({ξ i} : Set T) →
      cartierCoefficient
        (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ i) < (d : ℤ) := by
    intro i hi
    apply hb i
    have hs := (specializes_iff_mem_closure.mpr hi).map (ρ ≫ g).continuous
    have heq : (ρ ≫ g) (α (p : W.toScheme)) = (σ ≫ g) (x : U) := by
      change ((α ≫ ρ) ≫ g) (p : W.toScheme) = (σ ≫ g) (x : U)
      rw [hcomm]
      rfl
    rw [heq] at hs
    exact specializes_iff_mem_closure.mp
      (hs.trans (specializes_iff_mem_closure.mpr hxη))
  have h := isSNCFamily_actual_discrepancy_bound_at_center α hα cT
    (crepantPullbackFormUnit ρ hρ c f cT) d hd
    (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover)
    ξ hinj hξ hsnc hsupport cW p hb'
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


/-- Finite coefficient characterization without assuming klt away from the chosen point. -/
theorem logPairIsKltOverBasePoint_iff_crepant_snc_coefficients
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (cT : EtaleChart K T n)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) = 0) :
    LogPairIsKltOverBasePoint g η c f d D ↔
      ∀ i, η ∈ closure ({(ρ ≫ g) (ξ i)} : Set Y) → cartierCoefficient
      (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ i) < (d : ℤ) := by
  constructor
  · intro hklt i hi
    have h := hklt T ρ hρ cT (ξ i) (hξ i) hi
    rw [crepantBoundaryCartier_eq_neg_discrepancy, cartierCoefficient_neg]
    omega
  · intro hb U _ _ _ _ σ _ _ _ hσ cU x hx hxη
    exact crepant_snc_actual_test_discrepancy_bound_overBasePoint ρ hρ g η
      c f d hd D cT ξ hinj hξ hsnc hsupport hb σ hσ cU ⟨x, hx⟩ hxη

/-- The valuative klt locus on the base is open for a pair with an actual SNC model. -/
theorem isOpen_logPairIsKltOverBasePoint
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (cT : EtaleChart K T n)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) = 0) :
    IsOpen {η : Y | LogPairIsKltOverBasePoint g η c f d D} := by
  have heq : {η : Y | LogPairIsKltOverBasePoint g η c f d D} =
      ⋂ i, {η : Y | η ∈ closure ({(ρ ≫ g) (ξ i)} : Set Y) →
        cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover)
          (ξ i) < (d : ℤ)} := by
    ext η
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact logPairIsKltOverBasePoint_iff_crepant_snc_coefficients ρ hρ g η
      c f d hd D cT ξ hinj hξ hsnc hsupport
  rw [heq]
  apply isOpen_iInter_of_finite
  intro i
  by_cases hi : cartierCoefficient
      (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ i) < (d : ℤ)
  · simpa only [hi, implies_true, Set.setOf_true] using (isOpen_univ : IsOpen (Set.univ : Set Y))
  · have hset : {η : Y | η ∈ closure ({(ρ ≫ g) (ξ i)} : Set Y) →
        cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover)
          (ξ i) < (d : ℤ)} = (closure ({(ρ ≫ g) (ξ i)} : Set Y))ᶜ := by
      ext η
      simp [hi]
    rw [hset]
    exact isClosed_closure.isOpen_compl

end MixedFujita
