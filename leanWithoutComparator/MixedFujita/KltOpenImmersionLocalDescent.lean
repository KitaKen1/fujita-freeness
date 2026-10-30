/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.BirationalTestOpenLift
public import MixedFujita.HironakaSNCModelExistence

/-!
The base-point all-model klt predicate is unchanged by an actual open immersion
covering a neighbourhood of the chosen base point. Global test primes in that
neighbourhood are lifted on actual open test schemes, then discrepancies are
compared through their actual stalk isomorphisms and pulled rational top forms.
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

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {X Y : Scheme.{u}}
  [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [IsSeparated (X ↘ Spec (CommRingCat.of K))]

variable {Z : Scheme.{u}} [IsIntegral Z] [IsLocallyNoetherian Z]
  [Z.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of K))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of K))]
  (j : Z ⟶ X) [IsOpenImmersion j] [IsDominant j] [j.IsOver (Spec (CommRingCat.of K))]
  (hj : Function.Bijective (dominantFunctionFieldAlgHom (K := K) j))

/-- Local comparison descends the actual crepant pair on a base neighbourhood. -/
theorem logPairIsKltOverBasePoint_of_open_crepant_pullback
    (g : X ⟶ Y) (η : Y) (V : Y.Opens) (hηV : η ∈ V)
    (hV : g ⁻¹ᵁ V ≤ j.opensRange)
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (cZ : EtaleChart K Z n)
    (hklt : LogPairIsKltOverBasePoint (j ≫ g) η cZ
      (crepantPullbackFormUnit j hj c f cZ) d (cartierPullback j D)) :
    LogPairIsKltOverBasePoint g η c f d D := by
  intro U _ _ _ _ σ _ _ _ hσ cU u hu hη
  have huV : (σ ≫ g) u ∈ V :=
    (specializes_iff_mem_closure.mpr hη).mem_open V.isOpen hηV
  have huj : σ u ∈ j.opensRange := hV huV
  obtain ⟨W, huW, α, hdom, hover, hcomm, hα⟩ :=
    birational_test_exists_open_immersion_lift j σ hσ u huj
  letI : Nonempty W := ⟨⟨u, huW⟩⟩
  letI : W.toScheme.Over (Spec (CommRingCat.of K)) :=
    ⟨W.ι ≫ (U ↘ Spec (CommRingCat.of K))⟩
  haveI : W.ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  letI : IsDominant α := hdom
  letI : α.IsOver (Spec (CommRingCat.of K)) := hover
  letI : IsDominant W.ι := ⟨W.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  haveI : SmoothOfRelativeDimension n (W.toScheme ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := W.ι) (S := Spec (CommRingCat.of K))]
    have h : SmoothOfRelativeDimension (0 + n) (W.ι ≫ (U ↘ Spec (CommRingCat.of K))) :=
      inferInstance
    simpa only [Nat.zero_add] using h
  have hι : Function.Bijective (dominantFunctionFieldAlgHom (K := K) W.ι) :=
    dominantFunctionFieldMap_bijective_of_isOpenImmersion W.ι
  let w : W.toScheme := ⟨u, huW⟩
  have hw : Order.coheight w = 1 :=
    (coheight_eq_of_stalkMap_bijective W.ι w
      (ConcreteCategory.bijective_of_isIso (W.ι.stalkMap w))).trans hu
  let p : CodimensionOnePoint W.toScheme := ⟨w, hw⟩
  obtain ⟨cW, hcW⟩ : ∃ cW : EtaleChart K W.toScheme n, w ∈ cW.U :=
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := W.toScheme) (n := n)).symm ▸
      Opens.mem_top w)
  have hηW : η ∈ closure ({(α ≫ (j ≫ g)) (p : W.toScheme)} : Set Y) := by
    have heq : (α ≫ (j ≫ g)) (p : W.toScheme) = (σ ≫ g) u := by
      rw [← Category.assoc, hcomm, Category.assoc]
      rfl
    simpa only [heq] using hη
  have hbound := logPairIsKltOverBasePoint_discrepancy_bound_on_birational_test
    (j ≫ g) η cZ (crepantPullbackFormUnit j hj c f cZ) d hd (cartierPullback j D)
    hklt α hα cW p hηW
  rw [← logDiscrepancyDivisor_comp j α hj hα c f d D cZ cW etaleCharts_cover] at hbound
  have hbound' : -(d : ℤ) < cartierCoefficient
      (logDiscrepancyDivisor n (W.ι ≫ σ)
        (dominantFunctionFieldAlgHom_comp_bijective σ W.ι hσ hι)
        c f d D cW etaleCharts_cover) (p : W.toScheme) := by
    simpa only [hcomm] using hbound
  have heq := logDiscrepancyDivisor_comp_coefficient_of_stalkMap_bijective
    σ W.ι hσ hι c f d D cU cW p hu
      (ConcreteCategory.bijective_of_isIso (W.ι.stalkMap w))
  simpa [heq, p, w] using hbound'

/-- The original base-point condition agrees with the actual restricted crepant pair. -/
theorem logPairIsKltOverBasePoint_iff_open_crepant_pullback
    (g : X ⟶ Y) (η : Y) (V : Y.Opens) (hηV : η ∈ V)
    (hV : g ⁻¹ᵁ V ≤ j.opensRange)
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (cZ : EtaleChart K Z n) :
    LogPairIsKltOverBasePoint g η c f d D ↔
    LogPairIsKltOverBasePoint (j ≫ g) η cZ
      (crepantPullbackFormUnit j hj c f cZ) d (cartierPullback j D) := by
  constructor
  · exact fun h => logPairIsKltOverBasePoint_crepant_pullback_without_properness
      j hj g η c f d hd D h cZ
  · exact logPairIsKltOverBasePoint_of_open_crepant_pullback j hj g η V hηV hV c f d hd D cZ

/-- Global klt on an actual restricted pair implies klt over every base point it covers. -/
theorem logPairIsKltOverBasePoint_of_open_crepant_klt
    (g : X ⟶ Y) (η : Y) (V : Y.Opens) (hηV : η ∈ V)
    (hV : g ⁻¹ᵁ V ≤ j.opensRange)
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (cZ : EtaleChart K Z n)
    (hklt : LogPairIsKlt cZ (crepantPullbackFormUnit j hj c f cZ) d (cartierPullback j D)) :
    LogPairIsKltOverBasePoint g η c f d D := by
  exact logPairIsKltOverBasePoint_of_open_crepant_pullback j hj g η V hηV hV c f d hd D cZ
    (logPairIsKlt_overBasePoint (j ≫ g) η cZ (crepantPullbackFormUnit j hj c f cZ)
      d (cartierPullback j D) hklt)

end MixedFujita
