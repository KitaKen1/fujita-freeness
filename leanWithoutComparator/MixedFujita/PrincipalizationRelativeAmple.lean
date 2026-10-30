/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.BlowUpRelativeAmple
public import MixedFujita.ProjectiveCartierPullbackComposition
public import MixedFujita.ProjectiveCoordinateAtlas
public import MixedFujita.ProjectiveCenterGenerators
public import MixedFujita.PrincipalizedIdealCoefficients
public import Hironaka.Scheme.BlowUpSequence.CompositeBlowUp
public import MixedFujita.KltPairs
public import MixedFujita.BirationalComposition

/-!
Relative ampleness on the last stage of a succession of blow-ups of a projective variety
(step 10, R1).

* Very ampleness pulls back along closed immersions over the base field that are dominant, by
  pulling back the hyperplane divisor (`cartierIsVeryAmpleProj_cartierPullback`); a coefficient of
  a pullback vanishes where a local equation is a unit (`cartierCoefficient_cartierPullback_eq_zero`).
* A succession `S` of blow-ups of a closed subvariety `Y` of projective space with centres over a
  closed set `Z` is one blow-up of an ideal `J` supported in `Z`, up to isomorphism (the pinned
  resolution library). With the coordinate atlas of `Y` and generators of `J`, check 472 gives
  `π*((d+1) H₀) − G` very ample with `G` effective over `J`; transporting along the isomorphism,
  the last stage carries the ample divisor `S*(c H₀) − G'` with `G'` effective and without
  coefficients at the points not over `Z` (`blowUpSequence_exists_relative_ample`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.IdealSheafData
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

section Transport

variable {K : Type u} [Field K] {T Y : Scheme.{u}} [IsIntegral T] [IsIntegral Y]
  [T.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]

/-- **Very ampleness pulls back along a dominant closed immersion over the base field.** -/
theorem cartierIsVeryAmpleProj_cartierPullback (ρ : T ⟶ Y) [IsDominant ρ] [IsClosedImmersion ρ]
    [ρ.IsOver (Spec (CommRingCat.of K))] {A : CartierDivisor Y} (hA : CartierIsVeryAmpleProj K A) :
    CartierIsVeryAmpleProj K (cartierPullback ρ A) := by
  obtain ⟨N, e, he, hbase, g, hg, hggen, f, rfl⟩ := hA
  refine ⟨N, ρ ≫ e, inferInstance, ?_, g, hg, projectiveHomogeneous_generic_comp ρ e g hggen,
    Units.map (dominantFunctionFieldMap ρ).hom.toMonoidHom f, ?_⟩
  · rw [Category.assoc, hbase, HomIsOver.comp_over]
  · rw [cartierPullback_add, cartierPullback_projectiveHyperplaneCartier, cartierPullback_principal]

omit [T.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))] in
/-- The pullback only depends on the morphism. -/
theorem cartierPullback_eq_of_hom_eq {f f' : T ⟶ Y} [IsDominant f] [IsDominant f'] (h : f = f')
    (D : CartierDivisor Y) : cartierPullback f D = cartierPullback f' D := by
  subst h
  rfl

omit [T.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))] in
/-- **A coefficient of a pullback vanishes where a local equation downstairs is a unit.** -/
theorem cartierCoefficient_cartierPullback_eq_zero [IsLocallyNoetherian T] (ρ : T ⟶ Y)
    [IsDominant ρ] (D : CartierDivisor Y) (s : T) (V : Y.Opens) [Nonempty V] (a : Γ(Y, V))
    (ha : a ≠ 0) (hD : D.IsLocalEquationAt (ρ s) (regularEquationRationalUnit Y V a ha))
    (hs : ρ s ∈ Y.basicOpen a) : cartierCoefficient (cartierPullback ρ D) s = 0 := by
  have : Nonempty (ρ ⁻¹ᵁ V) := dominant_preimage_nonempty ρ V
  rw [cartierCoefficient_eq_ord (cartierPullback_isLocalEquationAt ρ D s hD), Units.coe_map]
  change T.ord ((dominantFunctionFieldMap ρ).hom (Y.germToFunctionField V a)) s = 0
  rw [dominantFunctionFieldMap_germ ρ V (ρ ⁻¹ᵁ V) le_rfl a, Scheme.Hom.appLE_eq_app]
  apply ord_germToFunctionField_eq_zero_of_mem_basicOpen
  rw [← Scheme.preimage_basicOpen]
  exact hs

end Transport

section Chart

variable {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) (a : I.ideal U)

/-- Off the centre, the pulled back generator of a chart is a unit at the points of the chart. -/
theorem blowUpChart_mem_basicOpen_of_notMem_support (t : blowUp I)
    (ht : t ∈ blowUpChartOpen I U a) (hns : blowUpπ I t ∉ I.support) :
    t ∈ (blowUp I).basicOpen ((blowUpπ I).appLE U.1 (blowUpChartOpen I U a)
      (blowUpChartOpen_le_preimage I U a) (a : Γ(X, U))) := by
  have hπt : blowUpπ I t ∈ U.1 := blowUpChartOpen_le_preimage I U a ht
  have hchart := (blowUp.mem_range_chart_iff I U a t hπt).mp ht
  have htop : I.exceptionalDivisor.stalkIdeal t = ⊤ := by
    rw [Scheme.IdealSheafData.exceptionalDivisor, stalkIdeal_comap,
      stalkIdeal_eq_top_of_notMem_support I hns, Ideal.map_top]
  rw [htop, eq_comm, Ideal.span_singleton_eq_top] at hchart
  apply ((blowUp I).mem_basicOpen _ t ht).mpr
  have hg : (blowUp I).presheaf.germ _ t ht ((blowUpπ I).appLE U.1 (blowUpChartOpen I U a)
      (blowUpChartOpen_le_preimage I U a) (a : Γ(X, U))) =
      (blowUpπ I).stalkMap t (X.presheaf.germ U.1 (blowUpπ I t) hπt (a : Γ(X, U))) := by
    rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE, CommRingCat.comp_apply,
      TopCat.Presheaf.germ_res_apply]
  rw [hg]
  exact hchart

end Chart

section Principalization

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y] [IsNoetherian Y]
  [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]

/-- **Relative ampleness on the last stage of a succession of blow-ups with centres over `Z`** of
a closed subvariety of projective space. -/
theorem blowUpSequence_exists_relative_ample {N : ℕ} (e : Y ⟶ polynomialProjectiveScheme N K)
    [IsClosedImmersion e] (he : e ≫ polynomialProjectiveToBase N K = Y ↘ Spec (CommRingCat.of K))
    (S : Scheme.BlowUpSequence Y) [IsIntegral S.last] [S.last.Over (Spec (CommRingCat.of K))]
    [S.composite.IsOver (Spec (CommRingCat.of K))] [IsDominant S.composite]
    [IsLocallyNoetherian S.last] (Z : TopologicalSpace.Closeds Y)
    (hZη : genericPoint Y ∉ (Z : Set Y))
    (hc : ∀ (i : Fin S.length) (z : S.stage i.castSucc), z ∈ (S.center i).support →
      S.stageMap i.castSucc z ∈ (Z : Set Y)) :
    ∃ (H₀ : CartierDivisor Y) (c : ℕ) (G : CartierDivisor S.last), CartierIsAmpleProj K H₀ ∧
      1 ≤ c ∧ G.IsEffective ∧
      (∀ t : S.last, S.composite t ∉ (Z : Set Y) → cartierCoefficient G t = 0) ∧
      CartierIsAmpleProj K (cartierPullback S.composite (c • H₀) - G) := by
  obtain ⟨J, hJsupp, φ, hφ, -⟩ := exists_blowUp_composite_iso S
  have hJZ : ∀ x : Y, x ∈ J.support → x ∈ (Z : Set Y) := by
    intro x hx
    have hx' : x ∈ (J.support : Set Y) := hx
    rw [hJsupp] at hx'
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx'
    obtain ⟨z, hz, rfl⟩ := hi
    exact hc i z hz
  have hne : Nonempty (blowUp J) := ⟨φ.hom (Classical.arbitrary S.last)⟩
  have hint : IsIntegral (blowUp J) := isIntegral_of_isOpenImmersion φ.inv
  let : (blowUp J).Over (Spec (CommRingCat.of K)) := ⟨blowUpπ J ≫ Y ↘ Spec (CommRingCat.of K)⟩
  have hπover : (blowUpπ J).IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  have hπeq : blowUpπ J = φ.inv ≫ S.composite := by
    rw [← hφ, Iso.inv_hom_id_assoc]
  have hπdom : IsDominant (blowUpπ J) := by
    rw [hπeq]
    infer_instance
  have hπprop : IsProper (blowUpπ J) := blowUp.isProper_π J
  have hBN : IsLocallyNoetherian (blowUp J) := LocallyOfFiniteType.isLocallyNoetherian (blowUpπ J)
  -- the coordinate atlas of `Y` and generators of `J`
  obtain ⟨d, m, g, hg, hgc⟩ := exists_projective_ideal_atlas_generators e J
  obtain ⟨k₀, hk₀⟩ := polynomialProjective_exists_coordinate_chart N K (e (genericPoint Y))
  have hη₀ : genericPoint Y ∈ (projectiveAtlasOpen e k₀).1 := ⟨trivial, hk₀⟩
  have : Nonempty (projectiveAtlasOpen e k₀).1 := ⟨⟨_, hη₀⟩⟩
  -- the coordinate `x_{k₀}` does not vanish at the generic point
  have hcoordY := ratioAtlasMap_coordinateOpen (K := K) (fun β : ULift.{u} (Fin N) => β.down)
    (fun β => (projectiveAtlasOpen e β.down).1)
    (baseAtlas_iSup (projectiveAtlasOpen e) (iSup_projectiveAtlasOpen e))
    (fun β => projectiveAtlasRatio e β.down) (fun β => projectiveAtlasRatio_self e β.down)
    (baseAtlas_cocycle (projectiveAtlasOpen e) (projectiveAtlasRatio e)
      (projectiveAtlasRatio_cocycle e))
    (fun β γ => basicOpen_projectiveAtlasRatio_le e γ.down β.down) ⟨k₀⟩
  have hggen : MvPolynomial.X k₀ ∉ ((baseAtlasMap K (projectiveAtlasOpen e) (projectiveAtlasRatio e)
      (iSup_projectiveAtlasOpen e) (projectiveAtlasRatio_self e) (projectiveAtlasRatio_cocycle e))
        (genericPoint Y)).asHomogeneousIdeal := by
    have h : genericPoint Y ∈ projectivePullbackCoordinateOpen (baseAtlasMap K (projectiveAtlasOpen e)
        (projectiveAtlasRatio e) (iSup_projectiveAtlasOpen e) (projectiveAtlasRatio_self e)
        (projectiveAtlasRatio_cocycle e)) k₀ := by
      change genericPoint Y ∈ projectivePullbackCoordinateOpen (ratioAtlasMap K
        (fun β : ULift.{u} (Fin N) => β.down) (fun β => (projectiveAtlasOpen e β.down).1)
        (baseAtlas_iSup (projectiveAtlasOpen e) (iSup_projectiveAtlasOpen e))
        (fun β => projectiveAtlasRatio e β.down) (fun β => projectiveAtlasRatio_self e β.down)
        (baseAtlas_cocycle (projectiveAtlasOpen e) (projectiveAtlasRatio e)
          (projectiveAtlasRatio_cocycle e))) (⟨k₀⟩ : ULift.{u} (Fin N)).down
      rw [hcoordY]
      exact hη₀
    exact h
  -- a generator of `J` not vanishing on the chart of `x_{k₀}`
  have hηJ : genericPoint Y ∉ J.support := fun h => hZη (hJZ _ h)
  have hst := stalkIdeal_eq_top_of_notMem_support J hηJ
  rw [stalkIdeal_eq_map_germ J (projectiveAtlasOpen e k₀) hη₀] at hst
  have hJne : J.ideal (projectiveAtlasOpen e k₀) ≠ ⊥ := by
    intro h
    rw [h, Ideal.map_bot] at hst
    exact bot_ne_top hst
  obtain ⟨l₀, hgl⟩ : ∃ l₀, (g k₀ l₀ : Γ(Y, projectiveAtlasOpen e k₀)) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hJne
    rw [← hg k₀, Ideal.span_eq_bot]
    rintro _ ⟨l, rfl⟩
    exact hall l
  -- the generic point of the blow-up lies on the chart of `g_{k₀,l₀}`
  have hπη : blowUpπ J (genericPoint (blowUp J)) = genericPoint Y :=
    dominant_map_genericPoint (blowUpπ J)
  have hηBU : blowUpπ J (genericPoint (blowUp J)) ∈ (projectiveAtlasOpen e k₀).1 := by
    rw [hπη]
    exact hη₀
  have hηBchart : genericPoint (blowUp J) ∈
      blowUpChartOpen J (projectiveAtlasOpen e k₀) (g k₀ l₀) := by
    apply (blowUp.mem_range_chart_iff J _ (g k₀ l₀) _ hηBU).mpr
    rw [Scheme.IdealSheafData.exceptionalDivisor, stalkIdeal_comap,
      stalkIdeal_eq_top_of_notMem_support J (by rw [hπη]; exact hηJ), Ideal.map_top, eq_comm,
      Ideal.span_singleton_eq_top]
    have hx : (blowUpπ J).stalkMap (genericPoint (blowUp J))
        (Y.presheaf.germ (projectiveAtlasOpen e k₀).1 _ hηBU
          (g k₀ l₀ : Γ(Y, projectiveAtlasOpen e k₀))) =
        (dominantFunctionFieldMap (blowUpπ J)).hom
          (Y.germToFunctionField (projectiveAtlasOpen e k₀).1
            (g k₀ l₀ : Γ(Y, projectiveAtlasOpen e k₀))) := by
      change _ = (blowUpπ J).stalkMap (genericPoint (blowUp J))
        (Y.presheaf.stalkSpecializes _ (Y.presheaf.germ (projectiveAtlasOpen e k₀).1
          (genericPoint Y) _ (g k₀ l₀ : Γ(Y, projectiveAtlasOpen e k₀))))
      rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
    rw [hx]
    apply Ne.isUnit
    exact (map_ne_zero _).mpr fun h =>
      hgl (Y.germToFunctionField_injective _ (h.trans (map_zero _).symm))
  have hcoordB := ratioAtlasMap_coordinateOpen (K := K)
    (fun β : ULift.{u} (Fin N × Fin m) => finProdFinEquiv β.down)
    (fun β => blowUpChartOpen J (projectiveAtlasOpen e β.down.1) (g β.down.1 β.down.2))
    (iSup_blowUpChartOpen_eq_top J (projectiveAtlasOpen e) g (iSup_projectiveAtlasOpen e) hg)
    (fun β q => blowUpAtlasCoordinate J (projectiveAtlasOpen e) (projectiveAtlasRatio e) g
      β.down.1 β.down.2 (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2)
    (fun β => by
      simp only [Equiv.symm_apply_apply]
      exact blowUpAtlasCoordinate_self J _ _ g (projectiveAtlasRatio_self e) β.down.1 β.down.2)
    (fun β γ q => by
      simp only [Equiv.symm_apply_apply]
      exact blowUpAtlasCoordinate_cocycle J _ _ g d (projectiveAtlasRatio_cocycle e) hgc
        β.down.1 β.down.2 γ.down.1 γ.down.2 _ _)
    (fun β γ => by
      simp only [Equiv.symm_apply_apply]
      exact blowUpAtlasCoordinate_basicOpen_le J _ _ g d (basicOpen_projectiveAtlasRatio_le e) hgc
        β.down.1 β.down.2 γ.down.1 γ.down.2) ⟨(k₀, l₀)⟩
  have hggenB : MvPolynomial.X (finProdFinEquiv (k₀, l₀)) ∉
      ((blowUpAtlasMap K J (projectiveAtlasOpen e) (projectiveAtlasRatio e) g
        (iSup_projectiveAtlasOpen e) (projectiveAtlasRatio_self e) (projectiveAtlasRatio_cocycle e)
          d hg hgc) (genericPoint (blowUp J))).asHomogeneousIdeal := by
    have h : genericPoint (blowUp J) ∈ projectivePullbackCoordinateOpen (blowUpAtlasMap K J
        (projectiveAtlasOpen e) (projectiveAtlasRatio e) g (iSup_projectiveAtlasOpen e)
        (projectiveAtlasRatio_self e) (projectiveAtlasRatio_cocycle e) d hg hgc)
        (finProdFinEquiv (k₀, l₀)) := by
      change genericPoint (blowUp J) ∈ projectivePullbackCoordinateOpen (ratioAtlasMap K
        (fun β : ULift.{u} (Fin N × Fin m) => finProdFinEquiv β.down)
        (fun β => blowUpChartOpen J (projectiveAtlasOpen e β.down.1) (g β.down.1 β.down.2))
        (iSup_blowUpChartOpen_eq_top J (projectiveAtlasOpen e) g (iSup_projectiveAtlasOpen e) hg)
        (fun β q => blowUpAtlasCoordinate J (projectiveAtlasOpen e) (projectiveAtlasRatio e) g
          β.down.1 β.down.2 (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2) _ _)
        ((fun β : ULift.{u} (Fin N × Fin m) => finProdFinEquiv β.down) ⟨(k₀, l₀)⟩)
      rw [hcoordB]
      exact hηBchart
    exact h
  -- the relative ampleness of check 472 on the blow-up of `J`
  have hvery := blowUp_pullback_sub_exceptional_isVeryAmpleProj J (projectiveAtlasOpen e)
    (projectiveAtlasRatio e) g (iSup_projectiveAtlasOpen e) (projectiveAtlasRatio_self e)
    (projectiveAtlasRatio_cocycle e) d hg hgc (basicOpen_projectiveAtlasRatio_le e) k₀ l₀ hgl hggen
    hggenB (projectiveAtlasRatio_generate e he)
  have heff₀ := blowUpAtlasExceptional_isEffective J (projectiveAtlasOpen e)
    (projectiveAtlasRatio e) g (iSup_projectiveAtlasOpen e) (projectiveAtlasRatio_self e)
    (projectiveAtlasRatio_cocycle e) d hg hgc (basicOpen_projectiveAtlasRatio_le e) k₀ l₀ hgl hggen
    hggenB
  have hH₀ : CartierIsAmpleProj K (projectiveHyperplaneCartier (baseAtlasMap K
      (projectiveAtlasOpen e) (projectiveAtlasRatio e) (iSup_projectiveAtlasOpen e)
      (projectiveAtlasRatio_self e) (projectiveAtlasRatio_cocycle e)) (MvPolynomial.X k₀)
      (MvPolynomial.isHomogeneous_X K k₀) hggen) := by
    apply cartierIsAmpleProj_of_veryAmple
    have hci : IsClosedImmersion (baseAtlasMap K (projectiveAtlasOpen e) (projectiveAtlasRatio e)
        (iSup_projectiveAtlasOpen e) (projectiveAtlasRatio_self e)
        (projectiveAtlasRatio_cocycle e)) :=
      ratioAtlasMap_isClosedImmersion (K := K) (fun β : ULift.{u} (Fin N) => β.down)
        (fun β => (projectiveAtlasOpen e β.down).1)
        (baseAtlas_iSup (projectiveAtlasOpen e) (iSup_projectiveAtlasOpen e))
        (fun β => projectiveAtlasRatio e β.down) (fun β => projectiveAtlasRatio_self e β.down)
        (baseAtlas_cocycle (projectiveAtlasOpen e) (projectiveAtlasRatio e)
          (projectiveAtlasRatio_cocycle e))
        (fun β γ => basicOpen_projectiveAtlasRatio_le e γ.down β.down)
        (fun β => (projectiveAtlasOpen e β.down).2)
        (fun β => projectiveAtlasRatio_generate e he β.down)
    exact ⟨N, _, hci, ratioAtlasMap_over _ _ _ _ _ _, MvPolynomial.X k₀,
      MvPolynomial.isHomogeneous_X K k₀, hggen, 1, by rw [principalCartierDivisor_one, add_zero]⟩
  -- transport along the isomorphism
  have hφover : φ.hom.IsOver (Spec (CommRingCat.of K)) := ⟨by
    change φ.hom ≫ (blowUpπ J ≫ Y ↘ Spec (CommRingCat.of K)) = _
    rw [← Category.assoc, hφ, HomIsOver.comp_over]⟩
  refine ⟨_, d + 1, cartierPullback φ.hom (blowUpAtlasExceptional K J (projectiveAtlasOpen e)
    (projectiveAtlasRatio e) g (iSup_projectiveAtlasOpen e) (projectiveAtlasRatio_self e)
    (projectiveAtlasRatio_cocycle e) d hg hgc k₀ l₀ hgl hggen hggenB), hH₀, by omega,
    cartierPullback_isEffective φ.hom _ heff₀, ?_, ?_⟩
  · intro t ht
    have hπt : blowUpπ J (φ.hom t) = S.composite t := by
      rw [← Scheme.Hom.comp_apply, hφ]
    have hns : blowUpπ J (φ.hom t) ∉ J.support := fun h => ht (hπt ▸ hJZ _ h)
    have hy : φ.hom t ∈ ⨆ β : ULift.{u} (Fin N × Fin m),
        blowUpChartOpen J (projectiveAtlasOpen e β.down.1) (g β.down.1 β.down.2) := by
      rw [iSup_blowUpChartOpen_eq_top J (projectiveAtlasOpen e) g (iSup_projectiveAtlasOpen e) hg]
      trivial
    obtain ⟨β, hβ⟩ := Opens.mem_iSup.mp hy
    have : Nonempty (blowUpChartOpen J (projectiveAtlasOpen e β.down.1) (g β.down.1 β.down.2)) :=
      ⟨⟨_, hβ⟩⟩
    exact cartierCoefficient_cartierPullback_eq_zero φ.hom _ t _ _
      (blowUpChartGenerator_ne_zero J _ g β.down.1 β.down.2)
      (blowUpAtlasExceptional_isLocalEquationAt J (projectiveAtlasOpen e) (projectiveAtlasRatio e) g
        (iSup_projectiveAtlasOpen e) (projectiveAtlasRatio_self e) (projectiveAtlasRatio_cocycle e) d
        hg hgc (basicOpen_projectiveAtlasRatio_le e) k₀ l₀ hgl hggen hggenB β.down.1 β.down.2
        (φ.hom t) hβ)
      (blowUpChart_mem_basicOpen_of_notMem_support J _ _ (φ.hom t) hβ hns)
  · apply cartierIsAmpleProj_of_veryAmple
    have h := cartierIsVeryAmpleProj_cartierPullback (K := K) φ.hom hvery
    rw [cartierPullback_sub, ← cartierPullback_comp, cartierPullback_eq_of_hom_eq hφ] at h
    exact h

end Principalization


end MixedFujita
