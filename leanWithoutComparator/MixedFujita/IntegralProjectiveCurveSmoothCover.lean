/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.NormalSteinFactorization
public import MixedFujita.NormalCurveSmoothness
public import MixedFujita.SameDimensionSteinBirational
public import MixedFujita.ProjectiveNumericallyTrivialSections

/-! 特異な整射影曲線の実有限優勢smooth proper被覆を内部構成。 See reports/check-232-nef-semiample-mixed-nonnegative.json for the verified scope. One original nef factor with a semiample tail and numerical-trivial-factor vanishing are proved in the declared scope. General nef-plus-ample ampleness, KV, BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra


/-- Every integral projective curve in characteristic zero has an actual
finite dominant smooth proper curve cover; no normalization witness is an input. -/
theorem proper_integral_curve_exists_finite_smooth_cover
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {Y : Scheme.{u}} [IsIntegral Y]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (hdim : topologicalKrullDim Y = 1)
    (hProj : ∃ A : CartierDivisor Y, CartierIsAmpleProj K A) :
    ∃ (C : Scheme.{u}) (_ : IsIntegral C) (_ : C.Over (Spec (CommRingCat.of K)))
      (f : C ⟶ Y), IsFinite f ∧ IsDominant f ∧ f.IsOver (Spec (CommRingCat.of K)) ∧
      IsProper (C ↘ Spec (CommRingCat.of K)) ∧ Smooth (C ↘ Spec (CommRingCat.of K)) ∧
      topologicalKrullDim C = 1 := by
  let := properOverField_scheme_isNoetherian (K := K) (X := Y)
  obtain ⟨A, hA⟩ := hProj
  obtain ⟨cY⟩ := nonempty_etaleChart_of_charZero (K := K) hdim
  obtain ⟨T, hTi, hTo, hTN, hTs, p, hdom, hover, hprop, hp, cT, r, ξ,
    hinj, hcoh, hsnc, hsupp, hG, J, hJ⟩ :=
    exists_projective_snc_model_with_ample cY 1 1 0 (fun _ : Fin 0 => 0) hA
  let := hTi
  let := hTo
  let := hTN
  let := hTs
  let := hdom
  let := hover
  let := hprop
  let : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth 1 _
  have hdimT : topologicalKrullDim T = 1 := etaleChart_topologicalKrullDim cT
  obtain ⟨C, hC, hCN, g, hgd, f, hg, hf, hfac, happ, hconn, hnorm⟩ :=
    properMap_exists_normal_stein_factorization p (fun t => smooth_stalk_isIntegrallyClosed (K := K) t)
  let := hC
  let := hCN
  let := hgd
  let := hg
  let := hf
  let : C.Over (Spec (CommRingCat.of K)) := ⟨f ≫ (Y ↘ Spec (CommRingCat.of K))⟩
  let : f.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  let : g.IsOver (Spec (CommRingCat.of K)) := ⟨by
    change g ≫ (f ≫ (Y ↘ Spec (CommRingCat.of K))) = T ↘ Spec (CommRingCat.of K)
    rw [← Category.assoc, hfac, HomIsOver.comp_over]⟩
  let : IsProper (C ↘ Spec (CommRingCat.of K)) := by
    change IsProper (f ≫ (Y ↘ Spec (CommRingCat.of K)))
    infer_instance
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨t, ht⟩ := surjective_of_isProper_of_isDominant p y
    exact ⟨g t, (congrArg (fun q : T ⟶ Y => q t) hfac).trans ht⟩
  let : IsDominant f := ⟨hsurj.denseRange⟩
  have hdimC : topologicalKrullDim C = 1 := le_antisymm
    ((dominant_topologicalKrullDim_le (K := K) g).trans hdimT.le)
    (hdim.symm.le.trans (dominant_topologicalKrullDim_le (K := K) f))
  have hsm : Smooth (C ↘ Spec (CommRingCat.of K)) := normalCurve_smooth hdimC hnorm
  exact ⟨C, hC, inferInstance, f, hf, inferInstance, inferInstance, inferInstance, hsm, hdimC⟩

end MixedFujita
