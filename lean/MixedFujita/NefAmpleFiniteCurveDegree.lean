/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.AmpleCartierPullbackRepresentatives
public import MixedFujita.AmpleCartierEulerDegree
public import MixedFujita.CurveMixedEulerDegree
public import MixedFujita.CartierNefDefinition

/-! 一般nef＋ampleの任意有限smooth曲線上の元の次数厳密正値性。 See reports/check-236-semiample-positive-curve-ampleness.json for the verified scope. Actual finite smooth-curve degree positivity makes the actual section morphism finite; original semiampleness then implies original Cartier ampleness over an algebraically closed characteristic-zero field. No source normality or smoothness, reduced fibers, supplied fiber curves or finiteness witnesses are required. Universal nef-plus-ample semiampleness, general KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra


/-- On every actual finite smooth curve over an infinite field, an
original nef plus an original ample Cartier class has strictly positive degree. -/
theorem nef_add_ample_finite_curve_pullback_degree_pos
    (K : Type u) [Field K] [Infinite K] {X C : Scheme.{u}} [IsIntegral X] [IsIntegral C]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    [C.Over (Spec (CommRingCat.of K))] [IsProper (C ↘ Spec (CommRingCat.of K))]
    [Smooth (C ↘ Spec (CommRingCat.of K))] (hC : topologicalKrullDim C = 1)
    (N A : CartierDivisor X) (hN : CartierIsNef K N) (hA : CartierIsAmpleProj K A)
    (φ : C ⟶ X) [IsFinite φ] [φ.IsOver (Spec (CommRingCat.of K))] :
    0 < cartierCurvePullbackDegree (K := K) (N + A) φ := by
  obtain ⟨B, ⟨b⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor A φ
  have hB : CartierIsAmpleProj K B := cartierIsAmpleProj_of_finite_pullback_over K φ A B hA b
  have hpos := proper_ample_cartierMixedEuler_diagonal_positive K 1 hC (by decide) B hB 0
  rw [List.replicate_one, properSmoothCurve_cartierMixedEulerDifference_singleton_eq_degree K hC B 0] at hpos
  rw [cartierCurvePullbackDegree_add (K := K) hC,
    cartierCurvePullbackDegree_eq_representation_degree (K := K) hC A φ B b]
  have hnonneg := hN C hC φ (HomIsOver.comp_over (f := φ) (S := Spec (CommRingCat.of K)))
  linarith

end MixedFujita
