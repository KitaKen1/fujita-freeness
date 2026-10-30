/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CoherentMixedEulerPositivityReduction

/-! 非零実最高次係数から整閉部分源の非零構造係数を内部抽出。 See reports/check-226-mixed-ample-intersection-positivity.json for the verified scope. Ample-pullback dimension patterns and the original numerical-dimension dictionary remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A nonzero top coherent coefficient on an arbitrary proper source has
an ACTUAL integral closed source with a nonzero structure coefficient.
Contrapositive coherent devissage avoids constructing maximal components. -/
theorem proper_mixedEuler_nonzero_exists_integral_closed_unit
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim Y ≤ (n + 1 : ℕ)) (p : Y ⟶ X)
    (M : Y.Modules) [M.IsCoherent] (D : List (CartierDivisor X))
    (hlen : n < D.length) (E : CartierDivisor X)
    (hM : cartierPulledModuleMixedEulerDifference K p M D E ≠ 0) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ Y), IsIntegral Z ∧ IsClosedImmersion i ∧
      letI : Z.Over (Spec (CommRingCat.of K)) := ⟨i ≫ (Y ↘ Spec (CommRingCat.of K))⟩
      cartierPulledModuleMixedEulerDifference K (i ≫ p) (CohomologyAux.unitModule Z) D E ≠ 0 := by
  by_contra hno
  apply hM
  apply cartierPulledModuleMixedEulerDifference_vanish_of_integral_step K p D E ?_ M
  intro Z i _ _ hsmall G hG
  let : Z.Over (Spec (CommRingCat.of K)) := ⟨i ≫ (Y ↘ Spec (CommRingCat.of K))⟩
  let : i.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  let : IsProper (Z ↘ Spec (CommRingCat.of K)) := by
    change IsProper (i ≫ (Y ↘ Spec (CommRingCat.of K)))
    infer_instance
  let := hG
  have hz : cartierPulledModuleMixedEulerDifference K (i ≫ p) (CohomologyAux.unitModule Z) D E = 0 := by
    by_contra hn
    exact hno ⟨Z, i, inferInstance, inferInstance, hn⟩
  rw [cartierPulledModuleMixedEulerDifference_closed_pushforward K p i G D E]
  exact proper_cartierPulledModuleMixedEulerDifference_top_vanish_of_unit_vanish K n
    (i.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans hdim) (i ≫ p) G D hlen E hz

end MixedFujita
