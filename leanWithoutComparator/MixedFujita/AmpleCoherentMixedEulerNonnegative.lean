/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.MixedAmpleCartierIntersection

/-! 実非被約閉源の任意連接係数と有効因子＋ample族の混合非負性。 See reports/check-226-mixed-ample-intersection-positivity.json for the verified scope. Ample-pullback dimension patterns and the original numerical-dimension dictionary remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Closed sources, including nonreduced ones and arbitrary coherent
coefficients, have nonnegative top mixed coefficients in original ample
directions. All integral-unit sign inputs are now supplied by the proved
mixed positivity theorem, not assumed. -/
theorem proper_closed_ample_coherentMixedEuler_nonneg
    (K : Type u) [Field K] [Infinite K] {X Y : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
    [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) [IsClosedImmersion p] [p.IsOver (Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim Y ≤ (n + 1 : ℕ))
    (D : List (CartierDivisor X)) (hlen : D.length = n + 1)
    (hD : ∀ H ∈ D, CartierIsAmpleProj K H) (M : Y.Modules) [M.IsCoherent]
    (E : CartierDivisor X) :
    0 ≤ cartierPulledModuleMixedEulerDifference K p M D E := by
  rw [proper_cartierPulledModuleMixedEulerDifference_top_base_independent K (n + 1)
    hdim p M D hlen E 0]
  apply proper_cartierPulledModuleMixedEulerDifference_top_nonneg_of_integral_units
    K n hdim p D (by omega) 0 ?_ M
  intro Z _ _ _ i _ _
  have hb := i.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans hdim
  rcases withBotENat_le_succ_cases (topologicalKrullDim Z) n hb with hs | heq
  · let : (CohomologyAux.unitModule Z).IsCoherent := invertible_module_isCoherent _
    rw [proper_cartierPulledModuleMixedEulerDifference_vanish_of_length K n hs (i ≫ p)
      (CohomologyAux.unitModule Z) D (by omega) 0]
  · obtain ⟨F, hFlen, hF, hval⟩ := closed_hyperplanePowers_exists_representatives K (i ≫ p) D
      (fun H hH => cartierHasHyperplanePower_of_isAmpleProj K H (hD H hH))
    rw [hval]
    exact le_of_lt (proper_hyperplanePowers_mixedEuler_positive K n Z heq F
      (hFlen.trans hlen) hF)


/-- An effective original Cartier factor and arbitrary original ample
remaining factors have nonnegative top mixed coefficient in dimension at
least two. The actual nonreduced Cartier cut supplies the coherent source. -/
theorem proper_effective_ample_cartierMixedEuler_nonneg
    (K : Type u) [Field K] [Infinite K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = (n + 1 + 1 : ℕ))
    (G : CartierDivisor X) (hG : G.IsEffective)
    (D : List (CartierDivisor X)) (hlen : D.length = n + 1)
    (hD : ∀ H ∈ D, CartierIsAmpleProj K H) (E : CartierDivisor X) :
    0 ≤ cartierMixedEulerDifference K (G :: D) E := by
  let I := effectiveCartierIdealSheaf G hG
  let p := I.subschemeι
  let : I.subscheme.Over (Spec (CommRingCat.of K)) := ⟨p ≫ (X ↘ Spec (CommRingCat.of K))⟩
  let : p.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  let : IsProper (I.subscheme ↘ Spec (CommRingCat.of K)) := by
    change IsProper (p ≫ (X ↘ Spec (CommRingCat.of K)))
    infer_instance
  let O : I.subscheme.Modules := CohomologyAux.unitModule I.subscheme
  let : O.IsCoherent := invertible_module_isCoherent O
  rw [proper_cartierMixedEulerDifference_top_eq_effective_cut K D G E hG
    (by simpa [hlen] using hdim.le)]
  exact proper_closed_ample_coherentMixedEuler_nonneg K p n
    (effectiveCartierCut_topologicalKrullDim_le G hG (n + 1) hdim.le) D hlen hD O 0


/-- Ordinary top intersection is nonnegative for one effective factor and
a nonempty family of ample factors, in its original integer normalization. -/
theorem proper_effective_ample_cartierMixedIntersection_nonneg
    (K : Type u) [Field K] [Infinite K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (G : CartierDivisor X) (hG : G.IsEffective) (D : List (CartierDivisor X))
    (hdim : topologicalKrullDim X = D.length + 1) (hne : D ≠ [])
    (hD : ∀ H ∈ D, CartierIsAmpleProj K H) :
    0 ≤ cartierMixedIntersection K (G :: D) (by simpa using hdim) := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero
    (by have := List.length_pos_iff.mpr hne; omega : D.length ≠ 0)
  exact proper_effective_ample_cartierMixedEuler_nonneg K n (by simpa [hn] using hdim)
    G hG D hn hD 0

end MixedFujita
