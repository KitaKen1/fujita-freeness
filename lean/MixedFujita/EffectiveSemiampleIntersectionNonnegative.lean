/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SemiampleCoherentMixedEulerNonnegative

/-! 一有効因子とsemiample族の非負性・有効差に関する因子単調性。 See reports/check-228-semiample-mixed-intersection-nonnegative.json for the verified scope. Strict ample-pullback positivity and the original numerical-dimension dictionary remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- One original effective factor plus arbitrary semiample factors has
nonnegative top coefficient, including curves and empty tails. -/
theorem proper_effective_semiample_cartierMixedEuler_nonneg
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (G : CartierDivisor X) (hG : G.IsEffective) (D : List (CartierDivisor X))
    (hdim : topologicalKrullDim X = D.length + 1)
    (hD : ∀ H ∈ D, ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • H))
    (E : CartierDivisor X) : 0 ≤ cartierMixedEulerDifference K (G :: D) E := by
  let I := effectiveCartierIdealSheaf G hG
  let p := I.subschemeι
  let : I.subscheme.Over (Spec (CommRingCat.of K)) := ⟨p ≫ (X ↘ Spec (CommRingCat.of K))⟩
  let : p.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  let : IsProper (I.subscheme ↘ Spec (CommRingCat.of K)) := by
    change IsProper (p ≫ (X ↘ Spec (CommRingCat.of K)))
    infer_instance
  let O : I.subscheme.Modules := CohomologyAux.unitModule I.subscheme
  let : O.IsCoherent := invertible_module_isCoherent O
  rw [proper_cartierMixedEulerDifference_top_eq_effective_cut K D G E hG hdim.le]
  exact proper_semiample_coherentMixedEuler_nonneg K D.length
    (effectiveCartierCut_topologicalKrullDim_le G hG D.length hdim.le) p D rfl hD O 0


/-- The original top mixed intersection is monotone in one effective
factor difference whenever all remaining factors are semiample. -/
theorem proper_cartierMixedEulerDifference_semiample_monotone_factor
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (H J : CartierDivisor X) (hHJ : (H - J).IsEffective)
    (D : List (CartierDivisor X)) (hdim : topologicalKrullDim X = D.length + 1)
    (hD : ∀ L ∈ D, ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • L))
    (E : CartierDivisor X) :
    cartierMixedEulerDifference K (J :: D) E ≤ cartierMixedEulerDifference K (H :: D) E := by
  have hn := proper_effective_semiample_cartierMixedEuler_nonneg K (H - J) hHJ D hdim hD E
  have ha := proper_cartierMixedEulerDifference_top_add_factor K (D.length + 1)
    hdim.le [] D (by simp) (H - J) J E
  simp only [List.nil_append, sub_add_cancel] at ha
  omega

end MixedFujita
