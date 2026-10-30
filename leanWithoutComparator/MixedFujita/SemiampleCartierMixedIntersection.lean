/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SemiampleCoherentMixedEulerNonnegative
public import MixedFujita.AmpleDivisibleGlobalGeneration

/-! 元semiample通常混合交点数と任意源への元ample引き戻しの非負性。 See reports/check-228-semiample-mixed-intersection-nonnegative.json for the verified scope. Strict ample-pullback positivity and the original numerical-dimension dictionary remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- The ORIGINAL ordinary INTEGER mixed intersection is nonnegative for
any family of original semiample factors, over every field and in every dimension. -/
theorem proper_semiample_cartierMixedIntersection_nonneg
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (D : List (CartierDivisor X)) (hdim : topologicalKrullDim X = D.length)
    (hD : ∀ H ∈ D, ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • H)) :
    0 ≤ cartierMixedIntersection K D hdim := by
  let O : X.Modules := CohomologyAux.unitModule X
  let : O.IsCoherent := invertible_module_isCoherent O
  have h := proper_semiample_coherentMixedEuler_nonneg K D.length hdim.le (𝟙 X) D rfl hD O 0
  rw [cartierPulledModuleMixedEulerDifference_id_unit] at h
  exact h


/-- ORIGINAL ample factors pull back to nonnegative coherent top mixed
coefficients on EVERY proper source; no closed immersion or infinite field is needed. -/
theorem proper_pulled_ample_coherentMixedEuler_nonneg
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
    [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim Y ≤ n) (p : Y ⟶ X)
    (D : List (CartierDivisor X)) (hlen : D.length = n)
    (hD : ∀ H ∈ D, CartierIsAmpleProj K H) (M : Y.Modules) [M.IsCoherent]
    (E : CartierDivisor X) :
    0 ≤ cartierPulledModuleMixedEulerDifference K p M D E := by
  apply proper_semiample_coherentMixedEuler_nonneg K n hdim p D hlen ?_ M E
  intro H hH
  obtain ⟨q, hq, hgen⟩ := cartierIsAmpleProj_exists_globallyGenerated_multiple H (hD H hH)
  exact ⟨q, hq, hgen⟩

end MixedFujita
