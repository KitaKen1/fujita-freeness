/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierNefPullback
public import MixedFujita.CartierMixedIntersectionRepresentatives

/-! 元の曲線判定nef性の任意の実引き戻し代表元への保存。 See reports/check-232-nef-semiample-mixed-nonnegative.json for the verified scope. One original nef factor with a semiample tail and numerical-trivial-factor vanishing are proved in the declared scope. General nef-plus-ample ampleness, KV, BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra


/-- The ORIGINAL curve-test nef predicate is preserved by ANY actual
line-bundle representative of pullback, including nondominant closed maps. -/
theorem cartierIsNef_of_pullback_representative
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
    (p : Y ⟶ X) [p.IsOver (Spec (CommRingCat.of K))]
    (N : CartierDivisor X) (F : CartierDivisor Y)
    (a : (Scheme.Modules.pullback p).obj N.sheaf ≅ F.sheaf)
    (hN : CartierIsNef K N) : CartierIsNef K F := by
  intro C _ _ _ _ hC q hq
  obtain ⟨G, ⟨b⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor N (q ≫ p)
  rw [cartierCurvePullbackDegree_eq_representation_degree (K := K) hC F q G
    ((Scheme.Modules.pullback q).mapIso a.symm ≪≫
      (Scheme.Modules.pullbackComp q p).app N.sheaf ≪≫ b)]
  rw [← cartierCurvePullbackDegree_eq_representation_degree (K := K) hC N (q ≫ p) G b]
  exact hN C hC (q ≫ p) (by rw [Category.assoc, HomIsOver.comp_over, hq])

end MixedFujita
