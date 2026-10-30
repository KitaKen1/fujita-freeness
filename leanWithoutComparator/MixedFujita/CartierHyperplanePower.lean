/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SGAPulledHyperplaneCartier
public import MixedFujita.FiniteProjectiveCartierAmpleness
public import MixedFujita.CartierGradedPullback

/-! 元ampleからの実超平面冪表示と非優勢閉部分源への実制限。 See reports/check-226-mixed-ample-intersection-positivity.json for the verified scope. Ample-pullback dimension patterns and the original numerical-dimension dictionary remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A geometric projective power presentation records an actual positive
Cartier multiple and an isomorphism to an actual closed-embedding hyperplane
sheaf. It is auxiliary proof data, without changing numerical dimension. -/
def CartierHasHyperplanePower
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] (H : CartierDivisor X) : Prop :=
  ∃ (m : ℕ), 0 < m ∧ ∃ (r : ℕ) (e : X ⟶ polynomialProjectiveScheme (r + 1) K)
    (_ : IsClosedImmersion e)
    (_ : e ≫ polynomialProjectiveToBase (r + 1) K = X ↘ Spec (CommRingCat.of K))
    (g : MvPolynomial (Fin (r + 1)) K) (hg : g.IsHomogeneous 1)
    (hgen : g ∉ (e (genericPoint X)).asHomogeneousIdeal),
    Nonempty ((m • H).sheaf ≅ (projectiveHyperplaneCartier e g hg hgen).sheaf)


/-- The ORIGINAL projective Cartier ample predicate internally supplies
the actual hyperplane power presentation used for restriction and induction. -/
theorem cartierHasHyperplanePower_of_isAmpleProj
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] (H : CartierDivisor X) (hH : CartierIsAmpleProj K H) :
    CartierHasHyperplanePower K H := by
  obtain ⟨m, hm, r, e, he, hover, g, hg, hgen, f, hrel⟩ := hH
  cases r with
  | zero =>
    obtain ⟨k, hk⟩ := polynomialProjective_exists_coordinate_chart 0 K (e (genericPoint X))
    exact k.elim0
  | succ r =>
    exact ⟨m, hm, r, e, he, hover, g, hg, hgen,
      ⟨eqToIso (congrArg CartierDivisor.sheaf hrel) ≪≫
        cartierSheafPrincipalShiftIso _ f⟩⟩


/-- An actual projective power presentation restricts along any integral
closed source, using actual line-bundle pullback and Cartier representatives.
No dominance or pullback of rational functions is required. -/
theorem cartierHasHyperplanePower_of_closed_representative
    (K : Type u) [Field K] {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
    [X.Over (Spec (CommRingCat.of K))] [Z.Over (Spec (CommRingCat.of K))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of K))]
    (H : CartierDivisor X) (F : CartierDivisor Z)
    (a : (Scheme.Modules.pullback i).obj H.sheaf ≅ F.sheaf)
    (hH : CartierHasHyperplanePower K H) : CartierHasHyperplanePower K F := by
  obtain ⟨m, hm, r, e, he, hover, g, hg, hgen, ⟨b⟩⟩ := hH
  let := he
  let j : Z ⟶ polynomialProjectiveScheme (r + 1) K := i ≫ e
  let : IsClosedImmersion j := inferInstance
  have hjover : j ≫ polynomialProjectiveToBase (r + 1) K = Z ↘ Spec (CommRingCat.of K) := by
    change (i ≫ e) ≫ _ = _
    rw [Category.assoc, hover, HomIsOver.comp_over]
  obtain ⟨k, hk⟩ := polynomialProjective_exists_coordinate_chart (r + 1) K (j (genericPoint Z))
  have hkgen : MvPolynomial.X k ∉ (j (genericPoint Z)).asHomogeneousIdeal := hk
  let L := projectiveSpace.twistingBundle (Fin (r + 1)) K
  let c : (m • F).sheaf ≅ (projectiveHyperplaneCartier j (MvPolynomial.X k)
      (MvPolynomial.isHomogeneous_X K k) hkgen).sheaf :=
    (cartierPullbackGradedIso H i F a m).symm ≪≫
      (Scheme.Modules.pullback i).mapIso b ≪≫
      (Scheme.Modules.pullback i).mapIso
        ((sgaPulledHyperplaneCartierIso e g hg hgen).symm ≪≫
          (sgaLineBundlePullbackPowerIso L e 1).symm) ≪≫
      (Scheme.Modules.pullbackCompIso' i e j rfl (L.toModules 1)).symm ≪≫
      sgaLineBundlePullbackPowerIso L j 1 ≪≫
      sgaPulledHyperplaneCartierIso j (MvPolynomial.X k) (MvPolynomial.isHomogeneous_X K k) hkgen
  exact ⟨m, hm, r, j, inferInstance, hjover, MvPolynomial.X k,
    MvPolynomial.isHomogeneous_X K k, hkgen, ⟨c⟩⟩

end MixedFujita
