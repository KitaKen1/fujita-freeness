/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SGATwistPullbackIso
public import MixedFujita.PolynomialHyperplaneSerreVanishing

/-! 引き戻したSGA超平面と指定した実Cartier超平面の同型。 See reports/check-217-semiample-fixed-twist-integration.json for the verified scope. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual pulled SGA hyperplane power is the specified homogeneous Cartier
hyperplane sheaf, rather than merely a freely chosen Cartier representative. -/
noncomputable def sgaPulledHyperplaneCartierIso
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] {r : ℕ}
    {X : Scheme.{u}} [IsIntegral X]
    (e : X ⟶ polynomialProjectiveScheme (r + 1) R) [IsClosedImmersion e]
    (g : MvPolynomial (Fin (r + 1)) R) (hg : g.IsHomogeneous 1)
    (hgX : g ∉ (e (genericPoint X)).asHomogeneousIdeal) :
    ((projectiveSpace.twistingBundle (Fin (r + 1)) R).pullback e).toModules 1 ≅
      (projectiveHyperplaneCartier e g hg hgX).sheaf := by
  let P := polynomialProjectiveScheme (r + 1) R
  let : IsIntegral P := polynomialProjectiveScheme_isIntegral R (0 : Fin (r + 1))
  have hg0 : g ≠ 0 := by
    intro h
    apply hgX
    rw [h]
    exact (e (genericPoint X)).asHomogeneousIdeal.zero_mem
  have hgP := polynomialProjective_nonzero_avoids_genericPoint (0 : Fin (r + 1)) g hg0
  let J := projectiveHyperplaneCartier (𝟙 P) g hg hgP
  let b : (Scheme.Modules.pullback e).obj J.sheaf ≅
      (projectiveHyperplaneCartier e g hg hgX).sheaf := by
    simpa only [Category.comp_id] using
      projectiveHomogeneousCartierPullbackIso (𝟙 P) e 1 g hg one_pos hgP hgX
  exact (sgaLineBundlePullbackPowerIso
    (projectiveSpace.twistingBundle (Fin (r + 1)) R) e 1).symm ≪≫
    (Scheme.Modules.pullback e).mapIso (polynomialHyperplaneSGAModuleIso g hg hgP).symm ≪≫ b

end MixedFujita
