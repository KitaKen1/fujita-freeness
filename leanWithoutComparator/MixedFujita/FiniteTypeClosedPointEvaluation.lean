/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ClosedRationalPoints
public import MixedFujita.HironakaSNCDictionary

/-! smooth性を仮定しない有限型閉点の実stalk評価。 See reports/check-215-curve-f1-f2-integration.json for the verified scope. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Order
open scoped Classical
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra


theorem finiteTypeScheme_closedPoint_has_localEvaluation
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    Nonempty (X.presheaf.stalk x →ₐ[K] K) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ (⊤ : X.Opens) from Opens.mem_top x) isOpen_univ
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxU⟩ : U)
  have := cartierBaseOpenLocalScalarTower (K := K) x hxU
  have key : ∀ P : Algebra K Γ(X, U),
      P = (X ↘ Spec (CommRingCat.of K)).sectionsAlgebra U →
        @Algebra.FiniteType K Γ(X, U) _ _ P := by
    rintro P rfl
    exact (X ↘ Spec (CommRingCat.of K)).finiteType_sectionsAlgebra hU
  have : Algebra.FiniteType K Γ(X, U) :=
    key _ (cartierBaseOpenAlgebra_eq_sectionsAlgebra (K := K) U)
  have : (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.IsMaximal :=
    hU.primeIdealOf_isMaximal_of_isClosed ⟨x, hxU⟩ hx
  have := hU.isLocalization_stalk (⟨x, hxU⟩ : U)
  exact ⟨closedPointLocalEvaluation (K := K) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
    (X.presheaf.stalk x)⟩

end MixedFujita
