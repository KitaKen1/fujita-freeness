/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SmoothSchemeCoordinates

/-!
The actual structure morphism being smooth of relative dimension n supplies
standard smooth affine neighbourhoods over K of that same relative dimension.
At a K-valued stalk point, completed coordinates have exactly Fin n variables.
Identifying this relative dimension with the manuscript's geometric dimension
is a separate statement, not an input disguised as a coordinate isomorphism.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace MixedFujita

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra

theorem smoothRelativeScheme_exists_affineStandardSmooth (n : ℕ)
    [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))] (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      Algebra.IsStandardSmoothOfRelativeDimension n K Γ(X, U) := by
  obtain ⟨V, hV, U, hU, hx, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := n) (f := X ↘ Spec (CommRingCat.of K)) x
  have hVtop : V = ⊤ := by
    apply top_unique
    intro z _
    have hz : z = (X ↘ Spec (CommRingCat.of K)) x := Subsingleton.elim _ _
    rw [hz]
    exact e hx
  subst V
  refine ⟨U, hU, hx, ?_⟩
  apply (RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).mp
  change RingHom.IsStandardSmoothOfRelativeDimension n
    (((X.baseRingToStructurePresheaf K).app (op U)).hom)
  rw [Scheme.baseRingToStructurePresheaf_app_eq_appLE]
  change RingHom.IsStandardSmoothOfRelativeDimension n
    (((X ↘ Spec (CommRingCat.of K)).appLE ⊤ U le_top).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
  have hb : RingHom.IsStandardSmoothOfRelativeDimension 0
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom := by
    let := (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.toAlgebra
    exact Algebra.IsStandardSmoothOfRelativeDimension.of_algebraMap_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv)
  simpa only [Nat.add_zero] using hf.comp hb

theorem smoothRelativeScheme_rationalPoint_exists_stalkCoordinates (n : ℕ)
    [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))] (x : X)
    (β : X.presheaf.stalk x →ₐ[K] K) :
    ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K,
      ∀ s, (e (AdicCompletion.of (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) s)).order = localAdicOrder (X.presheaf.stalk x) s := by
  obtain ⟨U, hU, hx, hs⟩ := smoothRelativeScheme_exists_affineStandardSmooth (K := K) n x
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : U)
  let := cartierBaseOpenLocalScalarTower (K := K) x hx
  let := hs
  let α := rationalAffineGermPoint x hx β
  have hα : RingHom.ker α.toRingHom = (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    rationalAffineGermPoint_ker x hx β hU
  let : (RingHom.ker α.toRingHom).IsMaximal := rationalPoint_ker_isMaximal α
  let : IsLocalization.AtPrime (X.presheaf.stalk x) (RingHom.ker α.toRingHom) := by
    have H := hU.isLocalization_stalk (⟨x, hx⟩ : U)
    simpa only [hα] using H
  exact standardSmoothRelativeDimension_exists_localCompletionCoordinates n α
    (X.presheaf.stalk x)

end MixedFujita
