/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ClosedRationalPoints
public import MixedFujita.SmoothSchemeCoordinates

/-!
K-valued evaluations of stalks at actual closed points of a smooth scheme over an algebraically
closed field. The prime of a closed point in an affine open containing it is maximal, and the
sections over the affine open are a finite type K-algebra, so the residue field is K by the
Nullstellensatz. The evaluation respects the K-action from the structure morphism and extends to
the actual stalk. This identifies the actual residue field with K and gives completion
coordinates computing the intrinsic order; the number of variables is existential here.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of K))] [Smooth (X ↘ Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra

/-- The K-valued evaluation of the stalk at a closed point of an affine open. -/
noncomputable def smoothAffineClosedPointEvaluation {U : X.Opens} (hU : IsAffineOpen U) (x : X)
    (hx : x ∈ U) (hClosed : IsClosed {x}) : X.presheaf.stalk x →ₐ[K] K := by
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : U)
  have := cartierBaseOpenLocalScalarTower (K := K) x hx
  have : Algebra.Smooth K Γ(X, U) := smoothScheme_affineOpen_smooth hU
  have : (hU.primeIdealOf ⟨x, hx⟩).asIdeal.IsMaximal :=
    hU.primeIdealOf_isMaximal_of_isClosed ⟨x, hx⟩ hClosed
  have := hU.isLocalization_stalk (⟨x, hx⟩ : U)
  exact closedPointLocalEvaluation (K := K) (hU.primeIdealOf ⟨x, hx⟩).asIdeal (X.presheaf.stalk x)

theorem smoothScheme_closedPoint_has_localEvaluation (x : X) (hClosed : IsClosed {x}) :
    Nonempty (X.presheaf.stalk x →ₐ[K] K) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ (⊤ : X.Opens) from Opens.mem_top x) isOpen_univ
  exact ⟨smoothAffineClosedPointEvaluation hU x hx hClosed⟩

theorem smoothScheme_closedPoint_residueField (x : X) (hClosed : IsClosed {x}) :
    Nonempty ((X.presheaf.stalk x ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ≃ₐ[K] K) := by
  obtain ⟨β⟩ := smoothScheme_closedPoint_has_localEvaluation (K := K) x hClosed
  exact ⟨rationalLocalPointResidueEquiv β⟩

theorem smoothScheme_closedPoint_exists_stalkCoordinates (x : X) (hClosed : IsClosed {x}) :
    ∃ n : ℕ, ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K,
      ∀ s, (e (AdicCompletion.of (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) s)).order = localAdicOrder (X.presheaf.stalk x) s := by
  obtain ⟨β⟩ := smoothScheme_closedPoint_has_localEvaluation (K := K) x hClosed
  exact smoothScheme_rationalPoint_exists_stalkCoordinates x β

end MixedFujita
