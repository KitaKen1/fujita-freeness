/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.GeometricGradedTaylor
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.RiemannRoch.Space
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
public import TauCeti.AlgebraicGeometry.Scheme.DiscreteValuationStalk

/-!
On an actual proper smooth integral curve, Cartier global sections are
finite dimensional. Smoothness supplies regular stalks and hence DVRs at
codimension-one points; properness and geometric dimension one then supply
the existing line-bundle finiteness theorem. No DVR, finite-dimensionality,
completion-coordinate or order-bound hypothesis is supplied by the caller.
This theorem is for curves, not arbitrary projective dimension.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Order
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of K))] [Smooth (X ↘ Spec (CommRingCat.of K))]

include K in
theorem smoothOverField_stalk_regular (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  let : ∀ y : Spec (CommRingCat.of K),
      IsRegularLocalRing ((Spec (CommRingCat.of K)).presheaf.stalk y) := fun y => inferInstance
  exact TauCeti.AlgebraicGeometry.isRegularLocalRing_stalk_of_smooth
    (X ↘ Spec (CommRingCat.of K)) x

include K in
theorem smoothOverField_codimensionOne_stalk_DVR (x : TauCeti.AlgebraicGeometry.CodimensionOnePoint X) :
    letI := smoothOverField_stalk_regular (K := K) (x : X)
    IsDiscreteValuationRing (X.presheaf.stalk (x : X)) := by
  let := smoothOverField_stalk_regular (K := K) (x : X)
  infer_instance

variable [IsIntegral X] [IsProper (X ↘ Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseLocalScalarTower cartierBaseSectionScalarTower

theorem properSmoothCurve_finiteDimensional_cartierSections
    (hX : topologicalKrullDim X = 1) (D : CartierDivisor X) :
    FiniteDimensional K Γ(D.sheaf, ⊤) := by
  let : ∀ y : TauCeti.AlgebraicGeometry.CodimensionOnePoint X,
      IsDiscreteValuationRing (X.presheaf.stalk (y : X)) := fun y =>
    smoothOverField_codimensionOne_stalk_DVR (K := K) y
  have hdim (x : X) : coheight x ≤ 1 := by
    exact_mod_cast (TauCeti.coheight_le_topologicalKrullDim x).trans hX.le
  have h := TauCeti.AlgebraicGeometry.InvertibleSheaf.finiteDimensional_cohomology_zero
    K hdim D.toInvertibleSheaf
  rw [CartierDivisor.toInvertibleSheaf_obj] at h
  let := h
  exact Module.Finite.equiv (Scheme.Modules.cohomologyZeroBaseLinearEquiv K X D.sheaf)

theorem properSmoothCurve_finiteDimensional_gradedSections
    (hX : topologicalKrullDim X = 1) (A : CartierDivisor X) :
    ∀ j : ℕ, FiniteDimensional K Γ((j • A).sheaf, ⊤) := fun j =>
  properSmoothCurve_finiteDimensional_cartierSections (K := K) hX (j • A)

end MixedFujita
