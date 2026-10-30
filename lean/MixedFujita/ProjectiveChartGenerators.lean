/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveBaseConstants

/-!
The coordinate ratios generate the functions on a coordinate chart of a closed subscheme of
projective space (the generators used for the tangent coordinates of section 5.1 of the
manuscript).

Let e be a closed immersion of Y into polynomial projective space over K, compatible with the
maps to the base. The chart of Y where the k-th coordinate does not vanish is affine, the constant
polynomials pull back to the constants of the chart, and the pullbacks of the variables, that is
the ratios X_j / X_k, generate the functions on the chart as a K-algebra.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

attribute [local instance] cartierBaseOpenAlgebra

variable {K : Type u} [Field K] {n : ℕ} {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of K))]
  (e : Y ⟶ polynomialProjectiveScheme n K)

omit [Y.Over (Spec (CommRingCat.of K))] in
/-- The coordinate charts of a closed subscheme of projective space are affine. -/
theorem projectivePullbackCoordinateOpen_isAffineOpen [IsClosedImmersion e] (k : Fin n) :
    IsAffineOpen (projectivePullbackCoordinateOpen e k) :=
  (Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K) (MvPolynomial.X k)
    (MvPolynomial.isHomogeneous_X K k) Nat.zero_lt_one).preimage e

/-- Constant polynomials pull back to the constants of the chart. -/
theorem projectivePullbackAffinePolynomialMap_C_eq_algebraMap
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K)) (k : Fin n) (c : K) :
    projectivePullbackAffinePolynomialMap e k (MvPolynomial.C c) =
      algebraMap K Γ(Y, projectivePullbackCoordinateOpen e k) c := by
  rw [projectivePullbackAffinePolynomialMap_C e he k c]
  change _ = ((Y.baseRingToStructurePresheaf K).app
    (op (projectivePullbackCoordinateOpen e k))).hom c
  rw [Scheme.baseRingToStructurePresheaf_app]
  rfl

/-- The ratios of the coordinates generate the functions on a coordinate chart. -/
theorem projectivePullback_adjoin_coordinates_eq_top [IsClosedImmersion e]
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K)) (k : Fin n) :
    Algebra.adjoin K (Set.range fun j : {j : Fin n // j ≠ k} =>
      projectivePullbackAffinePolynomialMap e k (MvPolynomial.X j)) = ⊤ := by
  rw [eq_top_iff]
  intro a _
  obtain ⟨p, rfl⟩ := projectivePullbackAffinePolynomialMap_surjective e k a
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [projectivePullbackAffinePolynomialMap_C_eq_algebraMap e he k c]
    exact Subalgebra.algebraMap_mem _ c
  | add p q hp hq =>
    rw [map_add]
    exact Subalgebra.add_mem _ (hp Algebra.mem_top) (hq Algebra.mem_top)
  | mul_X p j hp =>
    rw [map_mul]
    exact Subalgebra.mul_mem _ (hp Algebra.mem_top) (Algebra.subset_adjoin ⟨j, rfl⟩)

end MixedFujita
