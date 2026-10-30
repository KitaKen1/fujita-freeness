/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PolynomialProjectiveScheme

/-!
The standard coordinate charts cover the actual polynomial projective
Scheme. Each chart is the Spec of the degree-zero homogeneous localization.
The affine polynomial ring identification is supplied by ProjectiveChartEquiv
and ProjectiveAffineCharts. The blow-up identification remains separate.
-/

@[expose] public section

namespace MixedFujita

open AlgebraicGeometry CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n : ℕ) (R : Type*) [CommRing R]

theorem polynomial_adjoin_variables_degreeZero :
    Algebra.adjoin (MvPolynomial.homogeneousSubmodule (Fin n) R 0)
      (Set.range (MvPolynomial.X : Fin n → MvPolynomial (Fin n) R)) = ⊤ := by
  let S := Algebra.adjoin (MvPolynomial.homogeneousSubmodule (Fin n) R 0)
    (Set.range (MvPolynomial.X : Fin n → MvPolynomial (Fin n) R))
  apply top_unique
  intro p hp
  clear hp
  induction p using MvPolynomial.induction_on with
  | C r =>
    exact S.algebraMap_mem ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C (Fin n) r⟩
  | add p q hp hq => exact S.add_mem hp hq
  | mul_X p i hp => exact S.mul_mem hp (Algebra.subset_adjoin (Set.mem_range_self i))

theorem polynomialProjective_coordinate_opens_cover :
    (⨆ i : Fin n, Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R)
      (MvPolynomial.X i)) = ⊤ :=
  Proj.iSup_basicOpen_eq_top' _ _
    (fun i => ⟨1, MvPolynomial.isHomogeneous_X R i⟩)
    (polynomial_adjoin_variables_degreeZero n R)

theorem polynomialProjective_exists_coordinate_chart
    (x : polynomialProjectiveScheme n R) :
    ∃ i : Fin n, x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R)
      (MvPolynomial.X i) := by
  apply TopologicalSpace.Opens.mem_iSup.mp
  rw [polynomialProjective_coordinate_opens_cover n R]
  trivial

noncomputable def polynomialProjectiveCoordinateChart (i : Fin n) : Scheme :=
  (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X i)).toScheme

noncomputable def polynomialProjectiveCoordinateChartIso (i : Fin n) :
    polynomialProjectiveCoordinateChart n R i ≅
      Spec (CommRingCat.of (HomogeneousLocalization.Away
        (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X i))) :=
  Proj.basicOpenIsoSpec _ _ (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one

end MixedFujita
