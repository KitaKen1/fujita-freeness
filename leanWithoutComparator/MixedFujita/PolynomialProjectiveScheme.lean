/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.FiniteType
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
The actual polynomial projective Scheme, proper over its coefficient ring.
In particular R = K[T] supplies the proper ambient space of the diagonal
family. This does not identify a blow-up exceptional divisor or prove lct
semicontinuity; those are separate geometric inputs.
-/

@[expose] public section

namespace MixedFujita

open AlgebraicGeometry CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n : ℕ) (R : Type*) [CommRing R]

noncomputable def polynomialDegreeZeroEquiv :
    MvPolynomial.homogeneousSubmodule (Fin n) R 0 ≃+* R where
  toFun p := MvPolynomial.constantCoeff p.val
  invFun r := ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C (Fin n) r⟩
  left_inv p := by
    apply Subtype.ext
    exact ((MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp
      ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin n)).mpr p.property)).symm
  right_inv r := MvPolynomial.constantCoeff_C (Fin n) r
  map_add' p q := map_add MvPolynomial.constantCoeff p.val q.val
  map_mul' p q := map_mul MvPolynomial.constantCoeff p.val q.val

theorem polynomialDegreeZeroEquiv_symm_coe (r : R) :
    ((polynomialDegreeZeroEquiv n R).symm r : MvPolynomial (Fin n) R) = MvPolynomial.C r := rfl

theorem polynomial_finiteType_degreeZero :
    Algebra.FiniteType (MvPolynomial.homogeneousSubmodule (Fin n) R 0)
      (MvPolynomial (Fin n) R) := by
  have : IsScalarTower R (MvPolynomial.homogeneousSubmodule (Fin n) R 0)
      (MvPolynomial (Fin n) R) := IsScalarTower.of_algebraMap_eq
        (R := R) (S := MvPolynomial.homogeneousSubmodule (Fin n) R 0)
        (A := MvPolynomial (Fin n) R) (fun _ => rfl)
  exact Algebra.FiniteType.of_restrictScalars_finiteType R
    (MvPolynomial.homogeneousSubmodule (Fin n) R 0) (MvPolynomial (Fin n) R)

@[reducible]
noncomputable def polynomialProjectiveScheme : Scheme :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin n) R)

noncomputable def polynomialProjectiveToBase :
    polynomialProjectiveScheme n R ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin n) R) ≫
    Spec.map (polynomialDegreeZeroEquiv n R).symm.toCommRingCatIso.hom

theorem polynomialProjectiveToBase_isProper : IsProper (polynomialProjectiveToBase n R) := by
  have := polynomial_finiteType_degreeZero n R
  have hproper : IsProper (Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin n) R)) :=
    inferInstance
  have : IsIso (Spec.map (polynomialDegreeZeroEquiv n R).symm.toCommRingCatIso.hom) :=
    inferInstance
  unfold polynomialProjectiveToBase
  exact (MorphismProperty.cancel_right_of_respectsIso (P := @IsProper) _ _).mpr hproper

theorem polynomialProjectiveToBase_isClosedMap : IsClosedMap (polynomialProjectiveToBase n R) := by
  have := polynomialProjectiveToBase_isProper n R
  exact Scheme.Hom.isClosedMap _

theorem polynomialProjectiveToBase_closed_image {Z : Set (polynomialProjectiveScheme n R)}
    (hZ : IsClosed Z) : IsClosed ((polynomialProjectiveToBase n R) '' Z) :=
  polynomialProjectiveToBase_isClosedMap n R Z hZ

theorem polynomialProjectiveToBase_pullback_isProper {Y : Scheme}
    (g : Y ⟶ Spec (CommRingCat.of R)) :
    IsProper (CategoryTheory.Limits.pullback.snd (polynomialProjectiveToBase n R) g) := by
  have := polynomialProjectiveToBase_isProper n R
  infer_instance

theorem polynomialProjectiveToBase_good_neighborhood
    {Z : Set (polynomialProjectiveScheme n R)} (hZ : IsClosed Z)
    (y : Spec (CommRingCat.of R))
    (hy : ∀ x, polynomialProjectiveToBase n R x = y → x ∉ Z) :
    ∃ U : (Spec (CommRingCat.of R)).Opens, y ∈ U ∧
      ∀ x, polynomialProjectiveToBase n R x ∈ U → x ∉ Z := by
  let U : (Spec (CommRingCat.of R)).Opens :=
    ⟨((polynomialProjectiveToBase n R) '' Z)ᶜ,
      (polynomialProjectiveToBase_closed_image n R hZ).isOpen_compl⟩
  refine ⟨U, ?_, ?_⟩
  · rintro ⟨x, hx, hxy⟩
    exact hy x hxy hx
  · intro x hx hxZ
    exact hx ⟨x, hxZ, rfl⟩

end MixedFujita
