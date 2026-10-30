/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import Mathlib.LinearAlgebra.Determinant

/-!
Bases of Kähler differentials from étale coordinates, the algebra behind the canonical divisor K_X
(step 1). If x : K[X_1, …, X_n] → R is formally étale, then Ω[R/K] is the base change of the free
module Ω[K[X]/K], so the differentials d x_1, …, d x_n form a basis of Ω[R/K]. For two such
coordinate systems x and y on the same ring the change of basis determinant, the Jacobian
determinant of y with respect to x, is a unit of R. Determinants of bases commute with base change,
and along a formally étale map φ : R → S, such as the localization of a stalk to the function field,
the coordinate bases of φ ∘ x are the base changes of those of x; hence the Jacobian determinant
of φ ∘ y with respect to φ ∘ x is the image of a unit of R.
-/

@[expose] public section

namespace MixedFujita

open KaehlerDifferential

section BaseChange

variable {R S M N ι : Type*} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] [Fintype ι] [DecidableEq ι]
  {ε : M →ₗ[R] N}

/-- Determinants of bases commute with base change. -/
theorem isBaseChange_basis_det (ibc : IsBaseChange S ε) (b b' : Module.Basis ι R M) :
    (ibc.basis b).det (ibc.basis b') = algebraMap R S (b.det b') := by
  rw [Module.Basis.det_apply, Module.Basis.det_apply, RingHom.map_det]
  congr 1
  ext i j
  rw [Module.Basis.toMatrix_apply, IsBaseChange.basis_apply, IsBaseChange.basis_repr_comp_apply,
    RingHom.mapMatrix_apply, Matrix.map_apply, Module.Basis.toMatrix_apply]

end BaseChange

variable {K : Type*} [Field K] {n : ℕ}

section Coordinates

variable {R : Type*} [CommRing R] [Algebra K R]

/-- The basis (d x_i) of Ω[R/K] for formally étale coordinates x : K[X_1, …, X_n] → R. -/
noncomputable def etaleCoordinateBasis (x : MvPolynomial (Fin n) K →ₐ[K] R)
    (hx : x.toRingHom.FormallyEtale) : Module.Basis (Fin n) R Ω[R⁄K] :=
  letI := x.toRingHom.toAlgebra
  haveI : IsScalarTower K (MvPolynomial (Fin n) K) R :=
    IsScalarTower.of_algebraMap_eq fun c => (x.commutes c).symm
  haveI : Algebra.FormallyEtale (MvPolynomial (Fin n) K) R := hx
  (isBaseChange_of_formallyEtale K (MvPolynomial (Fin n) K) R).basis
    (mvPolynomialBasis K (Fin n))

theorem etaleCoordinateBasis_apply (x : MvPolynomial (Fin n) K →ₐ[K] R)
    (hx : x.toRingHom.FormallyEtale) (i : Fin n) :
    etaleCoordinateBasis x hx i = D K R (x (MvPolynomial.X i)) := by
  let _ := x.toRingHom.toAlgebra
  have : IsScalarTower K (MvPolynomial (Fin n) K) R :=
    IsScalarTower.of_algebraMap_eq fun c => (x.commutes c).symm
  have : Algebra.FormallyEtale (MvPolynomial (Fin n) K) R := hx
  change (isBaseChange_of_formallyEtale K (MvPolynomial (Fin n) K) R).basis
    (mvPolynomialBasis K (Fin n)) i = _
  rw [IsBaseChange.basis_apply, mvPolynomialBasis_apply, map_D]
  rfl

/-- The Jacobian determinant of y with respect to x is a unit. -/
theorem isUnit_etaleCoordinateBasis_det (x y : MvPolynomial (Fin n) K →ₐ[K] R)
    (hx : x.toRingHom.FormallyEtale) (hy : y.toRingHom.FormallyEtale) :
    IsUnit ((etaleCoordinateBasis x hx).det (etaleCoordinateBasis y hy)) :=
  Module.Basis.isUnit_det _ _

end Coordinates

section Compatibility

variable {R S : Type*} [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]

theorem formallyEtale_comp (φ : R →ₐ[K] S) (hφ : φ.toRingHom.FormallyEtale)
    (x : MvPolynomial (Fin n) K →ₐ[K] R) (hx : x.toRingHom.FormallyEtale) :
    (φ.comp x).toRingHom.FormallyEtale :=
  RingHom.FormallyEtale.comp hx hφ

/-- Along a formally étale map φ, the coordinate basis of φ ∘ x is the base change of the
coordinate basis of x, and Jacobian determinants are mapped by φ. -/
theorem etaleCoordinateBasis_det_comp (φ : R →ₐ[K] S) (hφ : φ.toRingHom.FormallyEtale)
    (x y : MvPolynomial (Fin n) K →ₐ[K] R) (hx : x.toRingHom.FormallyEtale)
    (hy : y.toRingHom.FormallyEtale) :
    (etaleCoordinateBasis (φ.comp x) (formallyEtale_comp φ hφ x hx)).det
        (etaleCoordinateBasis (φ.comp y) (formallyEtale_comp φ hφ y hy)) =
      φ ((etaleCoordinateBasis x hx).det (etaleCoordinateBasis y hy)) := by
  let _ := φ.toRingHom.toAlgebra
  have : IsScalarTower K R S := IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  have : Algebra.FormallyEtale R S := hφ
  set ibc := isBaseChange_of_formallyEtale K R S
  have hbasis : ∀ (z : MvPolynomial (Fin n) K →ₐ[K] R) (hz : z.toRingHom.FormallyEtale),
      ibc.basis (etaleCoordinateBasis z hz) =
        etaleCoordinateBasis (φ.comp z) (formallyEtale_comp φ hφ z hz) := by
    intro z hz
    apply Module.Basis.eq_of_apply_eq
    intro i
    rw [IsBaseChange.basis_apply, etaleCoordinateBasis_apply, etaleCoordinateBasis_apply, map_D]
    rfl
  rw [← hbasis x hx, ← hbasis y hy, isBaseChange_basis_det]
  rfl

end Compatibility

end MixedFujita
