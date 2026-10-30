/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.EtaleCoordinateDifferentials
public import MixedFujita.TensorEtaleCoordinates
public import Mathlib.RingTheory.Kaehler.TensorProduct

/-!
Jacobians of étale coordinates over a ring and their base change (step 10, R4-3).

* `ringEtaleCoordinateBasis`: for formally étale coordinates `y : A[Y_1, …, Y_n] → B` over a
  commutative ring `A`, the basis `(d y_j)` of `Ω[B/A]` (the version over a ring of
  `etaleCoordinateBasis`). Two systems of coordinates `y, y₀` give the Jacobian
  `det(dy, dy₀) ∈ B`, a unit.
* `tensorCoordinatesOf`, `tensorCoordinatesOf_formallyEtale`: the coordinates `1 ⊗ y_j` of
  `L ⊗_A B` over a field `L` over `A` (check 521).
* `etaleCoordinateBasis_tensorCoordinatesOf_det`: **the Jacobian of the base-changed coordinates is
  the image of the Jacobian over `A`**: `Ω[L ⊗_A B / L] = (L ⊗_A B) ⊗_B Ω[B/A]` (Mathlib's
  `tensorKaehlerEquiv`) maps the basis `(d y_j)` to `(d(1 ⊗ y_j))`, and determinants commute with
  base change (`isBaseChange_basis_det`).

For the closure `T_A`, the canonical equations of the charts of the fibres `T_K` and `T_κ` (their
Jacobians) are therefore the images of one Jacobian over `A`, which transfers the relations of
canonical divisors from `T_K` to `T_κ`.
-/

@[expose] public section

open TensorProduct KaehlerDifferential

namespace MixedFujita

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section Ring

variable {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B] {n : ℕ}

/-- The basis `(d y_j)` of `Ω[B/A]` for formally étale coordinates over a ring. -/
noncomputable def ringEtaleCoordinateBasis (y : MvPolynomial (Fin n) A →ₐ[A] B)
    (hy : y.toRingHom.FormallyEtale) : Module.Basis (Fin n) B Ω[B⁄A] :=
  letI := y.toRingHom.toAlgebra
  haveI : IsScalarTower A (MvPolynomial (Fin n) A) B :=
    IsScalarTower.of_algebraMap_eq fun c => (y.commutes c).symm
  haveI : Algebra.FormallyEtale (MvPolynomial (Fin n) A) B := hy
  (isBaseChange_of_formallyEtale A (MvPolynomial (Fin n) A) B).basis (mvPolynomialBasis A (Fin n))

theorem ringEtaleCoordinateBasis_apply (y : MvPolynomial (Fin n) A →ₐ[A] B)
    (hy : y.toRingHom.FormallyEtale) (i : Fin n) :
    ringEtaleCoordinateBasis y hy i = D A B (y (MvPolynomial.X i)) := by
  let _ := y.toRingHom.toAlgebra
  have : IsScalarTower A (MvPolynomial (Fin n) A) B :=
    IsScalarTower.of_algebraMap_eq fun c => (y.commutes c).symm
  have : Algebra.FormallyEtale (MvPolynomial (Fin n) A) B := hy
  change (isBaseChange_of_formallyEtale A (MvPolynomial (Fin n) A) B).basis
    (mvPolynomialBasis A (Fin n)) i = _
  rw [IsBaseChange.basis_apply, mvPolynomialBasis_apply, map_D]
  rfl

/-- The Jacobian of two systems of étale coordinates is a unit. -/
theorem isUnit_ringEtaleCoordinateBasis_det (y y₀ : MvPolynomial (Fin n) A →ₐ[A] B)
    (hy : y.toRingHom.FormallyEtale) (hy₀ : y₀.toRingHom.FormallyEtale) :
    IsUnit ((ringEtaleCoordinateBasis y hy).det (ringEtaleCoordinateBasis y₀ hy₀)) :=
  Module.Basis.isUnit_det _ _

variable (L : Type u) [Field L] [Algebra A L]

/-- The coordinates `1 ⊗ y_j` of `L ⊗_A B` over `L`. -/
noncomputable def tensorCoordinatesOf (y : MvPolynomial (Fin n) A →ₐ[A] B) :
    MvPolynomial (Fin n) L →ₐ[L] L ⊗[A] B :=
  MvPolynomial.aeval fun j => (1 : L) ⊗ₜ[A] y (MvPolynomial.X j)

theorem tensorCoordinatesOf_X (y : MvPolynomial (Fin n) A →ₐ[A] B) (j : Fin n) :
    tensorCoordinatesOf L y (MvPolynomial.X j) = (1 : L) ⊗ₜ[A] y (MvPolynomial.X j) :=
  MvPolynomial.aeval_X _ _

/-- The base-changed coordinates are formally étale (check 521). -/
theorem tensorCoordinatesOf_formallyEtale (y : MvPolynomial (Fin n) A →ₐ[A] B)
    (hy : y.toRingHom.FormallyEtale) : (tensorCoordinatesOf L y).toRingHom.FormallyEtale := by
  let _ : Algebra (MvPolynomial (Fin n) A) B := y.toRingHom.toAlgebra
  have : IsScalarTower A (MvPolynomial (Fin n) A) B :=
    IsScalarTower.of_algebraMap_eq fun c => (y.commutes c).symm
  have : Algebra.FormallyEtale (MvPolynomial (Fin n) A) B := hy
  exact formallyEtale_tensorCoordinates (A := A) (W := L) (B := B) (n := n)

/-- **The Jacobian of base-changed coordinates is the image of the Jacobian over `A`.** -/
theorem etaleCoordinateBasis_tensorCoordinatesOf_det (y y₀ : MvPolynomial (Fin n) A →ₐ[A] B)
    (hy : y.toRingHom.FormallyEtale) (hy₀ : y₀.toRingHom.FormallyEtale) :
    (etaleCoordinateBasis (tensorCoordinatesOf L y) (tensorCoordinatesOf_formallyEtale L y hy)).det
        (etaleCoordinateBasis (tensorCoordinatesOf L y₀)
          (tensorCoordinatesOf_formallyEtale L y₀ hy₀)) =
      algebraMap B (L ⊗[A] B)
        ((ringEtaleCoordinateBasis y hy).det (ringEtaleCoordinateBasis y₀ hy₀)) := by
  have hmap : ∀ ω : Ω[B⁄A], tensorKaehlerEquiv A L B (L ⊗[A] B) ((1 : L ⊗[A] B) ⊗ₜ ω) =
      KaehlerDifferential.map A L B (L ⊗[A] B) ω := by
    intro ω
    have h1 : ((tensorKaehlerEquiv A L B (L ⊗[A] B)).toLinearMap.restrictScalars B).comp
        (TensorProduct.mk B (L ⊗[A] B) Ω[B⁄A] 1) = KaehlerDifferential.map A L B (L ⊗[A] B) := by
      apply Derivation.liftKaehlerDifferential_unique
      ext b
      simp [tensorKaehlerEquiv_tmul_D, map_D]
    exact LinearMap.congr_fun h1 ω
  have ibc : IsBaseChange (L ⊗[A] B) (KaehlerDifferential.map A L B (L ⊗[A] B)) :=
    IsBaseChange.of_equiv (tensorKaehlerEquiv A L B (L ⊗[A] B)) hmap
  have hbasis : ∀ (z : MvPolynomial (Fin n) A →ₐ[A] B) (hz : z.toRingHom.FormallyEtale),
      ibc.basis (ringEtaleCoordinateBasis z hz) =
        etaleCoordinateBasis (tensorCoordinatesOf L z) (tensorCoordinatesOf_formallyEtale L z hz) := by
    intro z hz
    apply Module.Basis.eq_of_apply_eq
    intro i
    rw [IsBaseChange.basis_apply, ringEtaleCoordinateBasis_apply, etaleCoordinateBasis_apply,
      map_D, tensorCoordinatesOf_X]
    rfl
  rw [← hbasis y hy, ← hbasis y₀ hy₀, isBaseChange_basis_det]

end Ring

end MixedFujita
