/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Smooth.Flat

/-!
Divisibility by a coordinate descends from `K ⊗_A B` to `B` (step 10, R4-3).

* `mvPolynomialQuotientXEquiv`: `A[Y_1, …, Y_n]/(Y_a) ≅ A[Y_j : j ≠ a]` (renaming, Mathlib's
  `optionEquivLeft` with `Y_a ↦ t`, and `A[Y_j : j ≠ a][t]/(t) ≅ A[Y_j : j ≠ a]`), so `A[Y]/(Y_a)`
  is flat over `A` (`flat_mvPolynomial_quotient_X`).
* `mem_span_coordinate_of_tmul_mem_span`: let `B` be flat over `A[Y]` and `A → K` injective. If
  `1 ⊗ b` is a multiple of `1 ⊗ y_a` in `K ⊗_A B`, then `b` is a multiple of `y_a` in `B`. The
  module `M = A[Y]/(Y_a) ⊗_{A[Y]} B = B/y_a B` is flat over `A` (base change, then transitivity),
  so `M → K ⊗_A M` is injective, and `1 ⊗ b` maps to `0` there. The same holds for `B` formally
  étale over `A[Y]` and of finite presentation over `A`
  (`mem_span_coordinate_of_tmul_mem_span_of_formallyEtale`).

For the chart rings `B` of the closure `T_A` (étale over `A[Y]` by check 512) and `K ⊗_A B` those
of `T`, this says `y_a (K ⊗_A B) ∩ B = y_a B`: the closure of a boundary component `V(y_a)` of `T`
is `V(y_a)` on the chart of `T_A`.
-/

@[expose] public section

open TensorProduct

namespace MixedFujita

universe u

section Coordinate

variable (A : Type u) [CommRing A] {n : ℕ} (a : Fin n)

/-- `A[Y_1, …, Y_n] ≅ A[Y_j : j ≠ a][t]` with `Y_a ↦ t`. -/
noncomputable def mvPolynomialSplitCoordinate :
    MvPolynomial (Fin n) A ≃ₐ[A] Polynomial (MvPolynomial {j : Fin n // j ≠ a} A) :=
  (MvPolynomial.renameEquiv A (Equiv.optionSubtypeNe a).symm).trans
    (MvPolynomial.optionEquivLeft A {j : Fin n // j ≠ a})

theorem mvPolynomialSplitCoordinate_X_self :
    mvPolynomialSplitCoordinate A a (MvPolynomial.X a) = Polynomial.X := by
  simp [mvPolynomialSplitCoordinate, MvPolynomial.rename_X, MvPolynomial.optionEquivLeft_X_none]

/-- **`A[Y]/(Y_a) ≅ A[Y_j : j ≠ a]`.** -/
noncomputable def mvPolynomialQuotientXEquiv :
    (MvPolynomial (Fin n) A ⧸ Ideal.span {(MvPolynomial.X a : MvPolynomial (Fin n) A)}) ≃ₐ[A]
      MvPolynomial {j : Fin n // j ≠ a} A :=
  (Ideal.quotientEquivAlg (Ideal.span {(MvPolynomial.X a : MvPolynomial (Fin n) A)})
    (Ideal.span {Polynomial.X - Polynomial.C 0}) (mvPolynomialSplitCoordinate A a) (by
      rw [Ideal.map_span, Set.image_singleton, Polynomial.C_0, sub_zero]
      congr 1
      rw [Set.singleton_eq_singleton_iff]
      exact (mvPolynomialSplitCoordinate_X_self A a).symm)).trans
    ((Polynomial.quotientSpanXSubCAlgEquiv (0 : MvPolynomial {j : Fin n // j ≠ a} A)).restrictScalars A)

/-- `A[Y]/(Y_a)` is flat over `A`. -/
theorem flat_mvPolynomial_quotient_X :
    Module.Flat A (MvPolynomial (Fin n) A ⧸ Ideal.span {(MvPolynomial.X a : MvPolynomial (Fin n) A)}) :=
  Module.Flat.of_linearEquiv (mvPolynomialQuotientXEquiv A a).toLinearEquiv

end Coordinate

section Descent

variable {A : Type u} [CommRing A] {n : ℕ} {B : Type u} [CommRing B] [Algebra A B]
  [Algebra (MvPolynomial (Fin n) A) B] [IsScalarTower A (MvPolynomial (Fin n) A) B]
  {K : Type u} [CommRing K] [Algebra A K]

/-- **Divisibility by a coordinate descends**: for `B` flat over `A[Y]` and `A → K` injective, if
`1 ⊗ b` is a multiple of `1 ⊗ y_a` in `K ⊗_A B`, then `b` is a multiple of `y_a` in `B`. -/
theorem mem_span_coordinate_of_tmul_mem_span [Module.Flat (MvPolynomial (Fin n) A) B]
    (hK : Function.Injective (algebraMap A K)) (a : Fin n) (b : B)
    (hb : (1 : K) ⊗ₜ[A] b ∈ Ideal.span
      {(1 : K) ⊗ₜ[A] algebraMap (MvPolynomial (Fin n) A) B (MvPolynomial.X a)}) :
    b ∈ Ideal.span {algebraMap (MvPolynomial (Fin n) A) B (MvPolynomial.X a)} := by
  classical
  let P := MvPolynomial (Fin n) A
  let y : B := algebraMap P B (MvPolynomial.X a)
  let I : Ideal P := Ideal.span {(MvPolynomial.X a : P)}
  let Q := P ⧸ I
  let M := Q ⊗[P] B
  have : Module.Flat A Q := flat_mvPolynomial_quotient_X A a
  have : Module.Flat A M := Module.Flat.trans A Q M
  let j : B →ₗ[A] M := (TensorProduct.mk P Q B 1).restrictScalars A
  have hinj : Function.Injective ((Algebra.linearMap A K).rTensor M) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ hK
  let Φ : K ⊗[A] B →ₗ[A] K ⊗[A] M := j.lTensor K
  have hX : Ideal.Quotient.mk I (MvPolynomial.X a) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  have hX' : (MvPolynomial.X a : P) • (1 : Q) = 0 := by
    rw [show (MvPolynomial.X a : P) • (1 : Q) = Ideal.Quotient.mk I (MvPolynomial.X a * 1) from rfl,
      mul_one, hX]
  have hΦ0 : ∀ w : K ⊗[A] B, Φ (((1 : K) ⊗ₜ[A] y) * w) = 0 := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul k b' =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, LinearMap.lTensor_tmul]
      have : j (y * b') = 0 := by
        change (1 : Q) ⊗ₜ[P] (y * b') = 0
        rw [show y * b' = (MvPolynomial.X a : P) • b' from (Algebra.smul_def _ _).symm,
          ← TensorProduct.smul_tmul, hX', TensorProduct.zero_tmul]
      rw [this, TensorProduct.tmul_zero]
    | add w₁ w₂ h₁ h₂ => rw [mul_add, map_add, h₁, h₂, add_zero]
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hb
  have h1 : (Algebra.linearMap A K).rTensor M ((1 : A) ⊗ₜ[A] j b) = 0 := by
    rw [LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one]
    change Φ ((1 : K) ⊗ₜ[A] b) = 0
    rw [← hw, mul_comm]
    exact hΦ0 w
  have h2 : j b = 0 := by
    have := hinj (h1.trans (map_zero _).symm)
    simpa using congrArg (TensorProduct.lid A M) this
  have h3 : Submodule.Quotient.mk (p := I • (⊤ : Submodule P B)) b = 0 := by
    have := congrArg (TensorProduct.quotTensorEquivQuotSMul B I) h2
    rw [map_zero] at this
    change TensorProduct.quotTensorEquivQuotSMul B I ((1 : Q) ⊗ₜ[P] b) = 0 at this
    rw [← map_one (Ideal.Quotient.mk I), TensorProduct.quotTensorEquivQuotSMul_mk_tmul,
      one_smul] at this
    exact this
  rw [Submodule.Quotient.mk_eq_zero] at h3
  have hle : I • (⊤ : Submodule P B) ≤
      (Ideal.span {y}).restrictScalars P := by
    rw [Submodule.smul_le]
    intro r hr m _
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [Submodule.restrictScalars_mem, Algebra.smul_def, map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
  exact hle h3

/-- **Divisibility by an étale coordinate descends**: the same for `B` formally étale over `A[Y]`
and of finite presentation over `A` (then `B` is étale, hence flat, over `A[Y]`). -/
theorem mem_span_coordinate_of_tmul_mem_span_of_formallyEtale
    [Algebra.FormallyEtale (MvPolynomial (Fin n) A) B] [Algebra.FinitePresentation A B]
    (hK : Function.Injective (algebraMap A K)) (a : Fin n) (b : B)
    (hb : (1 : K) ⊗ₜ[A] b ∈ Ideal.span
      {(1 : K) ⊗ₜ[A] algebraMap (MvPolynomial (Fin n) A) B (MvPolynomial.X a)}) :
    b ∈ Ideal.span {algebraMap (MvPolynomial (Fin n) A) B (MvPolynomial.X a)} := by
  have : Algebra.FinitePresentation (MvPolynomial (Fin n) A) B :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation A _ B
  have : Algebra.Etale (MvPolynomial (Fin n) A) B := {}
  exact mem_span_coordinate_of_tmul_mem_span hK a b hb

end Descent

end MixedFujita
