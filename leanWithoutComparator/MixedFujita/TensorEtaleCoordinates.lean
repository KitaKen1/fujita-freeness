/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.WittTwoLift
public import MixedFujita.CoordinateFrobeniusLift
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.IsTensorProduct

/-!
Étale coordinates after a base change of the coefficients (step 10, R4-6).

Let `B` be an algebra over `A[Y_1, …, Y_n]` (the coordinates `y_j` of an étale chart of the closure
`T_A`) and `W` an `A`-algebra (the Witt vectors `W₂(κ)` of check 519). Then `W ⊗_A B` is an algebra
over `W[Y]` through the coordinates `1 ⊗ y_j` (`tensorCoordinates`), and
`W ⊗_A B ≅ W[Y] ⊗_{A[Y]} B` (`isPushout_tensorCoordinates`): the square `A → A[Y]`, `W → W[Y]` is a
pushout, so by pasting (Mathlib's `Algebra.IsPushout.comp_iff`) the right-hand square of
`A → A[Y] → B` over `W → W[Y] → W ⊗_A B` is one. Hence `W ⊗_A B` is formally étale over `W[Y]`
when `B` is over `A[Y]` (`formallyEtale_tensorCoordinates`).

This is the hypothesis of the coordinate Frobenius lifts of check 520 for the lifts
`L_x = W₂(κ) ⊗_A Γ(T_A, U_x)` of the lift data of check 491: on `W₂(κ) ⊗_A B`, with `κ ⊗_A B`
nonzero, there is a Frobenius lift over the reduction `W₂(κ) ⊗_A B → κ ⊗_A B` which is the
Frobenius of `W₂(κ)` on `W₂(κ) ⊗ 1`, maps every coordinate `1 ⊗ y_j` to its `p`-th power and the
Teichmüller lifts `[k] ⊗ 1` to their `p`-th powers (`exists_wittTwo_coordinateFrobeniusLift`).
-/

@[expose] public section

open TensorProduct

namespace MixedFujita

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra MvPolynomial.algebraMvPolynomial

section TensorCoordinates

variable {A W B : Type u} [CommRing A] [CommRing W] [CommRing B] [Algebra A W] [Algebra A B]
  {n : ℕ} [Algebra (MvPolynomial (Fin n) A) B] [IsScalarTower A (MvPolynomial (Fin n) A) B]

variable (A W B n) in
/-- The coordinates `1 ⊗ y_j` of `W ⊗_A B` over `W`. -/
noncomputable def tensorCoordinates : MvPolynomial (Fin n) W →ₐ[W] W ⊗[A] B :=
  MvPolynomial.aeval fun j =>
    (1 : W) ⊗ₜ[A] algebraMap (MvPolynomial (Fin n) A) B (MvPolynomial.X j)

omit [IsScalarTower A (MvPolynomial (Fin n) A) B] in
theorem tensorCoordinates_X (j : Fin n) :
    tensorCoordinates A W B n (MvPolynomial.X j) =
      (1 : W) ⊗ₜ[A] algebraMap (MvPolynomial (Fin n) A) B (MvPolynomial.X j) :=
  MvPolynomial.aeval_X _ _

omit [IsScalarTower A (MvPolynomial (Fin n) A) B] in
theorem tensorCoordinates_C (w : W) :
    tensorCoordinates A W B n (MvPolynomial.C w) = w ⊗ₜ[A] (1 : B) := by
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
  rfl

variable (A W B n) in
/-- `W ⊗_A B` as a `W[Y]`-algebra through the coordinates `1 ⊗ y_j`. -/
@[instance_reducible]
noncomputable def tensorCoordinatesAlgebra : Algebra (MvPolynomial (Fin n) W) (W ⊗[A] B) :=
  (tensorCoordinates A W B n).toRingHom.toAlgebra

variable (A W B n) in
/-- `W ⊗_A B` as an `A[Y]`-algebra through `B`. -/
@[instance_reducible]
noncomputable def tensorBaseCoordinatesAlgebra : Algebra (MvPolynomial (Fin n) A) (W ⊗[A] B) :=
  ((algebraMap B (W ⊗[A] B)).comp (algebraMap (MvPolynomial (Fin n) A) B)).toAlgebra

attribute [local instance] tensorCoordinatesAlgebra tensorBaseCoordinatesAlgebra

omit [IsScalarTower A (MvPolynomial (Fin n) A) B] in
theorem tensorCoordinates_algebraMap_X (j : Fin n) :
    algebraMap (MvPolynomial (Fin n) W) (W ⊗[A] B) (MvPolynomial.X j) =
      (1 : W) ⊗ₜ[A] algebraMap (MvPolynomial (Fin n) A) B (MvPolynomial.X j) :=
  tensorCoordinates_X j

omit [IsScalarTower A (MvPolynomial (Fin n) A) B] in
/-- The scalar tower `W → W[Y] → W ⊗_A B`. -/
theorem tensorCoordinates_isScalarTower_coeff :
    IsScalarTower W (MvPolynomial (Fin n) W) (W ⊗[A] B) :=
  IsScalarTower.of_algebraMap_eq fun w => by
    change algebraMap W (W ⊗[A] B) w = tensorCoordinates A W B n (MvPolynomial.C w)
    rw [tensorCoordinates_C]
    rfl

omit [IsScalarTower A (MvPolynomial (Fin n) A) B] in
/-- The scalar tower `A → W[Y] → W ⊗_A B`. -/
theorem tensorCoordinates_isScalarTower_base :
    IsScalarTower A (MvPolynomial (Fin n) W) (W ⊗[A] B) :=
  IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A (W ⊗[A] B) a =
      tensorCoordinates A W B n (MvPolynomial.C (algebraMap A W a))
    rw [tensorCoordinates_C]
    rfl

omit [IsScalarTower A (MvPolynomial (Fin n) A) B] in
/-- The scalar tower `A[Y] → B → W ⊗_A B`. -/
theorem tensorBaseCoordinates_isScalarTower_right :
    IsScalarTower (MvPolynomial (Fin n) A) B (W ⊗[A] B) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The scalar tower `A[Y] → W[Y] → W ⊗_A B`. -/
theorem tensorBaseCoordinates_isScalarTower_left :
    IsScalarTower (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) W) (W ⊗[A] B) := by
  refine IsScalarTower.of_algebraMap_eq fun P => ?_
  have h : (algebraMap (MvPolynomial (Fin n) A) (W ⊗[A] B)) =
      (tensorCoordinates A W B n).toRingHom.comp
        (algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) W)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change (1 : W) ⊗ₜ[A] algebraMap (MvPolynomial (Fin n) A) B (MvPolynomial.C a) =
        tensorCoordinates A W B n
          (algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) W) (MvPolynomial.C a))
      rw [MvPolynomial.algebraMap_def, MvPolynomial.map_C, tensorCoordinates_C,
        ← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply, Algebra.algebraMap_eq_smul_one,
        Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    · intro j
      change (1 : W) ⊗ₜ[A] algebraMap (MvPolynomial (Fin n) A) B (MvPolynomial.X j) =
        tensorCoordinates A W B n
          (algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) W) (MvPolynomial.X j))
      rw [MvPolynomial.algebraMap_def, MvPolynomial.map_X, tensorCoordinates_X]
  exact RingHom.congr_fun h P

/-- The scalar tower `A → A[Y] → W ⊗_A B`. -/
theorem tensorBaseCoordinates_isScalarTower_base :
    IsScalarTower A (MvPolynomial (Fin n) A) (W ⊗[A] B) :=
  IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A (W ⊗[A] B) a =
      (1 : W) ⊗ₜ[A] algebraMap (MvPolynomial (Fin n) A) B (algebraMap A (MvPolynomial (Fin n) A) a)
    rw [← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight.commutes a).symm

attribute [local instance] tensorCoordinates_isScalarTower_coeff
  tensorCoordinates_isScalarTower_base tensorBaseCoordinates_isScalarTower_right
  tensorBaseCoordinates_isScalarTower_left tensorBaseCoordinates_isScalarTower_base

/-- **`W ⊗_A B = W[Y] ⊗_{A[Y]} B`**: the coordinate square is a pushout. -/
theorem isPushout_tensorCoordinates :
    Algebra.IsPushout (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) W) B (W ⊗[A] B) := by
  have h1 : Algebra.IsPushout A B W (W ⊗[A] B) := inferInstance
  have h2 : Algebra.IsPushout (MvPolynomial (Fin n) A) B (MvPolynomial (Fin n) W) (W ⊗[A] B) :=
    (Algebra.IsPushout.comp_iff A (MvPolynomial (Fin n) A) W (MvPolynomial (Fin n) W)).mp h1
  exact h2.symm

/-- **Étale coordinates survive the base change**: if `B` is formally étale over `A[Y]`, then
`W ⊗_A B` is formally étale over `W[Y]` through the coordinates `1 ⊗ y_j`. -/
theorem formallyEtale_tensorCoordinates [Algebra.FormallyEtale (MvPolynomial (Fin n) A) B] :
    Algebra.FormallyEtale (MvPolynomial (Fin n) W) (W ⊗[A] B) := by
  have := isPushout_tensorCoordinates (A := A) (W := W) (B := B) (n := n)
  exact Algebra.FormallyEtale.of_equiv (Algebra.IsPushout.equiv (MvPolynomial (Fin n) A)
    (MvPolynomial (Fin n) W) B (W ⊗[A] B))

end TensorCoordinates

section WittTwoCoordinates

attribute [local instance] tensorCoordinatesAlgebra tensorCoordinates_isScalarTower_coeff

variable (p : ℕ) [Fact p.Prime] (κ : Type u) [Field κ] [CharP κ p] [PerfectRing κ p]
  {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Algebra A κ]
  [Algebra A (WittTwo p κ)]
  (h : ∀ a : A, wittTwoReduction p κ (algebraMap A (WittTwo p κ) a) = algebraMap A κ a)
  {n : ℕ} [Algebra (MvPolynomial (Fin n) A) B] [IsScalarTower A (MvPolynomial (Fin n) A) B]

/-- **The coordinate Frobenius lift on `W₂(κ) ⊗_A B`**: for `B` formally étale over `A[Y]` with
`κ ⊗_A B ≠ 0`, there is a ring endomorphism `F` of `W₂(κ) ⊗_A B` lifting the `p`-th power map of
`κ ⊗_A B`, equal to the Frobenius of `W₂(κ)` on `W₂(κ) ⊗ 1`, with `F(1 ⊗ y_j) = (1 ⊗ y_j)^p` and
`F([k] ⊗ 1) = ([k] ⊗ 1)^p`. -/
theorem exists_wittTwo_coordinateFrobeniusLift [Algebra.FormallyEtale (MvPolynomial (Fin n) A) B]
    [Nontrivial (κ ⊗[A] B)] :
    ∃ F : WittTwo p κ ⊗[A] B →+* WittTwo p κ ⊗[A] B,
      (∀ x, Algebra.TensorProduct.map (wittTwoReductionAlgHom p κ h) (AlgHom.id A B) (F x) =
        Algebra.TensorProduct.map (wittTwoReductionAlgHom p κ h) (AlgHom.id A B) x ^ p) ∧
      (∀ w, F (w ⊗ₜ[A] (1 : B)) = wittTwoFrobenius p κ w ⊗ₜ[A] (1 : B)) ∧
      (∀ j, F ((1 : WittTwo p κ) ⊗ₜ[A] algebraMap (MvPolynomial (Fin n) A) B (MvPolynomial.X j)) =
        ((1 : WittTwo p κ) ⊗ₜ[A] algebraMap (MvPolynomial (Fin n) A) B (MvPolynomial.X j)) ^ p) ∧
      ∀ k : κ, F (wittTwoTeichmuller p κ k ⊗ₜ[A] (1 : B)) =
        (wittTwoTeichmuller p κ k ⊗ₜ[A] (1 : B)) ^ p := by
  have : CharP (κ ⊗[A] B) p :=
    charP_of_injective_algebraMap (algebraMap κ (κ ⊗[A] B)).injective p
  have := formallyEtale_tensorCoordinates (A := A) (W := WittTwo p κ) (B := B) (n := n)
  obtain ⟨F, hF, hFW, hFX⟩ := exists_coordinateFrobeniusLift (n := n) (wittTwoFrobenius p κ) p
    (Algebra.TensorProduct.map (wittTwoReductionAlgHom p κ h) (AlgHom.id A B)).toRingHom
    (wittTwo_tensor_surjective p κ h)
    (fun x y hx hy => wittTwo_tensor_mul_eq_zero p κ h x y hx hy)
    (fun w => wittTwo_tensor_frobenius p κ h w)
  have hW : ∀ w, F (w ⊗ₜ[A] (1 : B)) = wittTwoFrobenius p κ w ⊗ₜ[A] (1 : B) := fun w => hFW w
  refine ⟨F, hF, hW, fun j => ?_, fun k => ?_⟩
  · have := hFX j
    rw [tensorCoordinates_algebraMap_X] at this
    exact this
  · rw [hW, wittTwoFrobenius_teichmuller, Algebra.TensorProduct.tmul_pow, one_pow]

end WittTwoCoordinates

end MixedFujita
