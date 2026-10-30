/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.JacobianCoordinateChange
public import Mathlib.RingTheory.MvPowerSeries.Rename

/-! Restrict a formal map to a coordinate divisor. Tangent derivatives
commute with restriction. If the normal coordinate pulls back as X_k v,
the restricted full Jacobian is v times the divisor-map Jacobian. These
identities work in every dimension and form the local adjunction step. -/

@[expose] public section
open MvPowerSeries
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {σ K : Type*} [Field K]

/-- Set the chosen normal variable to zero and retain the tangent variables. -/
noncomputable def powerSeriesDivisorRestriction (k : σ) :
    MvPowerSeries σ K →ₐ[K] MvPowerSeries {i : σ // i ≠ k} K :=
  killCompl (.subtype (· ≠ k))

theorem powerSeriesDivisorRestriction_X_self (k : σ) :
    powerSeriesDivisorRestriction (K := K) k (X k) = 0 := by
  apply killCompl_X_eq_zero
  rintro ⟨i, hi⟩
  exact i.property hi

theorem powerSeriesDivisorRestriction_X (k : σ) (i : {i : σ // i ≠ k}) :
    powerSeriesDivisorRestriction (K := K) k (X i.val) = X i :=
  killCompl_X (e := .subtype (· ≠ k)) i

theorem powerSeriesDivisorRestriction_rename (k : σ)
    (f : MvPowerSeries {i : σ // i ≠ k} K) :
    powerSeriesDivisorRestriction k (rename (Function.Embedding.subtype (· ≠ k)) f) = f :=
  killCompl_rename_app (e := .subtype (· ≠ k)) f

theorem powerSeriesDivisorRestriction_pderiv (k : σ) (i : {i : σ // i ≠ k})
    (f : MvPowerSeries σ K) :
    powerSeriesDivisorRestriction k (pderiv i.val f) =
      pderiv i (powerSeriesDivisorRestriction k f) := by
  classical
  ext d
  simp only [powerSeriesDivisorRestriction, coeff_killCompl, coeff_pderiv,
    Finsupp.embDomain_apply_self, Finsupp.embDomain_add, Finsupp.embDomain_single]
  rw [show Finsupp.embDomain (Function.Embedding.subtype (· ≠ k)) d i.val = d i from
    Finsupp.embDomain_apply_self _ _ i]
  rfl

/-- Tangent part of an actual formal map after restriction to the divisor. -/
noncomputable def powerSeriesDivisorMap
    (ψ : MvPowerSeries σ K →ₐ[K] MvPowerSeries σ K) (k : σ) :
    MvPowerSeries {i : σ // i ≠ k} K →ₐ[K] MvPowerSeries {i : σ // i ≠ k} K :=
  (powerSeriesDivisorRestriction k).comp (ψ.comp (rename (Function.Embedding.subtype (· ≠ k))))

theorem powerSeriesDivisorMap_X
    (ψ : MvPowerSeries σ K →ₐ[K] MvPowerSeries σ K) (k : σ) (i : {i : σ // i ≠ k}) :
    powerSeriesDivisorMap ψ k (X i) = powerSeriesDivisorRestriction k (ψ (X i.val)) := by
  simp only [powerSeriesDivisorMap, AlgHom.comp_apply, rename_X]
  rfl

variable [Fintype σ] [DecidableEq σ]

theorem powerSeriesDivisorMap_jacobian
    (ψ : MvPowerSeries σ K →ₐ[K] MvPowerSeries σ K) (k : σ)
    (i j : {i : σ // i ≠ k}) :
    powerSeriesJacobian (powerSeriesDivisorMap ψ k) i j =
      powerSeriesDivisorRestriction k (powerSeriesJacobian ψ i.val j.val) := by
  change pderiv j (powerSeriesDivisorMap ψ k (X i)) =
    powerSeriesDivisorRestriction k (pderiv j.val (ψ (X i.val)))
  rw [powerSeriesDivisorMap_X, powerSeriesDivisorRestriction_pderiv]

/-- Expansion along a row supported on its diagonal; the two permutation
signs cancel because the same coordinate is removed from rows and columns. -/
theorem matrix_det_of_single_coordinate_row {R : Type*} [CommRing R]
    (A : Matrix σ σ R) (k : σ) (hrow : ∀ j, j ≠ k → A k j = 0) :
    A.det = A k k * (A.submatrix (Subtype.val : {i : σ // i ≠ k} → σ) Subtype.val).det := by
  let e : {i : σ // i ≠ k} ⊕ PUnit.{1} ≃ σ := Equiv.subtypeNeSumPUnit k
  have hM : A.submatrix e e = Matrix.fromBlocks
      (A.submatrix (Subtype.val : {i : σ // i ≠ k} → σ) Subtype.val)
      (Matrix.of fun (i : {i : σ // i ≠ k}) (_ : PUnit.{1}) => A i.val k) 0
      (Matrix.of fun (_ _ : PUnit.{1}) => A k k) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rfl
    · rfl
    · change A k j.val = 0
      exact hrow j.val j.property
    · rfl
  rw [← Matrix.det_submatrix_equiv_self e A, hM, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_unique (Matrix.of fun (_ _ : PUnit.{1}) => A k k)]
  exact mul_comm _ _

theorem powerSeriesDivisorRestriction_jacobian_det
    (ψ : MvPowerSeries σ K →ₐ[K] MvPowerSeries σ K) (k : σ)
    (v : MvPowerSeries σ K) (hnormal : ψ (X k) = X k * v) :
    powerSeriesDivisorRestriction k (powerSeriesJacobian ψ).det =
      powerSeriesDivisorRestriction k v * (powerSeriesJacobian (powerSeriesDivisorMap ψ k)).det := by
  let δ := powerSeriesDivisorRestriction (K := K) k
  let A := δ.toRingHom.mapMatrix (powerSeriesJacobian ψ)
  have hδ : δ (X k) = 0 := powerSeriesDivisorRestriction_X_self k
  have hrow (j : σ) : A k j = if j = k then δ v else 0 := by
    change δ (pderiv j (ψ (X k))) = _
    rw [hnormal, (pderiv j).leibniz]
    simp only [smul_eq_mul, map_add, map_mul, hδ,
      zero_mul, zero_add, pderiv_X, Pi.single_apply]
    by_cases hj : j = k
    · simp [hj]
    · simp [hj, Ne.symm hj]
  have hminor : A.submatrix (Subtype.val : {i : σ // i ≠ k} → σ) Subtype.val =
      powerSeriesJacobian (powerSeriesDivisorMap ψ k) := by
    apply Matrix.ext
    intro i j
    exact (powerSeriesDivisorMap_jacobian ψ k i j).symm
  change δ.toRingHom (powerSeriesJacobian ψ).det = _
  rw [RingHom.map_det]
  change A.det = _
  rw [matrix_det_of_single_coordinate_row A k (fun j hj => by rw [hrow j, ite_eq_right hj]),
    hminor, hrow k, ite_eq_left rfl]

end MixedFujita
