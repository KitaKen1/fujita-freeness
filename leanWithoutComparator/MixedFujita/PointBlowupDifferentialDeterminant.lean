/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.EtaleCoordinateDifferentials
public import MixedFujita.PrincipalExceptionalDVR
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! The actual differential determinant of point-blow-up coordinates.
The matrix calculation holds over any commutative ring. Its interpretation
in Kähler differentials explicitly requires that the chart differentials
form a basis; construction of that basis on the actual blow-up is separate. -/

@[expose] public section
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {A : Type*} [CommRing A] {n : ℕ}

noncomputable def pointBlowupDifferentialMatrix (z : Fin n → A) (k : Fin n) :
    Matrix (Fin n) (Fin n) A :=
  Matrix.updateCol (z k • (1 : Matrix (Fin n) (Fin n) A)) k (Function.update z k 1)

theorem pointBlowupDifferentialMatrix_det (z : Fin n → A) (k : Fin n) :
    (pointBlowupDifferentialMatrix z k).det = z k ^ (n - 1) := by
  classical
  let v := Function.update z k 1
  have hv : (fun j => ∑ i, v i • (1 : Matrix (Fin n) (Fin n) A) j i) = v := by
    funext j
    simp [Matrix.one_apply, smul_eq_mul]
  have hdet : (Matrix.updateCol (1 : Matrix (Fin n) (Fin n) A) k v).det = 1 := by
    rw [← hv, Matrix.det_updateCol_sum, Matrix.det_one]
    simp [v]
  rw [pointBlowupDifferentialMatrix, Matrix.det_updateCol_smul_left, hdet,
    Fintype.card_fin, mul_one]

variable {K : Type*} [Field K] [Algebra K A]

theorem pointBlowup_kaehler_determinant (z x : Fin n → A) (k : Fin n)
    (hx : ∀ i, x i = if i = k then z k else z i * z k)
    (b : Module.Basis (Fin n) A Ω[A⁄K])
    (hb : ∀ i, b i = KaehlerDifferential.D K A (z i)) :
    b.det (fun i => KaehlerDifferential.D K A (x i)) = z k ^ (n - 1) := by
  classical
  have hmatrix : b.toMatrix (fun i => KaehlerDifferential.D K A (x i)) =
      (pointBlowupDifferentialMatrix z k).transpose := by
    ext j i
    rw [Module.Basis.toMatrix_apply, hx]
    by_cases hi : i = k
    · subst i
      by_cases hj : j = k
      · subst j
        simp [← hb, pointBlowupDifferentialMatrix]
      · simp [← hb, pointBlowupDifferentialMatrix, Matrix.transpose_apply, hj, Ne.symm hj]
    · rw [ite_eq_right hi, Derivation.leibniz, map_add, map_smul, map_smul, ← hb i, ← hb k]
      simp [pointBlowupDifferentialMatrix, Matrix.transpose_apply, Matrix.updateCol_apply,
        hi, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> simp_all
  rw [Module.Basis.det_apply, hmatrix, Matrix.det_transpose, pointBlowupDifferentialMatrix_det]

theorem pointBlowup_kaehler_exceptional_order [IsDomain A] [IsNoetherianRing A]
    (z x : Fin n → A) (k : Fin n)
    (hx : ∀ i, x i = if i = k then z k else z i * z k)
    (b : Module.Basis (Fin n) A Ω[A⁄K])
    (hb : ∀ i, b i = KaehlerDifferential.D K A (z i))
    (p : Ideal A) [p.IsPrime] (hp : p = Ideal.span {z k}) (hz : z k ≠ 0) :
    localAdicOrder (Localization.AtPrime p)
      (algebraMap A (Localization.AtPrime p)
        (b.det (fun i => KaehlerDifferential.D K A (x i)))) = ((n - 1 : ℕ) : ℕ∞) := by
  apply principalPrime_localization_order p (z k) hp hz _ 1 (n - 1)
  · rw [pointBlowup_kaehler_determinant z x k hx b hb, mul_one]
  · exact Ideal.one_notMem p

theorem pointBlowup_kaehler_logDiscrepancy [IsDomain A] [IsNoetherianRing A]
    (z x : Fin n → A) (k : Fin n)
    (hx : ∀ i, x i = if i = k then z k else z i * z k)
    (b : Module.Basis (Fin n) A Ω[A⁄K])
    (hb : ∀ i, b i = KaehlerDifferential.D K A (z i))
    (p : Ideal A) [p.IsPrime] (hp : p = Ideal.span {z k}) (hz : z k ≠ 0) :
    1 + localAdicOrder (Localization.AtPrime p)
      (algebraMap A (Localization.AtPrime p)
        (b.det (fun i => KaehlerDifferential.D K A (x i)))) = (n : ℕ∞) := by
  rw [pointBlowup_kaehler_exceptional_order z x k hx b hb p hp hz]
  have hn : 1 + (n - 1) = n := by have := k.isLt; omega
  exact_mod_cast hn

end MixedFujita
