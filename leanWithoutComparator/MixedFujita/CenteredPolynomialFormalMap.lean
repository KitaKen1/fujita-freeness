/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.EtaleRelativeJacobian
public import MixedFujita.CoordinateDivisorFormalMap
public import MixedFujita.ProjectiveChartThreshold
public import MixedFujita.PointBlowupExceptionalBaseChange

/-! Construct a centered formal map directly from the Taylor images of
actual polynomial coordinates. Its Jacobian is the Taylor image of the
actual relative Jacobian. Exceptional quotient identities transport to
the shifted leading-form restriction for this same formal map, without
requiring a second completion on the intermediate blow-up. -/

@[expose] public section
open MvPowerSeries
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type*} [Field K] {n : ℕ}

/-- Subtract the actual constant terms before substituting coordinates. -/
noncomputable def centeredPolynomialFormalMap
    (α : MvPolynomial (Fin n) K →ₐ[K] MvPowerSeries (Fin n) K) :
    MvPowerSeries (Fin n) K →ₐ[K] MvPowerSeries (Fin n) K :=
  substAlgHom (hasSubst_of_constantCoeff_zero (fun i =>
    show constantCoeff (α (MvPolynomial.X i) - C (constantCoeff (α (MvPolynomial.X i)))) = 0 by
      simp))

theorem centeredPolynomialFormalMap_X
    (α : MvPolynomial (Fin n) K →ₐ[K] MvPowerSeries (Fin n) K) (i : Fin n) :
    centeredPolynomialFormalMap α (X i) =
      α (MvPolynomial.X i) - C (constantCoeff (α (MvPolynomial.X i))) :=
  substAlgHom_X _ i

theorem centeredPolynomialFormalMap_normal
    (α : MvPolynomial (Fin n) K →ₐ[K] MvPowerSeries (Fin n) K)
    (k : Fin n) (v : MvPowerSeries (Fin n) K)
    (h : α (MvPolynomial.X k) = X k * v) :
    centeredPolynomialFormalMap α (X k) = X k * v := by
  rw [centeredPolynomialFormalMap_X, h]
  simp

theorem centeredPolynomialFormalMap_jacobian
    {R S : Type*} [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
    (β : R →ₐ[K] S) (x : MvPolynomial (Fin n) K →ₐ[K] R)
    (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale)
    (T : S →ₐ[K] MvPowerSeries (Fin n) K)
    (hT : ∀ i, T (y (MvPolynomial.X i)) = X i) :
    powerSeriesJacobian (centeredPolynomialFormalMap (T.comp (β.comp x))) =
      T.toRingHom.mapMatrix (etaleRelativeJacobian β x y hy) := by
  apply Matrix.ext
  intro i j
  change pderiv j (centeredPolynomialFormalMap (T.comp (β.comp x)) (X i)) =
    T (etaleCoordinateDerivation y hy j (β (x (MvPolynomial.X i))))
  rw [centeredPolynomialFormalMap_X, map_sub, pderiv_C, sub_zero,
    etaleCoordinateDerivation_taylor T y hy hT]
  rfl

theorem centeredPolynomialFormalMap_jacobian_det
    {R S : Type*} [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
    (β : R →ₐ[K] S) (x : MvPolynomial (Fin n) K →ₐ[K] R)
    (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale)
    (T : S →ₐ[K] MvPowerSeries (Fin n) K)
    (hT : ∀ i, T (y (MvPolynomial.X i)) = X i) :
    (powerSeriesJacobian (centeredPolynomialFormalMap (T.comp (β.comp x)))).det =
      T (etaleRelativeJacobian β x y hy).det := by
  rw [centeredPolynomialFormalMap_jacobian β x y hy T hT]
  exact (RingHom.map_det T.toRingHom _).symm

theorem centeredPolynomialFormalMap_divisor_shift
    (α : MvPolynomial (Fin n) K →ₐ[K] MvPowerSeries (Fin n) K)
    (k : Fin n) (g : MvPolynomial (Fin n) K) :
    powerSeriesDivisorMap (centeredPolynomialFormalMap α) k
        (chartShiftedForm k (fun i => constantCoeff (α (MvPolynomial.X i.val))) g) =
      MvPolynomial.aeval (fun i : Fin n => if i = k then 1 else
        powerSeriesDivisorRestriction k (α (MvPolynomial.X i))) g := by
  classical
  let ψ := powerSeriesDivisorMap (centeredPolynomialFormalMap α) k
  have hX (i : Fin n) :
      ψ (if h : i = k then (1 : MvPowerSeries {i : Fin n // i ≠ k} K)
        else C (constantCoeff (α (MvPolynomial.X i))) + X ⟨i, h⟩) =
      (if i = k then 1 else powerSeriesDivisorRestriction k (α (MvPolynomial.X i))) := by
    by_cases hi : i = k
    · simp only [hi, dite_true, ite_true, map_one]
    · simp only [dite_eq_right hi, ite_eq_right hi, map_add]
      dsimp only [ψ]
      rw [show (powerSeriesDivisorMap (centeredPolynomialFormalMap α) k)
          (C (constantCoeff (α (MvPolynomial.X i)))) = C (constantCoeff (α (MvPolynomial.X i))) from
        (powerSeriesDivisorMap (centeredPolynomialFormalMap α) k).commutes _,
        powerSeriesDivisorMap_X, centeredPolynomialFormalMap_X, map_sub,
        show powerSeriesDivisorRestriction k (C (constantCoeff (α (MvPolynomial.X i)))) =
          C (constantCoeff (α (MvPolynomial.X i))) from (powerSeriesDivisorRestriction k).commutes _]
      change C _ + (powerSeriesDivisorRestriction k (α (MvPolynomial.X i)) - C _) = _
      ring
  change ψ (MvPolynomial.aeval _ g) = _
  induction g using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f i hf => simp only [map_mul, MvPolynomial.aeval_X, hf, hX]

/-- An actual exceptional quotient identity gives the shifted-form
restriction for the directly constructed formal map. -/
theorem centeredPolynomialFormalMap_exceptional_restriction
    {R : Type*} [CommRing R] [Algebra K R]
    (τ : MvPolynomial (Fin n) K →ₐ[K] R) (T : R →ₐ[K] MvPowerSeries (Fin n) K)
    (k : Fin n) (v : MvPowerSeries (Fin n) K)
    (hnormal : T (τ (MvPolynomial.X k)) = X k * v)
    (z : R) (g : MvPolynomial (Fin n) K)
    (hres : Ideal.Quotient.mk (Ideal.span {τ (MvPolynomial.X k)}) z =
      pointBlowupExceptionalEvaluation τ.toRingHom k (projectiveDehomogenize K k g)) :
    powerSeriesDivisorRestriction k (T z) =
      powerSeriesDivisorMap (centeredPolynomialFormalMap (T.comp τ)) k
        (chartShiftedForm k (fun i => constantCoeff (T (τ (MvPolynomial.X i.val)))) g) := by
  classical
  let δ := powerSeriesDivisorRestriction (K := K) k
  let θ := δ.comp T
  have hkill : Ideal.span {τ (MvPolynomial.X k)} ≤ RingHom.ker θ.toRingHom := by
    rw [Ideal.span_le]
    rintro a rfl
    change δ (T (τ (MvPolynomial.X k))) = 0
    rw [hnormal, map_mul, powerSeriesDivisorRestriction_X_self, zero_mul]
  let q := Ideal.Quotient.lift _ θ.toRingHom hkill
  have hq := congrArg q hres
  rw [Ideal.Quotient.lift_mk] at hq
  have hshift := centeredPolynomialFormalMap_divisor_shift (T.comp τ) k g
  simp only [AlgHom.comp_apply] at hshift
  rw [hshift]
  change θ z = _
  change θ z = _ at hq
  rw [hq]
  have hX (i : Fin n) :
      q (pointBlowupExceptionalEvaluation τ.toRingHom k
        (projectiveDehomogenize K k (MvPolynomial.X i))) =
      (if i = k then 1 else δ (T (τ (MvPolynomial.X i)))) := by
    by_cases hi : i = k
    · subst i
      rw [projectiveDehomogenize_X_self, map_one, map_one, ite_eq_left rfl]
    · rw [show MvPolynomial.X i = MvPolynomial.X (⟨i, hi⟩ : {i : Fin n // i ≠ k}).val from rfl,
        projectiveDehomogenize_X_other, pointBlowupExceptionalEvaluation_X, ite_eq_right hi]
      rfl
  clear hres hq hshift
  induction g using MvPolynomial.induction_on with
  | C c =>
    rw [projectiveDehomogenize_C, pointBlowupExceptionalEvaluation_C, MvPolynomial.aeval_C]
    change (θ.comp τ) (algebraMap K (MvPolynomial (Fin n) K) c) = _
    exact (θ.comp τ).commutes c
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f i hf =>
    simp only [map_mul, MvPolynomial.aeval_X, hf, hX]
    rfl

end MixedFujita
