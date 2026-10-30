/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.JacobianValuationBound
public import MixedFujita.EtaleRelativeJacobian
public import Mathlib.RingTheory.Valuation.ExtendToLocalization
public import Mathlib.RingTheory.Localization.FractionRing

/-!
Formal test valuations as valuations of function fields. The weighted order of a power series
in finitely many variables over a field is a valuation with values in ℤᵐ⁰, and it extends to the
fraction field L of the power series ring. Let F be a field with two systems of étale
coordinates y and τ, every element of which is a quotient of polynomials in y, and φ : F → L a
ring homomorphism sending y(P) to the image of θ(P) for a K-algebra map θ from polynomials to power
series. The maps D_i = Σ_j φ(∂/∂y_j) ∂_iθ(y_j) from F to L agree with ∂_i ∘ θ on polynomials, lower
the valuation by at most w_i, and satisfy the chain rule in the coordinates τ. Hence the weighted
order of the Jacobian determinant of θ is at least v(det ∂y/∂τ) + Σ_a v(τ_a) - Σ_i w_i, the formal
analogue of the coordinate-sum inequality on smooth models, for an arbitrary formal test.
-/

@[expose] public section

namespace MixedFujita

open MvPowerSeries WithZero

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section WeightedValuation

open scoped Classical

variable {σ K : Type*} [Field K]

/-- The function f ↦ exp(-ord_w f), with 0 ↦ 0. -/
noncomputable def weightedValuationFun (w : σ → ℕ) (f : MvPowerSeries σ K) : ℤᵐ⁰ :=
  if f = 0 then 0 else exp (-((f.weightedOrder w).toNat : ℤ))

theorem weightedValuationFun_zero (w : σ → ℕ) : weightedValuationFun (K := K) w 0 = 0 :=
  ite_eq_left rfl

theorem weightedValuationFun_of_ne_zero (w : σ → ℕ) {f : MvPowerSeries σ K} (hf : f ≠ 0) :
    weightedValuationFun w f = exp (-((f.weightedOrder w).toNat : ℤ)) :=
  ite_eq_right hf

theorem weightedOrder_ne_top_of_ne_zero (w : σ → ℕ) {f : MvPowerSeries σ K} (hf : f ≠ 0) :
    f.weightedOrder w ≠ ⊤ := fun h => hf ((weightedOrder_eq_top_iff w).mp h)

/-- The weighted order as a valuation with values in ℤᵐ⁰: f ↦ exp(-ord_w f). -/
noncomputable def weightedValuation (w : σ → ℕ) : Valuation (MvPowerSeries σ K) ℤᵐ⁰ where
  toFun := weightedValuationFun w
  map_zero' := weightedValuationFun_zero w
  map_one' := by
    rw [weightedValuationFun_of_ne_zero w one_ne_zero, weightedOrder_one]
    rfl
  map_mul' f g := by
    by_cases hf : f = 0
    · rw [hf, zero_mul, weightedValuationFun_zero, zero_mul]
    by_cases hg : g = 0
    · rw [hg, mul_zero, weightedValuationFun_zero, mul_zero]
    rw [weightedValuationFun_of_ne_zero w (mul_ne_zero hf hg), weightedValuationFun_of_ne_zero w hf,
      weightedValuationFun_of_ne_zero w hg, ← exp_add, weightedOrder_mul,
      ENat.toNat_add (weightedOrder_ne_top_of_ne_zero w hf) (weightedOrder_ne_top_of_ne_zero w hg)]
    push_cast
    ring_nf
  map_add_le_max' f g := by
    by_cases hfg : f + g = 0
    · rw [hfg, weightedValuationFun_zero]
      exact zero_le
    by_cases hf : f = 0
    · rw [hf, zero_add]
      exact le_max_right _ _
    by_cases hg : g = 0
    · rw [hg, add_zero]
      exact le_max_left _ _
    rw [weightedValuationFun_of_ne_zero w hfg, weightedValuationFun_of_ne_zero w hf,
      weightedValuationFun_of_ne_zero w hg]
    have hmin := min_weightedOrder_le_add (w := w) (f := f) (g := g)
    have h3 := weightedOrder_ne_top_of_ne_zero w hfg
    rcases le_total (f.weightedOrder w) (g.weightedOrder w) with h | h
    · rw [min_eq_left h] at hmin
      apply le_max_of_le_left
      rw [exp_le_exp, neg_le_neg_iff, Nat.cast_le]
      exact ENat.toNat_le_toNat hmin h3
    · rw [min_eq_right h] at hmin
      apply le_max_of_le_right
      rw [exp_le_exp, neg_le_neg_iff, Nat.cast_le]
      exact ENat.toNat_le_toNat hmin h3

theorem weightedValuation_of_ne_zero (w : σ → ℕ) {f : MvPowerSeries σ K} (hf : f ≠ 0) :
    weightedValuation w f = exp (-((f.weightedOrder w).toNat : ℤ)) :=
  weightedValuationFun_of_ne_zero w hf

theorem weightedValuation_eq_zero_iff (w : σ → ℕ) {f : MvPowerSeries σ K} :
    weightedValuation w f = 0 ↔ f = 0 := by
  constructor
  · intro h
    by_contra hf
    rw [weightedValuation_of_ne_zero w hf] at h
    exact exp_ne_zero h
  · rintro rfl
    exact map_zero _

/-- The valuation reverses the weighted order. -/
theorem weightedValuation_le_iff (w : σ → ℕ) (f g : MvPowerSeries σ K) :
    weightedValuation w f ≤ weightedValuation w g ↔ g.weightedOrder w ≤ f.weightedOrder w := by
  by_cases hf : f = 0
  · subst hf
    simp only [map_zero, zero_le, weightedOrder_zero, le_top]
  by_cases hg : g = 0
  · subst hg
    rw [map_zero, weightedOrder_zero]
    simp only [le_zero_iff, weightedValuation_eq_zero_iff, hf, top_le_iff,
      weightedOrder_eq_top_iff]
  rw [weightedValuation_of_ne_zero w hf, weightedValuation_of_ne_zero w hg, exp_le_exp,
    neg_le_neg_iff]
  have e1 := (ne_zero_iff_weightedOrder_finite w).mp hf
  have e2 := (ne_zero_iff_weightedOrder_finite w).mp hg
  conv_rhs => rw [← e1, ← e2]
  constructor <;> intro h <;> exact_mod_cast h

/-- A partial derivative lowers the valuation of the weighted order by at most exp(w_i). -/
theorem weightedValuation_pderiv_le [DecidableEq σ] (w : σ → ℕ) (i : σ) (H : MvPowerSeries σ K) :
    weightedValuation w (pderiv i H) ≤ exp (w i : ℤ) * weightedValuation w H := by
  by_cases hH : H = 0
  · subst hH
    simp only [map_zero, mul_zero, le_refl]
  by_cases hd : pderiv i H = 0
  · rw [hd, map_zero]
    exact zero_le
  rw [weightedValuation_of_ne_zero w hH, weightedValuation_of_ne_zero w hd, ← exp_add, exp_le_exp]
  have hb := weightedOrder_le_pderiv_add w i H
  have e1 := (ne_zero_iff_weightedOrder_finite w).mp hH
  have e2 := (ne_zero_iff_weightedOrder_finite w).mp hd
  rw [← e1, ← e2, ← Nat.cast_add, Nat.cast_le] at hb
  omega

theorem weightedValuation_nonZeroDivisors_le (w : σ → ℕ) :
    nonZeroDivisors (MvPowerSeries σ K) ≤ (weightedValuation (K := K) w).supp.primeCompl := by
  intro s hs
  change s ∉ (weightedValuation w).supp
  rw [Valuation.mem_supp_iff, weightedValuation_eq_zero_iff]
  exact nonZeroDivisors.ne_zero hs

/-- The weighted valuation on the fraction field of the power series ring. -/
noncomputable def weightedFieldValuation (w : σ → ℕ) :
    Valuation (FractionRing (MvPowerSeries σ K)) ℤᵐ⁰ :=
  (weightedValuation (σ := σ) (K := K) w).extendToLocalization
    (S := nonZeroDivisors (MvPowerSeries σ K)) (weightedValuation_nonZeroDivisors_le w)
    (FractionRing (MvPowerSeries σ K))

theorem weightedFieldValuation_algebraMap (w : σ → ℕ) (f : MvPowerSeries σ K) :
    weightedFieldValuation w (algebraMap _ (FractionRing (MvPowerSeries σ K)) f) =
      weightedValuation w f :=
  Valuation.extendToLocalization_apply_map_apply (weightedValuation (σ := σ) (K := K) w)
    (weightedValuation_nonZeroDivisors_le w) (FractionRing (MvPowerSeries σ K)) f

end WeightedValuation

section Derivations

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {m : ℕ}

/-- The derivation D_i = Σ_j φ(∂/∂y_j) ∂_iθ(y_j) from F to the fraction field of power series. -/
noncomputable def formalTestFieldDerivation (y : MvPolynomial (Fin m) K →ₐ[K] F)
    (hy : y.toRingHom.FormallyEtale) (θ : MvPolynomial (Fin m) K →ₐ[K] MvPowerSeries (Fin m) K)
    (φ : F →+* FractionRing (MvPowerSeries (Fin m) K)) (i : Fin m) (f : F) : FractionRing (MvPowerSeries (Fin m) K) :=
  ∑ j, φ (etaleCoordinateDerivation y hy j f) *
    algebraMap _ (FractionRing (MvPowerSeries (Fin m) K)) (MvPowerSeries.pderiv i (θ (MvPolynomial.X j)))

variable (y : MvPolynomial (Fin m) K →ₐ[K] F) (hy : y.toRingHom.FormallyEtale)
  (θ : MvPolynomial (Fin m) K →ₐ[K] MvPowerSeries (Fin m) K) (φ : F →+* FractionRing (MvPowerSeries (Fin m) K))

theorem formalTestFieldDerivation_add (i : Fin m) (f g : F) :
    formalTestFieldDerivation y hy θ φ i (f + g) =
      formalTestFieldDerivation y hy θ φ i f + formalTestFieldDerivation y hy θ φ i g := by
  simp only [formalTestFieldDerivation, map_add, add_mul, Finset.sum_add_distrib]

theorem formalTestFieldDerivation_mul (i : Fin m) (f g : F) :
    formalTestFieldDerivation y hy θ φ i (f * g) =
      φ f * formalTestFieldDerivation y hy θ φ i g + φ g * formalTestFieldDerivation y hy θ φ i f := by
  simp only [formalTestFieldDerivation, Derivation.leibniz, smul_eq_mul, map_add, map_mul,
    add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

theorem formalTestFieldDerivation_algebraMap (i : Fin m) (c : K) :
    formalTestFieldDerivation y hy θ φ i (algebraMap K F c) = 0 := by
  simp only [formalTestFieldDerivation, Derivation.map_algebraMap, map_zero, zero_mul,
    Finset.sum_const_zero]

theorem formalTestFieldDerivation_coordinate (i j : Fin m) :
    formalTestFieldDerivation y hy θ φ i (y (MvPolynomial.X j)) =
      algebraMap _ (FractionRing (MvPowerSeries (Fin m) K)) (MvPowerSeries.pderiv i (θ (MvPolynomial.X j))) := by
  simp only [formalTestFieldDerivation, etaleCoordinateDerivation_coordinate]
  rw [Finset.sum_eq_single j]
  · rw [ite_eq_left rfl, map_one, one_mul]
  · intro b _ hb
    rw [ite_eq_right (Ne.symm hb), map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- On polynomials the derivation is ∂_i ∘ θ. -/
theorem formalTestFieldDerivation_polynomial
    (hφ : ∀ P, φ (y P) = algebraMap _ (FractionRing (MvPowerSeries (Fin m) K)) (θ P)) (i : Fin m) (P : MvPolynomial (Fin m) K) :
    formalTestFieldDerivation y hy θ φ i (y P) =
      algebraMap _ (FractionRing (MvPowerSeries (Fin m) K)) (MvPowerSeries.pderiv i (θ P)) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.algHom_C, MvPolynomial.algHom_C, formalTestFieldDerivation_algebraMap]
    rw [Derivation.map_algebraMap, map_zero]
  | add P Q hP hQ =>
    rw [map_add, formalTestFieldDerivation_add, hP, hQ, map_add, map_add, map_add]
  | mul_X P j hP =>
    rw [map_mul, formalTestFieldDerivation_mul, hP, formalTestFieldDerivation_coordinate,
      hφ, hφ, map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul]

/-- Chain rule in a second system of étale coordinates τ. -/
theorem formalTestFieldDerivation_chainRule (τ : MvPolynomial (Fin m) K →ₐ[K] F)
    (hτ : τ.toRingHom.FormallyEtale) (i : Fin m) (f : F) :
    formalTestFieldDerivation y hy θ φ i f =
      ∑ a, φ (etaleCoordinateDerivation τ hτ a f) *
        formalTestFieldDerivation y hy θ φ i (τ (MvPolynomial.X a)) := by
  have hch : ∀ j, etaleCoordinateDerivation y hy j f =
      ∑ a, etaleCoordinateDerivation τ hτ a f *
        etaleCoordinateDerivation y hy j (τ (MvPolynomial.X a)) := fun j =>
    etaleCoordinateDerivation_chainRule (AlgHom.id K F) τ hτ y hy j f
  simp only [formalTestFieldDerivation, hch, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Derivations

section Bounds

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {m : ℕ}

variable (y : MvPolynomial (Fin m) K →ₐ[K] F) (hy : y.toRingHom.FormallyEtale)
  (θ : MvPolynomial (Fin m) K →ₐ[K] MvPowerSeries (Fin m) K) (φ : F →+* FractionRing (MvPowerSeries (Fin m) K))
  (hφ : ∀ P, φ (y P) = algebraMap _ (FractionRing (MvPowerSeries (Fin m) K)) (θ P))
  (hfrac : ∀ f : F, ∃ P Q : MvPolynomial (Fin m) K, y Q ≠ 0 ∧ f * y Q = y P)

include hφ hfrac in
/-- The derivation lowers the field valuation by at most exp(w_i). -/
theorem weightedFieldValuation_formalTestFieldDerivation_le (w : Fin m → ℕ) (i : Fin m) (f : F) :
    weightedFieldValuation w (formalTestFieldDerivation y hy θ φ i f) ≤
      exp (w i : ℤ) * weightedFieldValuation w (φ f) := by
  obtain ⟨P, Q, hQ, hfQ⟩ := hfrac f
  set v := weightedFieldValuation (K := K) w
  have hφQ : φ (y Q) ≠ 0 := (map_ne_zero φ).mpr hQ
  have hvQ : v (φ (y Q)) ≠ 0 := (Valuation.ne_zero_iff v).mpr hφQ
  have hleib := formalTestFieldDerivation_mul y hy θ φ i f (y Q)
  rw [hfQ] at hleib
  have hD : φ (y Q) * formalTestFieldDerivation y hy θ φ i f =
      formalTestFieldDerivation y hy θ φ i (y P) - φ f * formalTestFieldDerivation y hy θ φ i (y Q) := by
    rw [hleib]
    ring
  have hP := formalTestFieldDerivation_polynomial y hy θ φ hφ i P
  have hQ' := formalTestFieldDerivation_polynomial y hy θ φ hφ i Q
  have hbP : v (formalTestFieldDerivation y hy θ φ i (y P)) ≤
      exp (w i : ℤ) * (v (φ f) * v (φ (y Q))) := by
    rw [hP, weightedFieldValuation_algebraMap, ← map_mul, ← map_mul, hfQ, hφ,
      weightedFieldValuation_algebraMap]
    exact weightedValuation_pderiv_le w i (θ P)
  have hbQ : v (φ f * formalTestFieldDerivation y hy θ φ i (y Q)) ≤
      exp (w i : ℤ) * (v (φ f) * v (φ (y Q))) := by
    rw [map_mul, hQ', weightedFieldValuation_algebraMap, hφ, weightedFieldValuation_algebraMap]
    calc v (φ f) * weightedValuation w (MvPowerSeries.pderiv i (θ Q))
        ≤ v (φ f) * (exp (w i : ℤ) * weightedValuation w (θ Q)) :=
          mul_le_mul_right (weightedValuation_pderiv_le w i (θ Q)) _
      _ = exp (w i : ℤ) * (v (φ f) * weightedValuation w (θ Q)) := by ac_rfl
  have hsum : v (φ (y Q) * formalTestFieldDerivation y hy θ φ i f) ≤
      exp (w i : ℤ) * (v (φ f) * v (φ (y Q))) := by
    rw [hD]
    exact (Valuation.map_sub v _ _).trans (max_le hbP hbQ)
  rw [map_mul] at hsum
  have h2 : v (φ (y Q)) * v (formalTestFieldDerivation y hy θ φ i f) ≤
      v (φ (y Q)) * (exp (w i : ℤ) * v (φ f)) := by
    calc v (φ (y Q)) * v (formalTestFieldDerivation y hy θ φ i f)
        ≤ exp (w i : ℤ) * (v (φ f) * v (φ (y Q))) := hsum
      _ = v (φ (y Q)) * (exp (w i : ℤ) * v (φ f)) := by ac_rfl
  calc v (formalTestFieldDerivation y hy θ φ i f)
      = (v (φ (y Q)))⁻¹ * (v (φ (y Q)) * v (formalTestFieldDerivation y hy θ φ i f)) := by
        rw [inv_mul_cancel_left₀ hvQ]
    _ ≤ (v (φ (y Q)))⁻¹ * (v (φ (y Q)) * (exp (w i : ℤ) * v (φ f))) := mul_le_mul_right h2 _
    _ = exp (w i : ℤ) * v (φ f) := by rw [inv_mul_cancel_left₀ hvQ]

theorem prod_exp_eq_exp_sum {ι : Type*} (s : Finset ι) (a : ι → ℤ) :
    ∏ i ∈ s, exp (a i) = exp (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Finset.sum_empty, exp_zero]
  | insert b s hb ih => rw [Finset.prod_insert hb, Finset.sum_insert hb, ih, exp_add]

include hφ hfrac in
/-- The determinant of the derivations of the τ-coordinates loses at most exp(Σ w). -/
theorem weightedFieldValuation_det_formalTestFieldDerivation_le (w : Fin m → ℕ)
    (τ : MvPolynomial (Fin m) K →ₐ[K] F) :
    weightedFieldValuation w (Matrix.of fun i a =>
        formalTestFieldDerivation y hy θ φ i (τ (MvPolynomial.X a))).det ≤
      exp ((∑ i, w i : ℕ) : ℤ) * ∏ a, weightedFieldValuation w (φ (τ (MvPolynomial.X a))) := by
  set v := weightedFieldValuation (K := K) w
  rw [Matrix.det_apply]
  apply Valuation.map_sum_le
  intro p _
  have hsign : ∀ x : FractionRing (MvPowerSeries (Fin m) K), v (Equiv.Perm.sign p • x) = v x := by
    intro x
    rcases Int.units_eq_one_or (Equiv.Perm.sign p) with h | h
    · rw [h, one_smul]
    · rw [h, Units.neg_smul, one_smul, Valuation.map_neg]
  rw [hsign, map_prod]
  calc ∏ i, v ((Matrix.of fun i a =>
          formalTestFieldDerivation y hy θ φ i (τ (MvPolynomial.X a))) (p i) i)
      ≤ ∏ i, (exp (w (p i) : ℤ) * v (φ (τ (MvPolynomial.X i)))) := by
        apply Finset.prod_le_prod
        intro i _
        exact weightedFieldValuation_formalTestFieldDerivation_le y hy θ φ hφ hfrac w (p i) _
    _ = exp ((∑ i, w i : ℕ) : ℤ) * ∏ a, v (φ (τ (MvPolynomial.X a))) := by
        rw [Finset.prod_mul_distrib, prod_exp_eq_exp_sum]
        congr 2
        push_cast
        exact Equiv.sum_comp p (fun i => (w i : ℤ))

include hy hφ hfrac in
/-- The formal Jacobian inequality: the weighted order of det(∂_i θ(y_j)) is at least
v(det ∂y/∂τ) + Σ_a v(τ_a) - Σ_i w_i, in the multiplicative form of the valuation. -/
theorem weightedFieldValuation_jacobian_le (w : Fin m → ℕ) (τ : MvPolynomial (Fin m) K →ₐ[K] F)
    (hτ : τ.toRingHom.FormallyEtale) :
    weightedFieldValuation w (algebraMap _ (FractionRing (MvPowerSeries (Fin m) K))
        (Matrix.of fun i j => MvPowerSeries.pderiv i (θ (MvPolynomial.X j))).det) ≤
      exp ((∑ i, w i : ℕ) : ℤ) * (∏ a, weightedFieldValuation w (φ (τ (MvPolynomial.X a)))) *
        weightedFieldValuation w (φ (etaleRelativeJacobian (AlgHom.id K F) y τ hτ).det) := by
  set v := weightedFieldValuation (K := K) w
  have hmat : (algebraMap (MvPowerSeries (Fin m) K) (FractionRing (MvPowerSeries (Fin m) K))).mapMatrix
      (Matrix.of fun i j => MvPowerSeries.pderiv i (θ (MvPolynomial.X j))) =
      (Matrix.of fun i a => formalTestFieldDerivation y hy θ φ i (τ (MvPolynomial.X a))) *
        (φ.mapMatrix (etaleRelativeJacobian (AlgHom.id K F) y τ hτ)).transpose := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply,
      ← formalTestFieldDerivation_coordinate y hy θ φ i j,
      formalTestFieldDerivation_chainRule y hy θ φ τ hτ i]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    simp only [etaleRelativeJacobian, Matrix.of_apply, AlgHom.id_apply]
    ring
  have hdet : algebraMap (MvPowerSeries (Fin m) K) (FractionRing (MvPowerSeries (Fin m) K))
      (Matrix.of fun i j => MvPowerSeries.pderiv i (θ (MvPolynomial.X j))).det =
      (Matrix.of fun i a => formalTestFieldDerivation y hy θ φ i (τ (MvPolynomial.X a))).det *
        φ (etaleRelativeJacobian (AlgHom.id K F) y τ hτ).det := by
    rw [RingHom.map_det, hmat, Matrix.det_mul, Matrix.det_transpose, RingHom.map_det]
  rw [hdet, map_mul]
  exact mul_le_mul_left
    (weightedFieldValuation_det_formalTestFieldDerivation_le y hy θ φ hφ hfrac w τ) _

end Bounds

section ShiftedTest

variable {K : Type*} [Field K] {m : ℕ}

/-- The polynomial map of a formal test at the point p: P ↦ ψ(P(p + X)). -/
noncomputable def shiftedFormalTestMap (ψ : MvPowerSeries (Fin m) K →ₐ[K] MvPowerSeries (Fin m) K)
    (p : Fin m → K) : MvPolynomial (Fin m) K →ₐ[K] MvPowerSeries (Fin m) K :=
  MvPolynomial.aeval fun j => algebraMap K (MvPowerSeries (Fin m) K) (p j) + ψ (MvPowerSeries.X j)

theorem shiftedFormalTestMap_X (ψ : MvPowerSeries (Fin m) K →ₐ[K] MvPowerSeries (Fin m) K)
    (p : Fin m → K) (j : Fin m) :
    shiftedFormalTestMap ψ p (MvPolynomial.X j) =
      algebraMap K (MvPowerSeries (Fin m) K) (p j) + ψ (MvPowerSeries.X j) :=
  MvPolynomial.aeval_X _ j

/-- The Jacobian of the shifted test is the transposed Jacobian of the formal test. -/
theorem shiftedFormalTestMap_jacobian_det
    (ψ : MvPowerSeries (Fin m) K →ₐ[K] MvPowerSeries (Fin m) K) (p : Fin m → K) :
    (Matrix.of fun i j => MvPowerSeries.pderiv i (shiftedFormalTestMap ψ p (MvPolynomial.X j))).det =
      (powerSeriesJacobian ψ).det := by
  rw [← Matrix.det_transpose (powerSeriesJacobian ψ)]
  congr 1
  ext i j
  rw [Matrix.of_apply, Matrix.transpose_apply, shiftedFormalTestMap_X, map_add,
    Derivation.map_algebraMap, zero_add]
  rfl

end ShiftedTest

end MixedFujita
