/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCMonomialDivisorOrders

/-! A regular quotient of two SNC coordinate products has the difference
of their exponents. Single-coordinate weighted orders first force every
selected exponent difference to be nonnegative. Cancelling the actual
nonzero coordinate product constructs the quotient unit. If the normal
exponents agree, restriction is nonzero and each tangent order is exactly
the coefficient difference. This avoids constructing a global divisor
for an intermediate Jacobian. -/

@[expose] public section
open MvPowerSeries
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {σ K : Type*} [Field K] [DecidableEq σ] {r : ℕ}

theorem weightedOrder_selected_coordinate_single
    (u : (MvPowerSeries σ K)ˣ) (χ : Fin r → Option σ) (m : Fin r → ℕ)
    (hinj : ∀ i j a, χ i = some a → χ j = some a → i = j)
    (t : Fin r) (l : σ) (ht : χ t = some l) :
    ((u : MvPowerSeries σ K) * ∏ i, ((χ i).elim 1 X) ^ m i).weightedOrder
      (Pi.single l 1) = (m t : ℕ∞) := by
  classical
  rw [weightedOrder_selected_coordinate_unit_product]
  congr 1
  rw [Finset.sum_eq_single t]
  · simp [ht]
  · intro i hi hit
    cases hχ : χ i with
    | none => simp [hχ]
    | some a =>
      have hal : a ≠ l := fun hal => hit (hinj i t l (by simpa only [hal] using hχ) ht)
      simp [hχ, Pi.single_apply, hal]
  · exact fun ht' => (ht' (Finset.mem_univ t)).elim

theorem selected_coordinate_regular_quotient_exponent_le
    (u v : (MvPowerSeries σ K)ˣ) (χ : Fin r → Option σ) (d b : Fin r → ℕ)
    (hinj : ∀ i j a, χ i = some a → χ j = some a → i = j)
    (N : ℕ) (J : MvPowerSeries σ K)
    (h : (u : MvPowerSeries σ K) * ∏ i, ((χ i).elim 1 X) ^ d i =
      ((v : MvPowerSeries σ K) * ∏ i, ((χ i).elim 1 X) ^ b i) ^ N * J)
    (t : Fin r) (l : σ) (ht : χ t = some l) : N * b t ≤ d t := by
  have hd := weightedOrder_selected_coordinate_single u χ d hinj t l ht
  have hb := weightedOrder_selected_coordinate_single v χ b hinj t l ht
  rw [h, weightedOrder_mul] at hd
  have hle := le_weightedOrder_pow (w := Pi.single l 1)
    (f := (v : MvPowerSeries σ K) * ∏ i, ((χ i).elim 1 X) ^ b i) N
  rw [hb, nsmul_eq_mul] at hle
  have hle' : ((N * b t : ℕ) : ℕ∞) ≤ (d t : ℕ∞) := by
    rw [Nat.cast_mul]
    exact hle.trans ((le_add_right le_rfl).trans_eq hd)
  exact_mod_cast hle'

theorem selected_coordinate_regular_quotient_unit_product
    (u v : (MvPowerSeries σ K)ˣ) (χ : Fin r → Option σ) (d b : Fin r → ℕ)
    (hinj : ∀ i j a, χ i = some a → χ j = some a → i = j)
    (N : ℕ) (J : MvPowerSeries σ K)
    (h : (u : MvPowerSeries σ K) * ∏ i, ((χ i).elim 1 X) ^ d i =
      ((v : MvPowerSeries σ K) * ∏ i, ((χ i).elim 1 X) ^ b i) ^ N * J) :
    ∃ w : (MvPowerSeries σ K)ˣ,
      J = (w : MvPowerSeries σ K) *
        ∏ i, ((χ i).elim 1 X) ^ (d i - N * b i) := by
  classical
  let P := ∏ i, ((χ i).elim (1 : MvPowerSeries σ K) X) ^ b i
  let Q := ∏ i, ((χ i).elim (1 : MvPowerSeries σ K) X) ^ (d i - N * b i)
  have hP : P ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    cases hχ : χ i with
    | none => simp [hχ]
    | some a =>
      have ha : (X a : MvPowerSeries σ K) ≠ 0 := by
        intro h0
        have hc := congrArg (coeff (Finsupp.single a 1)) h0
        simpa using hc
      simpa only [hχ, Option.elim_some] using pow_ne_zero (b i) ha
  have hprod : (∏ i, ((χ i).elim (1 : MvPowerSeries σ K) X) ^ d i) = P ^ N * Q := by
    dsimp only [P, Q]
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    cases hχ : χ i with
    | none => simp [hχ]
    | some a =>
      have hle := selected_coordinate_regular_quotient_exponent_le u v χ d b hinj N J h i a hχ
      simp only [hχ, Option.elim_some, ← pow_mul, ← pow_add]
      congr 1
      rw [Nat.mul_comm (b i) N]
      omega
  have hcancel : (u : MvPowerSeries σ K) * Q = (v : MvPowerSeries σ K) ^ N * J := by
    apply mul_left_cancel₀ (pow_ne_zero N hP)
    calc
      P ^ N * ((u : MvPowerSeries σ K) * Q) =
          (u : MvPowerSeries σ K) * ∏ i, ((χ i).elim 1 X) ^ d i := by rw [hprod]; ring
      _ = _ := h
      _ = P ^ N * ((v : MvPowerSeries σ K) ^ N * J) := by dsimp only [P]; rw [mul_pow]; ring
  refine ⟨u * (v ^ N)⁻¹, ?_⟩
  change J = ((u : MvPowerSeries σ K) * ((v ^ N)⁻¹ : (MvPowerSeries σ K)ˣ)) * Q
  calc
    J = (((v ^ N)⁻¹ : (MvPowerSeries σ K)ˣ) : MvPowerSeries σ K) *
        ((v : MvPowerSeries σ K) ^ N * J) := by
          simp only [← mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul,
            inv_mul_cancel, Units.val_one, one_mul]
    _ = _ := by rw [← hcancel]; ring

theorem selected_coordinate_regular_quotient_restriction
    (u v : (MvPowerSeries σ K)ˣ) (χ : Fin r → Option σ) (d b : Fin r → ℕ)
    (hinj : ∀ i j a, χ i = some a → χ j = some a → i = j)
    (N : ℕ) (J : MvPowerSeries σ K)
    (h : (u : MvPowerSeries σ K) * ∏ i, ((χ i).elim 1 X) ^ d i =
      ((v : MvPowerSeries σ K) * ∏ i, ((χ i).elim 1 X) ^ b i) ^ N * J)
    (e : Fin r) (k : σ) (he : χ e = some k) (heq : d e = N * b e) :
    powerSeriesDivisorRestriction k J ≠ 0 ∧
      ∀ (t : Fin r) (l : σ) (hlk : l ≠ k), χ t = some l →
        (powerSeriesDivisorRestriction k J).weightedOrder
          (Pi.single (⟨l, hlk⟩ : {i : σ // i ≠ k}) 1) = ((d t - N * b t : ℕ) : ℕ∞) := by
  obtain ⟨w, hw⟩ := selected_coordinate_regular_quotient_unit_product u v χ d b hinj N J h
  have hz (i : Fin r) (hi : χ i = some k) : d i - N * b i = 0 := by
    have hie := hinj i e k hi he
    simp only [hie, heq, Nat.sub_self]
  rw [hw]
  exact ⟨restrict_selected_coordinate_unit_product_ne_zero w χ _ k hz,
    fun t l hlk ht => weightedOrder_restrict_selected_coordinate_single w χ _ hinj k l hlk hz t ht⟩

end MixedFujita
