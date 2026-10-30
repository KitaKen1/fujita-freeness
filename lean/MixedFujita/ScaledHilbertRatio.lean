/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveSubspaceBound

/-!
A scaled Hilbert ratio. If h(j)/j^n tends to a positive limit, then
h(floor(theta j))/h(M j) tends to (theta/M)^n. This permits an upper comparison with the
hyperplane class without proving a Hilbert limit for every ample divisor.
-/

@[expose] public section

open Filter Topology

namespace MixedFujita

/-- A scaled denominator in the Hilbert ratio, with no monotonicity assumption on h. -/
theorem tendsto_ratio_floor_mul_of_tendsto_div_pow {n : ℕ} {h : ℕ → ℕ} {ℓ : ℝ}
    (hℓ : 0 < ℓ)
    (hlim : Tendsto (fun j : ℕ => (h j : ℝ) / (j : ℝ) ^ n) atTop (nhds ℓ))
    {θ : ℝ} (hθ : 0 < θ) {M : ℕ} (hM : 1 ≤ M) :
    Tendsto (fun j : ℕ => (h ⌊θ * j⌋₊ : ℝ) / (h (M * j) : ℝ)) atTop
      (nhds ((θ / M) ^ n)) := by
  have hMt : Tendsto (fun j : ℕ => M * j) atTop atTop :=
    tendsto_atTop_mono (fun j => Nat.le_mul_of_pos_left j hM) tendsto_id
  have hden := (hlim.comp hMt).mul_const ((M : ℝ) ^ n)
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have hden' : Tendsto (fun j : ℕ => (h (M * j) : ℝ) / (j : ℝ) ^ n) atTop
      (nhds (ℓ * (M : ℝ) ^ n)) := by
    refine hden.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with j hj
    have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
    simp only [Function.comp, Nat.cast_mul, mul_pow]
    field_simp
  have hq : Tendsto (fun j : ℕ => ⌊θ * j⌋₊) atTop atTop := tendsto_nat_floor_mul_atTop θ hθ
  have hfloor := (tendsto_nat_floor_mul_div_atTop hθ.le).comp tendsto_natCast_atTop_atTop
  have hnum := (hlim.comp hq).mul (hfloor.pow n)
  have hprod := hnum.div hden' (mul_ne_zero hℓ.ne' (pow_ne_zero _ hM0))
  have hlimit : (ℓ * θ ^ n) / (ℓ * (M : ℝ) ^ n) = (θ / M) ^ n := by
    rw [div_pow]
    field_simp
  rw [hlimit] at hprod
  refine hprod.congr' ?_
  have hpos := hden'.eventually (lt_mem_nhds
    (half_lt_self (mul_pos hℓ (pow_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)) n))))
  filter_upwards [hpos, hq.eventually (eventually_ge_atTop 1), eventually_ge_atTop 1] with
    j hj hqj hj1
  have hq0 : (⌊θ * (j : ℝ)⌋₊ : ℝ) ≠ 0 := by
    exact_mod_cast (show ⌊θ * (j : ℝ)⌋₊ ≠ 0 by omega)
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  have hh0 : (h (M * j) : ℝ) ≠ 0 := by
    intro hz
    rw [hz, zero_div] at hj
    have : 0 < ℓ * (M : ℝ) ^ n := mul_pos hℓ (pow_pos (by positivity) n)
    linarith
  simp only [Pi.div_apply, Function.comp, div_pow]
  field_simp

end MixedFujita
