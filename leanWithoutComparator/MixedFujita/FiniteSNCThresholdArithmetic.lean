/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Tactic

/-!
Exact rational endpoints of the finite coefficient inequalities arising from a
fixed effective Cartier perturbation of a klt SNC boundary. A positive integral
presentation and an actual coefficient attaining the endpoint are constructed.
-/

@[expose] public section

namespace MixedFujita

universe u

/-- One positive perturbation coefficient gives the exact rational upper bound. -/
theorem integer_perturbation_coefficient_lt_iff (b g : ℤ) (d p q : ℕ)
    (hd : 1 ≤ d) (hq : 1 ≤ q) (hg : 0 < g) :
    (q : ℤ) * b + ((d * p : ℕ) : ℤ) * g < ((q * d : ℕ) : ℤ) ↔
      (p : ℚ) / (q : ℚ) < ((d : ℚ) - b) / ((d : ℚ) * g) := by
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
  have hgQ : (0 : ℚ) < g := by exact_mod_cast hg
  have hcast :
      ((q : ℤ) * b + ((d * p : ℕ) : ℤ) * g < ((q * d : ℕ) : ℤ)) ↔
      (q : ℚ) * b + (d : ℚ) * p * g < (q : ℚ) * d := by
    norm_cast
  rw [hcast, div_lt_div_iff₀ hqQ (mul_pos hdQ hgQ)]
  constructor <;> intro h <;> nlinarith

/-- The same positive coefficient also gives the non-strict endpoint inequality. -/
theorem integer_perturbation_coefficient_le_iff (b g : ℤ) (d p q : ℕ)
    (hd : 1 ≤ d) (hq : 1 ≤ q) (hg : 0 < g) :
    (q : ℤ) * b + ((d * p : ℕ) : ℤ) * g ≤ ((q * d : ℕ) : ℤ) ↔
      (p : ℚ) / (q : ℚ) ≤ ((d : ℚ) - b) / ((d : ℚ) * g) := by
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
  have hgQ : (0 : ℚ) < g := by exact_mod_cast hg
  have hcast :
      ((q : ℤ) * b + ((d * p : ℕ) : ℤ) * g ≤ ((q * d : ℕ) : ℤ)) ↔
      (q : ℚ) * b + (d : ℚ) * p * g ≤ (q : ℚ) * d := by norm_cast
  rw [hcast, div_le_div_iff₀ hqQ (mul_pos hdQ hgQ)]
  constructor <;> intro h <;> nlinarith

/-- The finite positive minimum has an integral presentation, attains a
coefficient equality, and exactly characterizes all rational perturbations. -/
theorem finite_integer_coefficients_exact_threshold {r : ℕ} (b g : Fin r → ℤ)
    (d : ℕ) (hd : 1 ≤ d) (hb : ∀ i, b i < (d : ℤ))
    (hg : ∀ i, 0 ≤ g i) (hpos : ∃ i, 0 < g i) :
    ∃ (a q₀ : ℕ) (i₀ : Fin r), 1 ≤ a ∧ 1 ≤ q₀ ∧ 0 < g i₀ ∧
      (a : ℚ) / (q₀ : ℚ) = ((d : ℚ) - b i₀) / ((d : ℚ) * g i₀) ∧
      (q₀ : ℤ) * b i₀ + ((d * a : ℕ) : ℤ) * g i₀ = ((q₀ * d : ℕ) : ℤ) ∧
      ∀ (p q : ℕ), 1 ≤ q →
        ((∀ i, (q : ℤ) * b i + ((d * p : ℕ) : ℤ) * g i < ((q * d : ℕ) : ℤ)) ↔
          (p : ℚ) / (q : ℚ) < (a : ℚ) / (q₀ : ℚ)) := by
  classical
  let I := {i : Fin r // 0 < g i}
  haveI : Nonempty I := by obtain ⟨i, hi⟩ := hpos; exact ⟨⟨i, hi⟩⟩
  obtain ⟨i₀, hmin⟩ := Finite.exists_min
    (fun i : I => ((d : ℚ) - b i.1) / ((d : ℚ) * g i.1))
  let a := ((d : ℤ) - b i₀.1).toNat
  let q₀ := d * (g i₀.1).toNat
  have hgap : 0 < (d : ℤ) - b i₀.1 := sub_pos.mpr (hb i₀.1)
  have haZ : (a : ℤ) = (d : ℤ) - b i₀.1 := Int.toNat_of_nonneg hgap.le
  have hgZ : ((g i₀.1).toNat : ℤ) = g i₀.1 := Int.toNat_of_nonneg i₀.property.le
  have ha : 1 ≤ a := by omega
  have hgn : 0 < (g i₀.1).toNat := by have := i₀.property; omega
  have hq₀ : 1 ≤ q₀ := Nat.mul_pos (by omega) hgn
  have hqZ : (q₀ : ℤ) = (d : ℤ) * g i₀.1 := by
    dsimp [q₀]
    rw [hgZ]
  have haQ : (a : ℚ) = (d : ℚ) - b i₀.1 := by exact_mod_cast haZ
  have hqQ : (q₀ : ℚ) = (d : ℚ) * g i₀.1 := by exact_mod_cast hqZ
  have hratio : (a : ℚ) / (q₀ : ℚ) =
      ((d : ℚ) - b i₀.1) / ((d : ℚ) * g i₀.1) := by rw [haQ, hqQ]
  refine ⟨a, q₀, i₀.1, ha, hq₀, i₀.property, hratio, ?_, ?_⟩
  · simp only [q₀, Nat.cast_mul, haZ, hgZ]
    ring
  · intro p q hq
    constructor
    · intro h
      rw [hratio]
      exact (integer_perturbation_coefficient_lt_iff (b i₀.1) (g i₀.1) d p q hd hq
        i₀.property).mp (h i₀.1)
    · intro h i
      by_cases hgi : 0 < g i
      · apply (integer_perturbation_coefficient_lt_iff (b i) (g i) d p q hd hq hgi).mpr
        rw [hratio] at h
        exact h.trans_le (hmin ⟨i, hgi⟩)
      · have hzero : g i = 0 := by have := hg i; omega
        have hmul := mul_lt_mul_of_pos_left (hb i) (by exact_mod_cast hq : (0 : ℤ) < q)
        simpa only [hzero, mul_zero, add_zero, Nat.cast_mul] using hmul

/-- Exact rational endpoints are independent of the finite presentation:
testing each endpoint itself suffices, with no density argument required. -/
theorem rational_threshold_eq_of_natural_tests (a b q s : ℕ) (hq : 1 ≤ q) (hs : 1 ≤ s)
    (htest : ∀ (p r : ℕ), 1 ≤ r →
      ((p : ℚ) / r < (a : ℚ) / q ↔ (p : ℚ) / r < (b : ℚ) / s)) :
    (a : ℚ) / q = (b : ℚ) / s := by
  apply le_antisymm
  · by_contra h
    have hlt : (b : ℚ) / s < (a : ℚ) / q := lt_of_not_ge h
    exact (lt_irrefl ((b : ℚ) / s)) ((htest b s hs).mp hlt)
  · by_contra h
    have hlt : (a : ℚ) / q < (b : ℚ) / s := lt_of_not_ge h
    exact (lt_irrefl ((a : ℚ) / q)) ((htest a q hq).mpr hlt)

end MixedFujita
