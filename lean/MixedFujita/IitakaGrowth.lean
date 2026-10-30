/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LinearEffectiveFreenessStatement

/-!
Two numerical bridges for F2. A positive polynomial lower bound at arbitrarily large degrees
and an upper bound at every degree determine a unique exponent. Upper bounds on the finitely
many residue classes modulo a positive integer give a single bound at every degree. The latter
is the arithmetic step needed after applying Hilbert estimates to the coherent sheaves
f_* O_X(rD) for 0 ≤ r < q. These lemmas do not supply those geometric estimates, semiampleness,
existence of an Iitaka exponent, or its equality with numerical dimension.
-/

@[expose] public section

open Filter

namespace MixedFujita

/-- A frequent lower growth exponent cannot exceed an everywhere upper growth exponent. -/
theorem polynomialGrowth_lower_exponent_le {f : ℕ → ℝ} (hf0 : 0 ≤ f 0)
    {k l : ℕ} {c C : ℝ} (hc : 0 < c)
    (hlower : ∃ᶠ j : ℕ in atTop, c * (j : ℝ) ^ k ≤ f j)
    (hupper : ∀ j : ℕ, f j ≤ C * ((j : ℝ) + 1) ^ l) : k ≤ l := by
  have hC : 0 ≤ C := by simpa using hf0.trans (hupper 0)
  by_contra hkl
  have hlk : l + 1 ≤ k := by omega
  obtain ⟨N, hN⟩ := exists_nat_gt (C * 2 ^ l / c + 1)
  obtain ⟨j, hlow, hjN⟩ := (hlower.and_eventually (eventually_ge_atTop N)).exists
  have hjN' : (N : ℝ) ≤ j := by exact_mod_cast hjN
  have hj1 : (1 : ℝ) < j := by
    have : 0 ≤ C * 2 ^ l / c := by positivity
    linarith
  have hlarge : C * 2 ^ l < c * (j : ℝ) := by
    have : C * 2 ^ l / c < (j : ℝ) := by linarith
    simpa only [mul_comm] using (div_lt_iff₀ hc).mp this
  have hpow : (j : ℝ) ^ (l + 1) ≤ (j : ℝ) ^ k :=
    pow_le_pow_right₀ hj1.le hlk
  have hshift : ((j : ℝ) + 1) ^ l ≤ (2 * (j : ℝ)) ^ l :=
    pow_le_pow_left₀ (by positivity) (by linarith) l
  have hineq : (c * (j : ℝ)) * (j : ℝ) ^ l ≤ (C * 2 ^ l) * (j : ℝ) ^ l := calc
    _ = c * (j : ℝ) ^ (l + 1) := by rw [pow_succ]; ring
    _ ≤ c * (j : ℝ) ^ k := mul_le_mul_of_nonneg_left hpow hc.le
    _ ≤ f j := hlow
    _ ≤ C * ((j : ℝ) + 1) ^ l := hupper j
    _ ≤ C * (2 * (j : ℝ)) ^ l := mul_le_mul_of_nonneg_left hshift hC
    _ = _ := by rw [mul_pow]; ring
  exact (not_le_of_gt hlarge) (le_of_mul_le_mul_right hineq (pow_pos (by linarith) l))

/-- Finitely many residue class estimates control all degrees, including small degrees. -/
theorem polynomialGrowth_upper_of_residue_bounds {f : ℕ → ℝ} {q k : ℕ} (hq : 0 < q)
    (C : Fin q → ℝ)
    (hbound : ∀ (r : Fin q) (t : ℕ), f (q * t + r) ≤ C r * ((t : ℝ) + 1) ^ k) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j : ℕ, f j ≤ B * ((j : ℝ) + 1) ^ k := by
  classical
  let B : ℝ := ∑ r : Fin q, max (C r) 0
  have hB : 0 ≤ B := Finset.sum_nonneg fun r _ => le_max_right _ _
  refine ⟨B, hB, fun j => ?_⟩
  let r : Fin q := ⟨j % q, Nat.mod_lt j hq⟩
  have hCr : C r ≤ B := (le_max_left _ _).trans
    (Finset.single_le_sum (fun a _ => le_max_right (C a) 0) (Finset.mem_univ r))
  have ht : ((j / q : ℕ) : ℝ) ≤ j := by exact_mod_cast Nat.div_le_self j q
  have hpow : (((j / q : ℕ) : ℝ) + 1) ^ k ≤ ((j : ℝ) + 1) ^ k :=
    pow_le_pow_left₀ (by positivity) (by linarith) k
  calc
    f j = f (q * (j / q) + r) := by congr 1; exact (Nat.div_add_mod j q).symm
    _ ≤ C r * (((j / q : ℕ) : ℝ) + 1) ^ k := hbound r (j / q)
    _ ≤ B * (((j / q : ℕ) : ℝ) + 1) ^ k := mul_le_mul_of_nonneg_right hCr (by positivity)
    _ ≤ B * ((j : ℝ) + 1) ^ k := mul_le_mul_of_nonneg_left hpow hB

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- The growth definition of Iitaka dimension has at most one exponent. -/
theorem CartierIitakaDimension_unique (K : Type u) [Field K] {X : Scheme.{u}}
    [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] {D : CartierDivisor X} {k l : ℕ}
    (hk : CartierIitakaDimension K D k) (hl : CartierIitakaDimension K D l) : k = l := by
  obtain ⟨⟨c, hc, hlow⟩, C, hupp⟩ := hk
  obtain ⟨⟨d, hd, hlow'⟩, B, hupp'⟩ := hl
  exact Nat.le_antisymm
    (polynomialGrowth_lower_exponent_le (by positivity) hc hlow hupp')
    (polynomialGrowth_lower_exponent_le (by positivity) hd hlow' hupp)

end MixedFujita
