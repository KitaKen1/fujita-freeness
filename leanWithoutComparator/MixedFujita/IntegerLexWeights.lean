/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PowerSeriesExponents
public import Mathlib.Algebra.BigOperators.Fin
public import Lean.Elab.Tactic.Omega

/-!
Lexicographic order on a finite bounded collection of natural exponent
vectors is realized by positive integer weights. Give the radix base first;
the remaining digits contribute less than one unit of the preceding place.
This finite result does not assert a weight representation on all exponents.
-/

@[expose] public section

namespace MixedFujita

def radixExponentCode : (n : ℕ) → ℕ → (Fin n → ℕ) → ℕ
  | 0, _, _ => 0
  | n + 1, B, p => p 0 * B ^ n + radixExponentCode n B (fun i => p i.succ)

def integerLexWeight (n B : ℕ) (i : Fin n) : ℕ := B ^ (n - 1 - i.val)

theorem integerLexWeight_pos {n B : ℕ} (hB : 0 < B) (i : Fin n) :
    0 < integerLexWeight n B i := by
  exact pow_pos hB _

theorem radixExponentCode_eq_sum {n : ℕ} (B : ℕ) (p : Fin n → ℕ) :
    radixExponentCode n B p = ∑ i, integerLexWeight n B i * p i := by
  induction n with
  | zero => simp [radixExponentCode]
  | succ n ih =>
    rw [radixExponentCode, Fin.sum_univ_succ, ih]
    simp only [integerLexWeight, Fin.val_zero, Fin.val_succ, Nat.add_sub_cancel,
      Nat.sub_zero]
    have heq (i : Fin n) : n - 1 - i.val = n - (i.val + 1) := by omega
    simp_rw [heq]
    rw [mul_comm (p 0)]

theorem radixExponentCode_lt_pow {n : ℕ} {B : ℕ} (_hB : 0 < B)
    (p : Fin n → ℕ) (hp : ∀ i, p i < B) : radixExponentCode n B p < B ^ n := by
  induction n with
  | zero => simp [radixExponentCode]
  | succ n ih =>
    have htail := ih (fun i => p i.succ) (fun i => hp i.succ)
    have hhead : p 0 + 1 ≤ B := hp 0
    rw [radixExponentCode, pow_succ]
    have hmul := Nat.mul_le_mul_right (B ^ n) hhead
    nlinarith

theorem radixExponentCode_lt_of_lex {n : ℕ} {B : ℕ} (hB : 0 < B)
    (p q : Fin n → ℕ) (hp : ∀ i, p i < B) (hq : ∀ i, q i < B)
    (hlex : Pi.Lex (· < ·) (· < ·) p q) :
    radixExponentCode n B p < radixExponentCode n B q := by
  induction n with
  | zero => obtain ⟨i, _⟩ := hlex; exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨i, hprev, hi⟩ := hlex
    obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
    · have htail := radixExponentCode_lt_pow hB (fun i => p i.succ) (fun i => hp i.succ)
      have hhead : p 0 + 1 ≤ q 0 := hi
      have hmul := Nat.mul_le_mul_right (B ^ n) hhead
      rw [radixExponentCode, radixExponentCode]
      nlinarith
    · have hhead : p 0 = q 0 := hprev 0 (by simp)
      have htail : Pi.Lex (· < ·) (· < ·) (fun j : Fin n => p j.succ)
          (fun j : Fin n => q j.succ) :=
        ⟨i, fun j hj => hprev j.succ (by simpa using hj), hi⟩
      have h := ih (fun j : Fin n => p j.succ) (fun j : Fin n => q j.succ)
        (fun j => hp j.succ) (fun j => hq j.succ) htail
      simpa only [radixExponentCode, hhead] using Nat.add_lt_add_left h (q 0 * B ^ n)

theorem integerLexWeight_lt_of_lex {n : ℕ} {B : ℕ} (hB : 0 < B)
    (p q : Fin n →₀ ℕ) (hp : ∀ i, p i < B) (hq : ∀ i, q i < B)
    (hlex : (MonomialOrder.lex (σ := Fin n)).toSyn p < MonomialOrder.lex.toSyn q) :
    (∑ i, integerLexWeight n B i * p i) < ∑ i, integerLexWeight n B i * q i := by
  rw [← radixExponentCode_eq_sum, ← radixExponentCode_eq_sum]
  apply radixExponentCode_lt_of_lex hB p q hp hq
  exact hlex

theorem exists_finite_exponent_radix_bound {n : ℕ} (S : Finset (Fin n →₀ ℕ)) :
    ∃ B > 0, ∀ p ∈ S, ∀ i, p i < B := by
  let B := S.sup (fun p => ∑ i, p i) + 1
  refine ⟨B, by dsimp [B]; omega, ?_⟩
  intro p hp i
  have hi : p i ≤ ∑ j, p j := Finset.single_le_sum (fun j _ => Nat.zero_le (p j))
    (Finset.mem_univ i)
  have hsup := Finset.le_sup (f := fun p : Fin n →₀ ℕ => ∑ j, p j) hp
  dsimp [B]
  omega

/-- One explicit positive integer weight vector works for every lex comparison
in the finite collection, hence for every polynomial in a finite family. -/
theorem exists_common_positive_integer_lex_weights {n : ℕ} (S : Finset (Fin n →₀ ℕ)) :
    ∃ w : Fin n → ℕ, (∀ i, 0 < w i) ∧
      ∀ p ∈ S, ∀ q ∈ S,
        (MonomialOrder.lex (σ := Fin n)).toSyn p < MonomialOrder.lex.toSyn q →
          (∑ i, w i * p i) < ∑ i, w i * q i := by
  obtain ⟨B, hB, hbound⟩ := exists_finite_exponent_radix_bound S
  exact ⟨integerLexWeight n B, integerLexWeight_pos hB,
    fun p hp q hq hlex => integerLexWeight_lt_of_lex hB p q (hbound p hp) (hbound q hq) hlex⟩

end MixedFujita
