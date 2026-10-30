/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
The Iwasawa decomposition over a valuation subring, in the form used for limits of flags. For a
valuation subring R of a field F, every invertible matrix U over F has a lower triangular L such
that L U has entries in R and a determinant that is a unit of R
(`exists_isLowerTriangular_mul_integral`). The first row is divided by its coordinate of largest
absolute value, that column is cleared in the other rows, and the remaining rows and columns are
treated by induction. A lower triangular change of the rows of U keeps the flag of the spans of
the first rows, so this is the valuative criterion of properness of the flag variety, without
the flag variety.
-/

@[expose] public section

namespace MixedFujita

open Matrix

variable {F : Type*} [Field F]

/-- A coordinate of largest absolute value of a nonzero vector: every coordinate is an integral
multiple of it. -/
theorem exists_coord_div_mem (R : ValuationSubring F) {n : ℕ} (u : Fin n → F) (hu : u ≠ 0) :
    ∃ j₀, u j₀ ≠ 0 ∧ ∀ j, u j / u j₀ ∈ R := by
  classical
  obtain ⟨j₁, hj₁⟩ := Function.ne_iff.mp hu
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image Finset.univ (fun j => R.valuation (u j))
    ⟨j₁, Finset.mem_univ j₁⟩
  have hne : u j₀ ≠ 0 := by
    intro h0
    have h1 := hj₀ j₁ (Finset.mem_univ j₁)
    rw [h0, map_zero] at h1
    exact hj₁ ((Valuation.zero_iff _).mp (le_antisymm h1 zero_le))
  refine ⟨j₀, hne, fun j => ?_⟩
  rw [← R.valuation_le_one_iff, map_div₀]
  have hpos : 0 < R.valuation (u j₀) := by
    rw [zero_lt_iff]
    exact (Valuation.ne_zero_iff _).mpr hne
  exact (div_le_one₀ hpos).mpr (hj₀ j (Finset.mem_univ j))

/-- The Iwasawa decomposition over a valuation subring: an invertible matrix becomes integral
with unit determinant after a lower triangular change of its rows. -/
theorem exists_isLowerTriangular_mul_integral (R : ValuationSubring F) :
    ∀ (n : ℕ) (U : Matrix (Fin n) (Fin n) F), U.det ≠ 0 →
      ∃ L : Matrix (Fin n) (Fin n) F, L.IsLowerTriangular ∧ (∀ i j, (L * U) i j ∈ R) ∧
        (L * U).det ≠ 0 ∧ (L * U).det ∈ R ∧ (L * U).det⁻¹ ∈ R := by
  intro n
  induction n with
  | zero =>
    intro U _
    refine ⟨1, fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_, ?_, ?_⟩
    · rw [Matrix.det_isEmpty]
      exact one_ne_zero
    · rw [Matrix.det_isEmpty]
      exact R.one_mem
    · rw [Matrix.det_isEmpty, inv_one]
      exact R.one_mem
  | succ n ih =>
    intro U hU
    classical
    have hrow : U 0 ≠ 0 := fun h0 =>
      hU (Matrix.det_eq_zero_of_row_eq_zero 0 (fun j => congrFun h0 j))
    obtain ⟨j₀, ha, hdiv⟩ := exists_coord_div_mem R (U 0) hrow
    -- the first elimination: divide the first row by a = U 0 j₀ and clear the column j₀
    set E : Matrix (Fin (n + 1)) (Fin (n + 1)) F := Matrix.of fun i l =>
      if i = 0 then (if l = 0 then (U 0 j₀)⁻¹ else 0) else
        (if l = 0 then -(U i j₀ * (U 0 j₀)⁻¹) else if l = i then 1 else 0) with hE
    have hEl : E.IsLowerTriangular := by
      intro i l hil
      have hil' : i < l := hil
      simp only [hE, Matrix.of_apply]
      split_ifs with h1 h2 h3 h4
      · exact absurd (h1 ▸ h2 ▸ hil') (lt_irrefl _)
      · rfl
      · exact absurd (h3 ▸ hil') (Fin.not_lt_zero _)
      · exact absurd (h4 ▸ hil') (lt_irrefl _)
      · rfl
    have hEdet : E.det = (U 0 j₀)⁻¹ := by
      rw [Matrix.det_of_isLowerTriangular E hEl, Fin.prod_univ_succ]
      have h1 : ∀ i : Fin n, E i.succ i.succ = 1 := fun i => by
        simp [hE, Fin.succ_ne_zero]
      simp only [h1, Finset.prod_const_one, mul_one]
      simp [hE]
    set U₁ := E * U with hU₁
    have hU₁0 : ∀ j, U₁ 0 j = U 0 j / U 0 j₀ := by
      intro j
      rw [hU₁, Matrix.mul_apply, Finset.sum_eq_single 0]
      · simp [hE, div_eq_inv_mul]
      · intro l _ hl
        simp [hE, hl]
      · simp
    have hU₁i : ∀ i : Fin (n + 1), i ≠ 0 → ∀ j,
        U₁ i j = U i j - U i j₀ * (U 0 j₀)⁻¹ * U 0 j := by
      intro i hi j
      rw [hU₁, Matrix.mul_apply, Fin.sum_univ_succ]
      have hrest : ∑ l : Fin n, E i l.succ * U l.succ j = U i j := by
        obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.mpr hi
        rw [Finset.sum_eq_single i']
        · simp [hE, Fin.succ_ne_zero]
        · intro l _ hl
          have : l.succ ≠ i'.succ := fun h => hl (Fin.succ_injective _ h)
          simp [hE, Fin.succ_ne_zero, this]
        · simp
      rw [hrest]
      simp only [hE, Matrix.of_apply, hi, ↓reduceIte]
      ring
    have hU₁00 : U₁ 0 j₀ = 1 := by rw [hU₁0, div_self ha]
    have hU₁i0 : ∀ i : Fin (n + 1), i ≠ 0 → U₁ i j₀ = 0 := by
      intro i hi
      rw [hU₁i i hi, mul_assoc, inv_mul_cancel₀ ha, mul_one, sub_self]
    -- the remaining rows and columns
    set U' : Matrix (Fin n) (Fin n) F := U₁.submatrix Fin.succ j₀.succAbove with hU'
    have hcol : ∀ W : Matrix (Fin (n + 1)) (Fin (n + 1)) F, W 0 j₀ = 1 →
        (∀ i : Fin (n + 1), i ≠ 0 → W i j₀ = 0) →
        W.det = (-1) ^ (j₀ : ℕ) * (W.submatrix Fin.succ j₀.succAbove).det := by
      intro W h0 hi
      rw [Matrix.det_succ_column W j₀, Finset.sum_eq_single 0]
      · simp [h0, Fin.succAbove_zero]
      · intro i _ hne
        rw [hi i hne, mul_zero, zero_mul]
      · simp
    have hdetU₁ : U₁.det = (-1) ^ (j₀ : ℕ) * U'.det := hcol U₁ hU₁00 hU₁i0
    have hU'det : U'.det ≠ 0 := by
      intro h0
      have h1 : U₁.det = 0 := by rw [hdetU₁, h0, mul_zero]
      rw [hU₁, Matrix.det_mul, hEdet] at h1
      exact mul_ne_zero (inv_ne_zero ha) hU h1
    obtain ⟨L', hL'l, hL'R, hL'ne, hL'd, hL'd'⟩ := ih U' hU'det
    -- the induction step on the rows other than the first
    set L₂ : Matrix (Fin (n + 1)) (Fin (n + 1)) F := Matrix.of fun i l =>
      Fin.cases (Fin.cases 1 (fun _ => 0) l) (fun i' => Fin.cases 0 (fun l' => L' i' l') l) i
      with hL₂
    have hL₂l : L₂.IsLowerTriangular := by
      intro i l hil
      have hil' : i < l := hil
      simp only [hL₂, Matrix.of_apply]
      cases i using Fin.cases with
      | zero =>
        cases l using Fin.cases with
        | zero => exact absurd hil' (lt_irrefl _)
        | succ l' => simp
      | succ i' =>
        cases l using Fin.cases with
        | zero => exact absurd hil' (Fin.not_lt_zero _)
        | succ l' =>
          simp only [Fin.cases_succ]
          exact hL'l (Fin.succ_lt_succ_iff.mp hil')
    set W := L₂ * U₁ with hW
    have hW0 : ∀ j, W 0 j = U₁ 0 j := by
      intro j
      rw [hW, Matrix.mul_apply, Fin.sum_univ_succ]
      simp [hL₂]
    have hWs : ∀ (i' : Fin n) j, W i'.succ j = ∑ l' : Fin n, L' i' l' * U₁ l'.succ j := by
      intro i' j
      rw [hW, Matrix.mul_apply, Fin.sum_univ_succ]
      simp [hL₂]
    have hWsub : W.submatrix Fin.succ j₀.succAbove = L' * U' := by
      ext i' k
      rw [Matrix.submatrix_apply, hWs, Matrix.mul_apply]
      rfl
    have hWi0 : ∀ i : Fin (n + 1), i ≠ 0 → W i j₀ = 0 := by
      intro i hi
      obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.mpr hi
      rw [hWs]
      exact Finset.sum_eq_zero fun l' _ => by rw [hU₁i0 _ (Fin.succ_ne_zero l'), mul_zero]
    have hdetW : W.det = (-1) ^ (j₀ : ℕ) * (L' * U').det := by
      rw [hcol W (by rw [hW0, hU₁00]) hWi0, hWsub]
    have hsign : ((-1 : F) ^ (j₀ : ℕ)) ∈ R := R.pow_mem (R.neg_mem _ R.one_mem) _
    have hsign' : ((-1 : F) ^ (j₀ : ℕ))⁻¹ ∈ R := by
      rw [← inv_pow, inv_neg, inv_one]
      exact hsign
    refine ⟨L₂ * E, hL₂l.mul hEl, fun i j => ?_, ?_, ?_, ?_⟩
    · rw [Matrix.mul_assoc, ← hU₁, ← hW]
      cases i using Fin.cases with
      | zero =>
        rw [hW0, hU₁0]
        exact hdiv j
      | succ i' =>
        by_cases hj : j = j₀
        · rw [hj, hWi0 _ (Fin.succ_ne_zero i')]
          exact R.zero_mem
        · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
          have h1 : W i'.succ (j₀.succAbove k) = (L' * U') i' k := by
            rw [← hWsub, Matrix.submatrix_apply]
          rw [h1]
          exact hL'R i' k
    · rw [Matrix.mul_assoc, ← hU₁, ← hW, hdetW]
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hL'ne
    · rw [Matrix.mul_assoc, ← hU₁, ← hW, hdetW]
      exact mul_mem hsign hL'd
    · rw [Matrix.mul_assoc, ← hU₁, ← hW, hdetW, mul_inv]
      exact mul_mem hsign' hL'd'

end MixedFujita
