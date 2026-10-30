/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Module.Basic
public import Mathlib.Tactic.NoncommRing

/-!
Cochains on the nerve of an index set and the Alexander–Whitney cup product (step 10).

The local part of the Deligne–Illusie map lives on the nerve of the index set `J` of the Frobenius
lifts of one chart: cochains are functions of tuples `j : Fin (a + 1) → J` with values in a ring
`A` (for us the exterior algebra of the chart), with the Čech differential
`(δα)(j) = Σ_k (-1)^k α(j ∘ succAbove k)` and no restriction maps (`indexCechD`). The
Alexander–Whitney cup product multiplies the values on the front face and the back face
(`indexCup`). Its Čech Leibniz rule `δ(α ∪ β) = δα ∪ β + (-1)^a α ∪ δβ` holds, evaluated at a tuple
(`indexCechD_indexCup`): the faces deleting a front vertex give `δα ∪ β`, those deleting a back
vertex give `α ∪ δβ`, and the two middle terms cancel. With the de Rham Leibniz rule and the
cocycles `(Φ_j, h_{jj'})` of checks 443 and 444, the antisymmetrized cup products are the
components of the Deligne–Illusie map.
-/

@[expose] public section

namespace MixedFujita

universe u v

section IndexNerve

variable {J : Type u} {A : Type v} [Ring A]

/-- The Čech differential on the nerve of `J` (no restriction maps). -/
def indexCechD (a : ℕ) (α : (Fin (a + 1) → J) → A) : (Fin (a + 2) → J) → A :=
  fun j => ∑ k : Fin (a + 2), (-1 : A) ^ (k : ℕ) * α (j ∘ Fin.succAbove k)

/-- The first `a + 1` vertices of a tuple of length `a + a' + 1`. -/
abbrev indexFront (a a' : ℕ) : Fin (a + 1) → Fin (a + a' + 1) := fun i => ⟨i, by omega⟩

/-- The last `a' + 1` vertices of a tuple of length `a + a' + 1`. -/
abbrev indexBack (a a' : ℕ) : Fin (a' + 1) → Fin (a + a' + 1) := fun i => ⟨a + i, by omega⟩

/-- **The Alexander–Whitney cup product** of index cochains, evaluated at a tuple. -/
def indexCup (a a' : ℕ) (α : (Fin (a + 1) → J) → A) (β : (Fin (a' + 1) → J) → A)
    (j : Fin (a + a' + 1) → J) : A :=
  α (j ∘ indexFront a a') * β (j ∘ indexBack a a')

/-- The vertex map of the face deleting the vertex `k` (a natural number). -/
abbrev indexFaceMap {N : ℕ} (k : ℕ) : Fin N → Fin (N + 1) :=
  fun i => ⟨if (i : ℕ) < k then i else i + 1, by split <;> omega⟩

/-- An embedding of vertices by an offset. -/
abbrev indexShift {N M : ℕ} (c : ℕ) (h : N + c ≤ M) : Fin N → Fin M := fun i => ⟨c + i, by omega⟩

theorem indexFaceMap_val {N : ℕ} (k : ℕ) (i : Fin N) :
    (indexFaceMap (N := N) k i : ℕ) = if (i : ℕ) < k then (i : ℕ) else (i : ℕ) + 1 := rfl

theorem indexShift_val {N M : ℕ} (c : ℕ) (h : N + c ≤ M) (i : Fin N) :
    (indexShift c h i : ℕ) = c + i := rfl

theorem indexFront_val (a a' : ℕ) (i : Fin (a + 1)) : (indexFront a a' i : ℕ) = i := rfl

theorem indexBack_val (a a' : ℕ) (i : Fin (a' + 1)) : (indexBack a a' i : ℕ) = a + i := rfl

theorem comp_eq_comp_of_val {N M : ℕ} (j : Fin M → J) {f g : Fin N → Fin M}
    (h : ∀ i, (f i : ℕ) = g i) : j ∘ f = j ∘ g :=
  congrArg (j ∘ ·) (funext fun i => Fin.ext (h i))

theorem succAbove_val_eq {N : ℕ} (k : Fin (N + 1)) (i : Fin N) :
    ((k.succAbove i : Fin (N + 1)) : ℕ) = (indexFaceMap (N := N) k i : ℕ) := by
  rcases lt_or_ge (Fin.castSucc i) k with h | h
  · rw [Fin.succAbove_of_castSucc_lt k i h]
    have h' : (i : ℕ) < k := h
    simp [h']
  · rw [Fin.succAbove_of_le_castSucc k i h]
    have h' : ¬ (i : ℕ) < k := by
      have : (k : ℕ) ≤ i := h
      omega
    simp [h']

theorem indexCechD_eq_sum_range (a : ℕ) (α : (Fin (a + 1) → J) → A) (j : Fin (a + 2) → J) :
    indexCechD a α j =
      ∑ k ∈ Finset.range (a + 2), (-1 : A) ^ k * α (j ∘ indexFaceMap k) := by
  rw [indexCechD, ← Fin.sum_univ_eq_sum_range (fun k => (-1 : A) ^ k * α (j ∘ indexFaceMap k))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [comp_eq_comp_of_val j (succAbove_val_eq k)]

/-- **The Čech Leibniz rule for the cup product**, evaluated at a tuple:
`δ(α ∪ β) = δα ∪ β + (-1)^a α ∪ δβ`. -/
theorem indexCechD_indexCup (a a' : ℕ) (α : (Fin (a + 1) → J) → A) (β : (Fin (a' + 1) → J) → A)
    (j : Fin (a + a' + 2) → J) :
    indexCechD (a + a') (indexCup a a' α β) j =
      indexCechD a α (j ∘ indexShift 0 (by omega)) * β (j ∘ indexShift (a + 1) (by omega)) +
        (-1 : A) ^ a * (α (j ∘ indexShift 0 (by omega)) *
          indexCechD a' β (j ∘ indexShift a (by omega))) := by
  have hL : indexCechD (a + a') (indexCup a a' α β) j =
      ∑ k ∈ Finset.range (a + 1), (-1 : A) ^ k * indexCup a a' α β (j ∘ indexFaceMap k) +
        ∑ l ∈ Finset.range (a' + 1),
          (-1 : A) ^ (a + 1 + l) * indexCup a a' α β (j ∘ indexFaceMap (a + 1 + l)) := by
    rw [indexCechD_eq_sum_range,
      show Finset.range (a + a' + 2) = Finset.range ((a + 1) + (a' + 1)) by congr 1; omega,
      Finset.sum_range_add]
  have hα' : indexCechD a α (j ∘ indexShift 0 (by omega)) =
      ∑ k ∈ Finset.range (a + 1),
          (-1 : A) ^ k * α ((j ∘ indexShift 0 (by omega)) ∘ indexFaceMap k) +
        (-1 : A) ^ (a + 1) * α ((j ∘ indexShift 0 (by omega)) ∘ indexFaceMap (a + 1)) := by
    rw [indexCechD_eq_sum_range, Finset.sum_range_succ]
  have hβ' : indexCechD a' β (j ∘ indexShift a (by omega)) =
      (-1 : A) ^ 0 * β ((j ∘ indexShift a (by omega)) ∘ indexFaceMap 0) +
        ∑ l ∈ Finset.range (a' + 1),
          (-1 : A) ^ (l + 1) * β ((j ∘ indexShift a (by omega)) ∘ indexFaceMap (l + 1)) := by
    rw [indexCechD_eq_sum_range, Finset.sum_range_succ', add_comm]
  rw [hL, hα', hβ', add_mul, Finset.sum_mul, mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
  have h1 : ∀ k ∈ Finset.range (a + 1),
      (-1 : A) ^ k * indexCup a a' α β (j ∘ indexFaceMap k) =
        (-1 : A) ^ k * α ((j ∘ indexShift 0 (by omega)) ∘ indexFaceMap k) *
          β (j ∘ indexShift (a + 1) (by omega)) := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have e1 : (j ∘ indexFaceMap k) ∘ indexFront a a' =
        (j ∘ indexShift 0 (by omega)) ∘ indexFaceMap k := by
      simp only [Function.comp_assoc]
      refine comp_eq_comp_of_val j fun i => ?_
      simp only [Function.comp_apply, indexFaceMap_val]
      split_ifs <;> omega
    have e2 : (j ∘ indexFaceMap k) ∘ indexBack a a' = j ∘ indexShift (a + 1) (by omega) := by
      simp only [Function.comp_assoc]
      refine comp_eq_comp_of_val j fun i => ?_
      simp only [Function.comp_apply, indexFaceMap_val]
      split_ifs <;> omega
    rw [indexCup, e1, e2, mul_assoc]
  have h2 : ∀ l ∈ Finset.range (a' + 1),
      (-1 : A) ^ (a + 1 + l) * indexCup a a' α β (j ∘ indexFaceMap (a + 1 + l)) =
        (-1 : A) ^ a * (α (j ∘ indexShift 0 (by omega)) *
          ((-1 : A) ^ (l + 1) * β ((j ∘ indexShift a (by omega)) ∘ indexFaceMap (l + 1)))) := by
    intro l hl
    have hl' := Finset.mem_range.mp hl
    have e1 : (j ∘ indexFaceMap (a + 1 + l)) ∘ indexFront a a' = j ∘ indexShift 0 (by omega) := by
      simp only [Function.comp_assoc]
      refine comp_eq_comp_of_val j fun i => ?_
      simp only [Function.comp_apply, indexFaceMap_val]
      split_ifs <;> omega
    have e2 : (j ∘ indexFaceMap (a + 1 + l)) ∘ indexBack a a' =
        (j ∘ indexShift a (by omega)) ∘ indexFaceMap (l + 1) := by
      simp only [Function.comp_assoc]
      refine comp_eq_comp_of_val j fun i => ?_
      simp only [Function.comp_apply, indexFaceMap_val]
      split_ifs <;> omega
    rw [indexCup, e1, e2, show a + 1 + l = a + (l + 1) by omega, pow_add, mul_assoc]
    congr 1
    exact ((Commute.neg_one_left _).pow_left (l + 1)).left_comm _
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2]
  have hlast : (j ∘ indexShift 0 (by omega : a + 2 + 0 ≤ a + a' + 2)) ∘ indexFaceMap (a + 1) =
      j ∘ indexShift 0 (by omega) := by
    simp only [Function.comp_assoc]
    refine comp_eq_comp_of_val j fun i => ?_
    simp only [Function.comp_apply]
    split_ifs <;> omega
  have hfirst : (j ∘ indexShift a (by omega : a' + 2 + a ≤ a + a' + 2)) ∘ indexFaceMap 0 =
      j ∘ indexShift (a + 1) (by omega) := by
    simp only [Function.comp_assoc]
    refine comp_eq_comp_of_val j fun i => ?_
    simp only [Function.comp_apply]
    split_ifs <;> omega
  rw [hlast, hfirst, pow_succ]
  noncomm_ring

end IndexNerve

end MixedFujita
