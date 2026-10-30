/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.IndexNerveLeibniz

/-!
Index cochains on sequences of vertices and their cup product (step 10).

An index cochain of Čech degree `a` is here a function `α : (ℕ → J) → A` on infinite sequences of
indices that only depends on the first `a + 1` vertices (`SeqSupported a α`). Deleting the vertex
`k` is `s ↦ s ∘ seqSkip k`, the Čech differential is `(δα)(s) = Σ_{k ≤ a+1} (-1)^k α(s ∘ seqSkip k)`
(`seqCechD`) and the cup product is `(α ∪ β)(s) = α(s) β(s(· + a))` (`seqCup`). Unlike the
`Fin`-indexed cochains of check 446, the degree of a cup product does not appear in its type, so
sums of products over the antidiagonal need no casts. The Čech Leibniz rule
`δ(α ∪ β) = δα ∪ β + (-1)^a α ∪ δβ` (`seqCechD_seqCup`) only needs `α` to be supported.
-/

@[expose] public section

namespace MixedFujita

universe u v

section Sequence

variable {J : Type u} {A : Type v} [Ring A]

/-- Deleting the vertex `k`: `i ↦ i` for `i < k` and `i ↦ i + 1` otherwise. -/
def seqSkip (k i : ℕ) : ℕ := if i < k then i else i + 1

/-- The sequence of vertices from the vertex `a` on. -/
def seqShift (a : ℕ) (s : ℕ → J) : ℕ → J := fun i => s (i + a)

/-- An index cochain of Čech degree `a` only depends on the first `a + 1` vertices. -/
def SeqSupported (a : ℕ) (α : (ℕ → J) → A) : Prop :=
  ∀ s t : ℕ → J, (∀ i ≤ a, s i = t i) → α s = α t

/-- **The Čech differential** of an index cochain of Čech degree `a`. -/
def seqCechD (a : ℕ) (α : (ℕ → J) → A) (s : ℕ → J) : A :=
  ∑ k ∈ Finset.range (a + 2), (-1 : A) ^ k * α (s ∘ seqSkip k)

/-- **The cup product** of an index cochain of Čech degree `a` with an index cochain. -/
def seqCup (a : ℕ) (α β : (ℕ → J) → A) (s : ℕ → J) : A :=
  α s * β (seqShift a s)

theorem seqShift_comp_seqSkip_of_le {a k : ℕ} (hk : k ≤ a) (s : ℕ → J) :
    seqShift a (s ∘ seqSkip k) = seqShift (a + 1) s := by
  funext i
  simp only [seqShift, Function.comp_apply, seqSkip]
  split_ifs <;> first | omega | rfl

theorem seqShift_comp_seqSkip_add (a k : ℕ) (s : ℕ → J) :
    seqShift a (s ∘ seqSkip (a + k)) = seqShift a s ∘ seqSkip k := by
  funext i
  simp only [seqShift, Function.comp_apply, seqSkip]
  split_ifs <;> first | omega | rfl | (congr 1; omega)

theorem seqShift_comp_seqSkip_zero (a : ℕ) (s : ℕ → J) :
    seqShift a s ∘ seqSkip 0 = seqShift (a + 1) s := by
  funext i
  simp only [seqShift, Function.comp_apply, seqSkip]
  split_ifs <;> first | omega | rfl | (congr 1; omega)

omit [Ring A] in
theorem seqSupported_comp_seqSkip {a : ℕ} {α : (ℕ → J) → A} (hα : SeqSupported a α) (k : ℕ)
    (hk : a < k) (s : ℕ → J) : α (s ∘ seqSkip k) = α s :=
  hα _ _ fun i hi => by
    simp only [Function.comp_apply, seqSkip, show i < k by omega, ↓reduceIte]

theorem seqSupported_seqCup {a a' : ℕ} {α β : (ℕ → J) → A} (hα : SeqSupported a α)
    (hβ : SeqSupported a' β) : SeqSupported (a + a') (seqCup a α β) := by
  intro s t h
  rw [seqCup, seqCup, hα s t fun i hi => h i (by omega),
    hβ (seqShift a s) (seqShift a t) fun i hi => h (i + a) (by omega)]

theorem seqSupported_seqCechD {a : ℕ} {α : (ℕ → J) → A} (hα : SeqSupported a α) :
    SeqSupported (a + 1) (seqCechD a α) := by
  intro s t h
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hα (s ∘ seqSkip k) (t ∘ seqSkip k) fun i hi => h _ (by
    simp only [seqSkip]
    split_ifs <;> omega)]

omit [Ring A] in
theorem seqSupported_comp {a : ℕ} {α : (ℕ → J) → A} (hα : SeqSupported a α) (f : A → A) :
    SeqSupported a (fun s => f (α s)) :=
  fun s t h => congrArg f (hα s t h)

theorem seqCechD_comp_ringHom (f : A →+* A) (a : ℕ) (α : (ℕ → J) → A) (s : ℕ → J) :
    seqCechD a (fun t => f (α t)) s = f (seqCechD a α s) := by
  simp only [seqCechD, map_sum, map_mul, map_pow, map_neg, map_one]

theorem seqCechD_sum {ι : Type*} (I : Finset ι) (a : ℕ) (α : ι → (ℕ → J) → A) (s : ℕ → J) :
    seqCechD a (fun t => ∑ x ∈ I, α x t) s = ∑ x ∈ I, seqCechD a (α x) s := by
  simp only [seqCechD, Finset.mul_sum]
  exact Finset.sum_comm

/-- **The Čech Leibniz rule for the cup product of sequence cochains**:
`δ(α ∪ β) = δα ∪ β + (-1)^a α ∪ δβ` when `α` has Čech degree `a`. -/
theorem seqCechD_seqCup {a : ℕ} {α : (ℕ → J) → A} (hα : SeqSupported a α) (β : (ℕ → J) → A)
    (a' : ℕ) (s : ℕ → J) :
    seqCechD (a + a') (seqCup a α β) s =
      seqCup (a + 1) (seqCechD a α) β s + (-1 : A) ^ a * seqCup a α (seqCechD a' β) s := by
  have hL : seqCechD (a + a') (seqCup a α β) s =
      ∑ k ∈ Finset.range (a + 1), (-1 : A) ^ k * seqCup a α β (s ∘ seqSkip k) +
        ∑ l ∈ Finset.range (a' + 1),
          (-1 : A) ^ (a + 1 + l) * seqCup a α β (s ∘ seqSkip (a + 1 + l)) := by
    rw [seqCechD,
      show Finset.range (a + a' + 2) = Finset.range ((a + 1) + (a' + 1)) by congr 1; omega,
      Finset.sum_range_add]
  have hα' : seqCechD a α s =
      ∑ k ∈ Finset.range (a + 1), (-1 : A) ^ k * α (s ∘ seqSkip k) +
        (-1 : A) ^ (a + 1) * α s := by
    rw [seqCechD, Finset.sum_range_succ, seqSupported_comp_seqSkip hα (a + 1) (by omega) s]
  have hβ' : seqCechD a' β (seqShift a s) =
      (-1 : A) ^ 0 * β (seqShift (a + 1) s) +
        ∑ l ∈ Finset.range (a' + 1), (-1 : A) ^ (l + 1) * β (seqShift a s ∘ seqSkip (l + 1)) := by
    rw [seqCechD, Finset.sum_range_succ', add_comm, seqShift_comp_seqSkip_zero]
  show _ = seqCechD a α s * β (seqShift (a + 1) s) +
    (-1 : A) ^ a * (α s * seqCechD a' β (seqShift a s))
  rw [hL, hα', hβ', add_mul, Finset.sum_mul, mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
  have h1 : ∀ k ∈ Finset.range (a + 1), (-1 : A) ^ k * seqCup a α β (s ∘ seqSkip k) =
      (-1 : A) ^ k * α (s ∘ seqSkip k) * β (seqShift (a + 1) s) := by
    intro k hk
    have hk' : k ≤ a := by
      have := Finset.mem_range.mp hk
      omega
    rw [seqCup, seqShift_comp_seqSkip_of_le hk' s, mul_assoc]
  have h2 : ∀ l ∈ Finset.range (a' + 1),
      (-1 : A) ^ (a + 1 + l) * seqCup a α β (s ∘ seqSkip (a + 1 + l)) =
        (-1 : A) ^ a * (α s * ((-1 : A) ^ (l + 1) * β (seqShift a s ∘ seqSkip (l + 1)))) := by
    intro l _
    rw [seqCup, seqSupported_comp_seqSkip hα (a + 1 + l) (by omega) s,
      show a + 1 + l = a + (l + 1) by omega, seqShift_comp_seqSkip_add, pow_add, mul_assoc]
    congr 1
    exact ((Commute.neg_one_left _).pow_left (l + 1)).left_comm _
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, pow_succ]
  noncomm_ring

end Sequence

end MixedFujita
