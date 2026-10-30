/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.IndexNerveCup
public import Mathlib.Logic.Function.Iterate

/-!
The graded cup product on the index nerve and its two Leibniz rules (step 10).

Let `A` be a ring with an involution `σ` (a ring homomorphism with `σ ∘ σ = id`, for us the grade
involution of the exterior algebra) and an additive map `d` with `d(x y) = d x · y + σ x · d y` and
`d ∘ σ = -σ ∘ d` (the de Rham differential). The graded cup product of index cochains of Čech
degrees `a` and `a'` is `α ∪ β = (σ^{a'} ∘ α) ∪₀ β` (`indexGradedCup`; `σ^{a'}` carries the Koszul
sign of the de Rham degree of `α` past the Čech degree of `β`). It satisfies the Čech Leibniz rule
`δ(α ∪ β) = δα ∪ β + (-1)^a (σ ∘ α) ∪ δβ` (`indexCechD_indexGradedCup`, from check 446) and the
de Rham Leibniz rule `d(α ∪ β) = (-1)^{a'} (d ∘ α) ∪ β + (σ ∘ α) ∪ (d ∘ β)`
(`map_indexGradedCup`). Together, with the total differential `D = δ + (-1)^a d`, they give the
graded Leibniz rule `D(α ∪ β) = Dα ∪ β + (-1)^a (σ ∘ α) ∪ Dβ` used for the products of the
Deligne–Illusie cocycles.
-/

@[expose] public section

namespace MixedFujita

universe u v

section Graded

variable {J : Type u} {A : Type v} [Ring A] (σ : A →+* A)

/-- **The graded cup product** of index cochains: `(σ^{a'} ∘ α) ∪₀ β`. -/
def indexGradedCup (a a' : ℕ) (α : (Fin (a + 1) → J) → A) (β : (Fin (a' + 1) → J) → A)
    (j : Fin (a + a' + 1) → J) : A :=
  indexCup a a' (fun x => (σ ^ a') (α x)) β j

theorem indexCechD_comp_ringHom (f : A →+* A) (a : ℕ) (α : (Fin (a + 1) → J) → A)
    (j : Fin (a + 2) → J) :
    indexCechD a (fun x => f (α x)) j = f (indexCechD a α j) := by
  simp only [indexCechD, map_sum, map_mul, map_pow, map_neg, map_one]

variable (hσ : ∀ x, σ (σ x) = x)

include hσ in
theorem ringHom_pow_succ_succ (n : ℕ) (x : A) : (σ ^ (n + 2)) x = (σ ^ n) x := by
  rw [RingHom.coe_pow, RingHom.coe_pow, Function.iterate_add_apply]
  exact congrArg _ (hσ x)

theorem ringHom_pow_comm (n : ℕ) (x : A) : σ ((σ ^ n) x) = (σ ^ n) (σ x) := by
  rw [RingHom.coe_pow, ← Function.iterate_succ_apply' σ n x, Function.iterate_succ_apply]

include hσ in
/-- **The Čech Leibniz rule of the graded cup product**, evaluated at a tuple. -/
theorem indexCechD_indexGradedCup (a a' : ℕ) (α : (Fin (a + 1) → J) → A)
    (β : (Fin (a' + 1) → J) → A) (j : Fin (a + a' + 2) → J) :
    indexCechD (a + a') (indexGradedCup σ a a' α β) j =
      indexCechD a (fun x => (σ ^ a') (α x)) (j ∘ indexShift 0 (by omega)) *
          β (j ∘ indexShift (a + 1) (by omega)) +
        (-1 : A) ^ a * ((σ ^ (a' + 1)) (σ (α (j ∘ indexShift 0 (by omega)))) *
          indexCechD a' β (j ∘ indexShift a (by omega))) := by
  have h := indexCechD_indexCup a a' (fun x => (σ ^ a') (α x)) β j
  have hs : (σ ^ (a' + 1)) (σ (α (j ∘ indexShift 0 (by omega)))) =
      (σ ^ a') (α (j ∘ indexShift 0 (by omega))) := by
    rw [RingHom.coe_pow, RingHom.coe_pow, Function.iterate_succ_apply, hσ]
  rw [hs]
  exact h

variable (d : A →+ A) (hd : ∀ x y, d (x * y) = d x * y + σ x * d y)
  (hdσ : ∀ x, d (σ x) = -σ (d x))

include hdσ in
theorem map_ringHom_pow (n : ℕ) (x : A) : d ((σ ^ n) x) = (-1 : A) ^ n * (σ ^ n) (d x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have e1 : (σ ^ (n + 1)) x = σ ((σ ^ n) x) := by
      rw [RingHom.coe_pow, RingHom.coe_pow, Function.iterate_succ_apply']
    have e2 : (σ ^ (n + 1)) (d x) = σ ((σ ^ n) (d x)) := by
      rw [RingHom.coe_pow, RingHom.coe_pow, Function.iterate_succ_apply']
    rw [e1, e2, hdσ, ih, map_mul, map_pow, map_neg, map_one, pow_succ]
    noncomm_ring

include hd hdσ in
/-- **The de Rham Leibniz rule of the graded cup product**:
`d(α ∪ β) = (-1)^{a'} (d ∘ α) ∪ β + (σ ∘ α) ∪ (d ∘ β)`. -/
theorem map_indexGradedCup (a a' : ℕ) (α : (Fin (a + 1) → J) → A) (β : (Fin (a' + 1) → J) → A)
    (j : Fin (a + a' + 1) → J) :
    d (indexGradedCup σ a a' α β j) =
      (-1 : A) ^ a' * indexGradedCup σ a a' (fun x => d (α x)) β j +
        indexGradedCup σ a a' (fun x => σ (α x)) (fun x => d (β x)) j := by
  simp only [indexGradedCup, indexCup]
  rw [hd, map_ringHom_pow σ d hdσ, mul_assoc, ringHom_pow_comm σ]

end Graded

end MixedFujita
