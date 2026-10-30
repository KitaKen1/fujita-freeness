/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.IndexSequenceCochain
public import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
The product of total index cochains and the graded Leibniz rule of the total differential
(step 10).

A total index cochain is a family `α : ℕ → (ℕ → J) → A` of sequence cochains (check 450), `α c`
being the component of Čech degree `c`. With an involution `σ` and a twisted derivation `d` as in
check 447 (on the exterior algebra of a chart: the grade involution and the de Rham differential,
check 448), the product is `(α ⋆ β)_c = Σ_{a + a' = c} (σ^{a'} ∘ α_a) ∪ β_{a'}` (`seqTotalMul`),
and the total differential is `D = Δ + ∂` with `(Δα)_0 = 0`, `(Δα)_{c+1} = δα_c`
(`seqTotalCechD`) and `(∂α)_c = (-1)^c d ∘ α_c` (`seqTotalDeRham`). With the sign twist
`(εα)_c = (-1)^c σ ∘ α_c` (`seqTotalSign`), both parts satisfy the Leibniz rule
`Δ(α ⋆ β) = Δα ⋆ β + εα ⋆ Δβ` and `∂(α ⋆ β) = ∂α ⋆ β + εα ⋆ ∂β` (the first from check 450 by
reindexing the antidiagonal, the second termwise from check 447), hence
`D(α ⋆ β) = Dα ⋆ β + εα ⋆ Dβ` (`seqTotalD_seqTotalMul`), and the product of two `D`-cocycles is a
`D`-cocycle (`seqTotalD_seqTotalMul_eq_zero`). The component of Čech degree `0` of a product is the
product of the components of degree `0` (`seqTotalMul_zero`).
-/

@[expose] public section

namespace MixedFujita

universe u v

section Total

variable {J : Type u} {A : Type v} [Ring A] (σ : A →+* A)

/-- **The product of total index cochains**: the component of Čech degree `c` is
`Σ_{a + a' = c} (σ^{a'} ∘ α_a) ∪ β_{a'}`. -/
def seqTotalMul (α β : ℕ → (ℕ → J) → A) (c : ℕ) (s : ℕ → J) : A :=
  ∑ x ∈ Finset.antidiagonal c, (σ ^ x.2) (α x.1 s) * β x.2 (seqShift x.1 s)

/-- The Čech part of the total differential: `(Δα)_0 = 0` and `(Δα)_{c+1} = δα_c`. -/
def seqTotalCechD (α : ℕ → (ℕ → J) → A) : ℕ → (ℕ → J) → A
  | 0 => fun _ => 0
  | c + 1 => seqCechD c (α c)

/-- The de Rham part of the total differential: `(∂α)_c = (-1)^c d ∘ α_c`. -/
def seqTotalDeRham (d : A →+ A) (α : ℕ → (ℕ → J) → A) (c : ℕ) (s : ℕ → J) : A :=
  (-1 : A) ^ c * d (α c s)

/-- **The total differential** `D = Δ + ∂` of a total index cochain. -/
def seqTotalD (d : A →+ A) (α : ℕ → (ℕ → J) → A) (c : ℕ) (s : ℕ → J) : A :=
  seqTotalCechD α c s + seqTotalDeRham d α c s

/-- The sign twist `(εα)_c = (-1)^c σ ∘ α_c`. -/
def seqTotalSign (α : ℕ → (ℕ → J) → A) (c : ℕ) (s : ℕ → J) : A :=
  (-1 : A) ^ c * σ (α c s)

/-- The unit total cochain: `1` in Čech degree `0`. -/
def seqTotalOne : ℕ → (ℕ → J) → A
  | 0 => fun _ => 1
  | _ + 1 => fun _ => 0

/-- **The product of a list of total index cochains.** -/
def seqTotalProd (l : List (ℕ → (ℕ → J) → A)) : ℕ → (ℕ → J) → A :=
  l.foldr (seqTotalMul σ) seqTotalOne

theorem seqShift_zero (s : ℕ → J) : seqShift 0 s = s :=
  funext fun _ => rfl

/-- The component of Čech degree `0` of a product. -/
theorem seqTotalMul_zero (α β : ℕ → (ℕ → J) → A) (s : ℕ → J) :
    seqTotalMul σ α β 0 s = α 0 s * β 0 s := by
  simp only [seqTotalMul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton, RingHom.coe_pow,
    Function.iterate_zero, id_eq, seqShift_zero]

theorem seqSupported_seqTotalMul {α β : ℕ → (ℕ → J) → A} (hα : ∀ a, SeqSupported a (α a))
    (hβ : ∀ a, SeqSupported a (β a)) (c : ℕ) : SeqSupported c (seqTotalMul σ α β c) := by
  intro s t h
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' : x.1 + x.2 = c := Finset.mem_antidiagonal.mp hx
  rw [hα x.1 s t fun i hi => h i (by omega),
    hβ x.2 (seqShift x.1 s) (seqShift x.1 t) fun i hi => h (i + x.1) (by omega)]

theorem seqSupported_seqTotalSign {α : ℕ → (ℕ → J) → A} (hα : ∀ a, SeqSupported a (α a))
    (c : ℕ) : SeqSupported c (seqTotalSign σ α c) :=
  fun s t h => by rw [seqTotalSign, seqTotalSign, hα c s t h]

theorem seqSupported_seqTotalD (d : A →+ A) {α : ℕ → (ℕ → J) → A}
    (hα : ∀ a, SeqSupported a (α a)) (c : ℕ) : SeqSupported c (seqTotalD d α c) := by
  intro s t h
  cases c with
  | zero => simp only [seqTotalD, seqTotalCechD, seqTotalDeRham, hα 0 s t h]
  | succ c =>
    simp only [seqTotalD, seqTotalCechD, seqTotalDeRham, hα (c + 1) s t h,
      seqSupported_seqCechD (hα c) s t h]

omit [Ring A] in
theorem seqSupported_seqTotalOne [Ring A] (c : ℕ) :
    SeqSupported c (seqTotalOne (J := J) (A := A) c) := by
  intro s t _
  cases c <;> rfl

theorem seqTotalProd_nil : seqTotalProd σ ([] : List (ℕ → (ℕ → J) → A)) = seqTotalOne := rfl

theorem seqTotalProd_cons (α : ℕ → (ℕ → J) → A) (l : List (ℕ → (ℕ → J) → A)) :
    seqTotalProd σ (α :: l) = seqTotalMul σ α (seqTotalProd σ l) := rfl

/-- The component of Čech degree `0` of a product of a list is the product of the components. -/
theorem seqTotalProd_zero (l : List (ℕ → (ℕ → J) → A)) (s : ℕ → J) :
    seqTotalProd σ l 0 s = (l.map fun α => α 0 s).prod := by
  induction l with
  | nil => rfl
  | cons α l ih => rw [seqTotalProd_cons, seqTotalMul_zero, ih, List.map_cons, List.prod_cons]

theorem seqSupported_seqTotalProd (l : List (ℕ → (ℕ → J) → A))
    (hl : ∀ α ∈ l, ∀ a, SeqSupported a (α a)) (c : ℕ) :
    SeqSupported c (seqTotalProd σ l c) := by
  induction l generalizing c with
  | nil => exact seqSupported_seqTotalOne c
  | cons α l ih =>
    rw [seqTotalProd_cons]
    exact seqSupported_seqTotalMul σ (hl α List.mem_cons_self)
      (fun a => ih (fun β hβ => hl β (List.mem_cons_of_mem _ hβ)) a) c

variable (hσ : ∀ x, σ (σ x) = x)

include hσ in
/-- **The Leibniz rule of the Čech part**: `Δ(α ⋆ β) = Δα ⋆ β + εα ⋆ Δβ`. -/
theorem seqTotalCechD_seqTotalMul {α : ℕ → (ℕ → J) → A} (hα : ∀ a, SeqSupported a (α a))
    (β : ℕ → (ℕ → J) → A) (c : ℕ) (s : ℕ → J) :
    seqTotalCechD (seqTotalMul σ α β) c s =
      seqTotalMul σ (seqTotalCechD α) β c s +
        seqTotalMul σ (seqTotalSign σ α) (seqTotalCechD β) c s := by
  cases c with
  | zero =>
    simp only [seqTotalMul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton, seqTotalCechD,
      map_zero, zero_mul, mul_zero, add_zero]
  | succ c =>
    have hL : seqTotalCechD (seqTotalMul σ α β) (c + 1) s =
        ∑ x ∈ Finset.antidiagonal c,
          ((σ ^ x.2) (seqCechD x.1 (α x.1) s) * β x.2 (seqShift (x.1 + 1) s) +
            (-1 : A) ^ x.1 * ((σ ^ x.2) (α x.1 s) * seqCechD x.2 (β x.2) (seqShift x.1 s))) := by
      show seqCechD c (fun t => ∑ x ∈ Finset.antidiagonal c,
        (σ ^ x.2) (α x.1 t) * β x.2 (seqShift x.1 t)) s = _
      rw [seqCechD_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      obtain ⟨a, a'⟩ := x
      have hc : a + a' = c := Finset.mem_antidiagonal.mp hx
      subst hc
      have h := seqCechD_seqCup (seqSupported_comp (hα a) fun y => (σ ^ a') y) (β a') a' s
      rw [seqCup, seqCup, seqCechD_comp_ringHom] at h
      exact h
    have hR1 : seqTotalMul σ (seqTotalCechD α) β (c + 1) s =
        ∑ x ∈ Finset.antidiagonal c,
          (σ ^ x.2) (seqCechD x.1 (α x.1) s) * β x.2 (seqShift (x.1 + 1) s) := by
      rw [seqTotalMul, Finset.Nat.sum_antidiagonal_succ]
      simp only [seqTotalCechD, map_zero, zero_mul, zero_add]
    have hR2 : seqTotalMul σ (seqTotalSign σ α) (seqTotalCechD β) (c + 1) s =
        ∑ x ∈ Finset.antidiagonal c,
          (-1 : A) ^ x.1 * ((σ ^ x.2) (α x.1 s) * seqCechD x.2 (β x.2) (seqShift x.1 s)) := by
      rw [seqTotalMul, Finset.Nat.sum_antidiagonal_succ']
      simp only [seqTotalCechD, mul_zero, zero_add]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [seqTotalSign, map_mul, map_pow, map_neg, map_one, RingHom.coe_pow, RingHom.coe_pow,
        Function.iterate_succ_apply, hσ, mul_assoc]
    rw [hL, hR1, hR2, Finset.sum_add_distrib]

variable (d : A →+ A) (hd : ∀ x y, d (x * y) = d x * y + σ x * d y)
  (hdσ : ∀ x, d (σ x) = -σ (d x))

omit hσ in
include hd hdσ in
/-- **The Leibniz rule of the de Rham part**: `∂(α ⋆ β) = ∂α ⋆ β + εα ⋆ ∂β`. -/
theorem seqTotalDeRham_seqTotalMul (α β : ℕ → (ℕ → J) → A) (c : ℕ) (s : ℕ → J) :
    seqTotalDeRham d (seqTotalMul σ α β) c s =
      seqTotalMul σ (seqTotalDeRham d α) β c s +
        seqTotalMul σ (seqTotalSign σ α) (seqTotalDeRham d β) c s := by
  simp only [seqTotalDeRham, seqTotalMul, seqTotalSign, map_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  obtain ⟨a, a'⟩ := x
  have hc : a + a' = c := Finset.mem_antidiagonal.mp hx
  subst hc
  have hv : ∀ y : A, (-1 : A) ^ a' * y = y * (-1 : A) ^ a' :=
    fun y => ((Commute.neg_one_left y).pow_left a').eq
  have hvv : (-1 : A) ^ a' * (-1 : A) ^ a' = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  dsimp only
  rw [hd, map_ringHom_pow σ d hdσ, ringHom_pow_comm σ, map_mul, map_mul, map_pow, map_neg,
    map_one, pow_add]
  set X := (σ ^ a') (d (α a s))
  set Y := β a' (seqShift a s)
  set Z := (σ ^ a') (σ (α a s))
  set W := d (β a' (seqShift a s))
  calc (-1 : A) ^ a * (-1 : A) ^ a' * ((-1 : A) ^ a' * X * Y + Z * W)
      = (-1 : A) ^ a * ((-1 : A) ^ a' * (-1 : A) ^ a') * X * Y +
          (-1 : A) ^ a * ((-1 : A) ^ a' * Z * W) := by noncomm_ring
    _ = (-1 : A) ^ a * X * Y + (-1 : A) ^ a * Z * ((-1 : A) ^ a' * W) := by
      rw [hvv, hv Z]
      noncomm_ring

include hσ hd hdσ in
/-- **The graded Leibniz rule of the total differential**: `D(α ⋆ β) = Dα ⋆ β + εα ⋆ Dβ`. -/
theorem seqTotalD_seqTotalMul {α : ℕ → (ℕ → J) → A} (hα : ∀ a, SeqSupported a (α a))
    (β : ℕ → (ℕ → J) → A) (c : ℕ) (s : ℕ → J) :
    seqTotalD d (seqTotalMul σ α β) c s =
      seqTotalMul σ (seqTotalD d α) β c s +
        seqTotalMul σ (seqTotalSign σ α) (seqTotalD d β) c s := by
  have e1 : seqTotalMul σ (seqTotalD d α) β c s =
      seqTotalMul σ (seqTotalCechD α) β c s + seqTotalMul σ (seqTotalDeRham d α) β c s := by
    simp only [seqTotalMul, seqTotalD, map_add, add_mul, Finset.sum_add_distrib]
  have e2 : seqTotalMul σ (seqTotalSign σ α) (seqTotalD d β) c s =
      seqTotalMul σ (seqTotalSign σ α) (seqTotalCechD β) c s +
        seqTotalMul σ (seqTotalSign σ α) (seqTotalDeRham d β) c s := by
    simp only [seqTotalMul, seqTotalD, mul_add, Finset.sum_add_distrib]
  rw [seqTotalD, seqTotalCechD_seqTotalMul σ hσ hα β c s,
    seqTotalDeRham_seqTotalMul σ d hd hdσ α β c s, e1, e2]
  abel

include hσ hd hdσ in
/-- **The product of two `D`-cocycles is a `D`-cocycle.** -/
theorem seqTotalD_seqTotalMul_eq_zero {α β : ℕ → (ℕ → J) → A} (hα : ∀ a, SeqSupported a (α a))
    (hDα : ∀ c s, seqTotalD d α c s = 0) (hDβ : ∀ c s, seqTotalD d β c s = 0) (c : ℕ)
    (s : ℕ → J) : seqTotalD d (seqTotalMul σ α β) c s = 0 := by
  rw [seqTotalD_seqTotalMul σ hσ d hd hdσ hα β c s]
  simp only [seqTotalMul, hDα, hDβ, map_zero, zero_mul, mul_zero, Finset.sum_const_zero,
    add_zero]

include hd in
theorem seqTotalD_seqTotalOne (c : ℕ) (s : ℕ → J) : seqTotalD d seqTotalOne c s = 0 := by
  have h1 : d 1 = 0 := by
    have h := hd 1 1
    simp only [mul_one, map_one σ, one_mul] at h
    exact add_left_cancel (h.symm.trans (add_zero (d 1)).symm)
  cases c with
  | zero => simp only [seqTotalD, seqTotalCechD, seqTotalDeRham, seqTotalOne, h1, mul_zero, add_zero]
  | succ c =>
    cases c with
    | zero =>
      simp only [seqTotalD, seqTotalCechD, seqTotalDeRham, seqTotalOne, seqCechD, map_zero,
        mul_zero, add_zero, Finset.sum_range_succ, Finset.sum_range_zero]
      simp
    | succ c =>
      simp only [seqTotalD, seqTotalCechD, seqTotalDeRham, seqTotalOne, seqCechD, map_zero,
        mul_zero, add_zero, Finset.sum_const_zero]

include hσ hd hdσ in
/-- **A product of `D`-cocycles is a `D`-cocycle.** -/
theorem seqTotalD_seqTotalProd (l : List (ℕ → (ℕ → J) → A))
    (hl : ∀ α ∈ l, (∀ a, SeqSupported a (α a)) ∧ ∀ c s, seqTotalD d α c s = 0) (c : ℕ)
    (s : ℕ → J) : seqTotalD d (seqTotalProd σ l) c s = 0 := by
  induction l generalizing c s with
  | nil => exact seqTotalD_seqTotalOne σ d hd c s
  | cons α l ih =>
    rw [seqTotalProd_cons]
    exact seqTotalD_seqTotalMul_eq_zero σ hσ d hd hdσ (hl α List.mem_cons_self).1
      (hl α List.mem_cons_self).2 (ih fun β hβ => hl β (List.mem_cons_of_mem _ hβ)) c s

end Total

end MixedFujita
