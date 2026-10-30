/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.IndexSequenceHomogeneous

/-!
Additivity and Frobenius-semilinearity of the products of Deligne–Illusie cocycles (step 10).

The product of total index cochains of check 451 is additive in each factor and, for an
`R`-algebra `A` and an `R`-linear `σ`, compatible with scalars on each side
(`seqTotalMul_add_left`, `seqTotalMul_smul_right`, …); hence the product of a list is additive and
compatible with scalars in each entry (`seqTotalProd_append_cons_add`,
`seqTotalProd_append_cons_smul`). The degree-`1` Deligne–Illusie cocycle of check 452 is additive
and Frobenius-semilinear in the `1`-form, `φ¹(f ω) = f^p φ¹(ω)` (`diSeqCocycle_add`,
`diSeqCocycle_smul`, from checks 408 and 409), so the product `φ¹(ω_1) ⋆ ⋯ ⋆ φ¹(ω_b)` is additive
and Frobenius-semilinear in each `ω_i` (`diSeqProd_append_cons_add`,
`diSeqProd_append_cons_smul`): it is a multilinear map into the Frobenius twist, ready to be
antisymmetrized and lifted to `⋀^b`.
-/

@[expose] public section

namespace MixedFujita

universe u v w

section Linear

variable {J : Type*} {R : Type*} [CommRing R] {A : Type*} [Ring A] [Algebra R A] (σ : A →+* A)

omit [Algebra R A] in
theorem seqTotalMul_add_left (α α' β : ℕ → (ℕ → J) → A) :
    seqTotalMul σ (α + α') β = seqTotalMul σ α β + seqTotalMul σ α' β := by
  funext c s
  simp only [seqTotalMul, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

omit [Algebra R A] in
theorem seqTotalMul_add_right (α β β' : ℕ → (ℕ → J) → A) :
    seqTotalMul σ α (β + β') = seqTotalMul σ α β + seqTotalMul σ α β' := by
  funext c s
  simp only [seqTotalMul, Pi.add_apply, mul_add, Finset.sum_add_distrib]

variable (hσr : ∀ (r : R) (x : A), σ (r • x) = r • σ x)

include hσr in
theorem ringHom_pow_smul (k : ℕ) (r : R) (x : A) : (σ ^ k) (r • x) = r • (σ ^ k) x := by
  rw [RingHom.coe_pow]
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hσr]

include hσr in
theorem seqTotalMul_smul_left (r : R) (α β : ℕ → (ℕ → J) → A) :
    seqTotalMul σ (r • α) β = r • seqTotalMul σ α β := by
  funext c s
  simp only [seqTotalMul, Pi.smul_apply, ringHom_pow_smul σ hσr, smul_mul_assoc, Finset.smul_sum]

theorem seqTotalMul_smul_right (r : R) (α β : ℕ → (ℕ → J) → A) :
    seqTotalMul σ α (r • β) = r • seqTotalMul σ α β := by
  funext c s
  simp only [seqTotalMul, Pi.smul_apply, mul_smul_comm, Finset.smul_sum]

omit [Algebra R A] in
/-- **The product of a list is additive in each entry.** -/
theorem seqTotalProd_append_cons_add (l₁ l₂ : List (ℕ → (ℕ → J) → A))
    (α α' : ℕ → (ℕ → J) → A) :
    seqTotalProd σ (l₁ ++ (α + α') :: l₂) =
      seqTotalProd σ (l₁ ++ α :: l₂) + seqTotalProd σ (l₁ ++ α' :: l₂) := by
  induction l₁ with
  | nil => simp only [List.nil_append, seqTotalProd_cons, seqTotalMul_add_left]
  | cons γ l₁ ih => simp only [List.cons_append, seqTotalProd_cons, ih, seqTotalMul_add_right]

include hσr in
/-- **The product of a list is compatible with scalars in each entry.** -/
theorem seqTotalProd_append_cons_smul (l₁ l₂ : List (ℕ → (ℕ → J) → A)) (r : R)
    (α : ℕ → (ℕ → J) → A) :
    seqTotalProd σ (l₁ ++ (r • α) :: l₂) = r • seqTotalProd σ (l₁ ++ α :: l₂) := by
  induction l₁ with
  | nil => simp only [List.nil_append, seqTotalProd_cons, seqTotalMul_smul_left σ hσr]
  | cons γ l₁ ih => simp only [List.cons_append, seqTotalProd_cons, ih, seqTotalMul_smul_right]

end Linear

section DeligneIllusie

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S] {n : ℕ}
  (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale)
  {L : Type w} [CommRing L] (π : L →+* S) (hπ : Function.Surjective π) (p : ℕ) [hp : Fact p.Prime]
  [CharP K p] {J : Type*} (F : J → (L →+* L)) (hF : ∀ j x, π (F j x) = π x ^ p)
  (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z)

/-- **The degree-`1` Deligne–Illusie cocycle is additive in the `1`-form.** -/
theorem diSeqCocycle_add (ω ω' : Ω[S⁄K]) :
    diSeqCocycle y hy π hπ p F hF hker (ω + ω') =
      diSeqCocycle y hy π hπ p F hF hker ω + diSeqCocycle y hy π hπ p F hF hker ω' := by
  funext c s
  rcases c with _ | _ | c
  · simp only [diSeqCocycle, diCocycleP, Pi.add_apply, frobeniusLiftOneFormAux_add, map_add]
  · simp only [diSeqCocycle, diCocycleH, Pi.add_apply, frobeniusLiftHomotopyAux_add, map_add]
  · simp only [diSeqCocycle, Pi.add_apply, add_zero]

omit hp [CharP K p] in
/-- **The degree-`1` Deligne–Illusie cocycle is Frobenius-semilinear**: `φ¹(f ω) = f^p φ¹(ω)`. -/
theorem diSeqCocycle_smul (f : S) (ω : Ω[S⁄K]) :
    diSeqCocycle y hy π hπ p F hF hker (f • ω) = (f ^ p) • diSeqCocycle y hy π hπ p F hF hker ω := by
  funext c s
  rcases c with _ | _ | c
  · simp only [diSeqCocycle, diCocycleP, Pi.smul_apply, frobeniusLiftOneFormAux_smul, map_smul]
  · simp only [diSeqCocycle, diCocycleH, Pi.smul_apply, frobeniusLiftHomotopyAux_smul, map_mul,
      Algebra.smul_def]
  · simp only [diSeqCocycle, Pi.smul_apply, smul_zero]

/-- **The product of the Deligne–Illusie cocycles is additive in each `1`-form.** -/
theorem diSeqProd_append_cons_add (l₁ l₂ : List Ω[S⁄K]) (ω ω' : Ω[S⁄K]) :
    diSeqProd y hy π hπ p F hF hker (l₁ ++ (ω + ω') :: l₂) =
      diSeqProd y hy π hπ p F hF hker (l₁ ++ ω :: l₂) +
        diSeqProd y hy π hπ p F hF hker (l₁ ++ ω' :: l₂) := by
  simp only [diSeqProd, List.map_append, List.map_cons, diSeqCocycle_add]
  exact seqTotalProd_append_cons_add _ _ _ _ _

omit hp [CharP K p] in
/-- **The product of the Deligne–Illusie cocycles is Frobenius-semilinear in each `1`-form.** -/
theorem diSeqProd_append_cons_smul (l₁ l₂ : List Ω[S⁄K]) (f : S) (ω : Ω[S⁄K]) :
    diSeqProd y hy π hπ p F hF hker (l₁ ++ (f • ω) :: l₂) =
      (f ^ p) • diSeqProd y hy π hπ p F hF hker (l₁ ++ ω :: l₂) := by
  simp only [diSeqProd, List.map_append, List.map_cons, diSeqCocycle_smul]
  exact seqTotalProd_append_cons_smul _ (fun r x => exteriorInvolute_smul r x) _ _ _ _

end DeligneIllusie

end MixedFujita
