/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.DeligneIllusieSequenceCocycle

/-!
Homogeneity of total index cochains with values in an exterior algebra (step 10).

A total index cochain `α` with values in `⋀_R M` is homogeneous of total degree `t`
(`SeqTotalHomogeneous t α`) if its component of Čech degree `a` lies in `⋀^{t - a}` and vanishes
for `a > t`. For a ring endomorphism `σ` preserving every `⋀^i` (such as the grade involution,
`involute_mem_exteriorPower`), the product of check 451 adds total degrees
(`seqTotalHomogeneous_seqTotalMul`), the unit has total degree `0`, and a product of a list of
cochains of total degree `1` has total degree the length of the list. The degree-`1`
Deligne–Illusie cocycle of check 452 has total degree `1` (`seqTotalHomogeneous_diSeqCocycle`), so
the component of Čech degree `a` of `φ¹(ω_1) ⋆ ⋯ ⋆ φ¹(ω_b)` is a `(b - a)`-form
(`seqTotalHomogeneous_diSeqProd`): these are the components `Ψ_{b → b - a}` of the
Deligne–Illusie map.
-/

@[expose] public section

namespace MixedFujita

universe u v w

section Homogeneous

variable {J : Type*} {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- A total index cochain is **homogeneous of total degree `t`**: its component of Čech degree `a`
lies in `⋀^{t - a}` and vanishes for `a > t`. -/
def SeqTotalHomogeneous (t : ℕ) (α : ℕ → (ℕ → J) → ExteriorAlgebra R M) : Prop :=
  ∀ a s, α a s ∈ ⋀[R]^(t - a) M ∧ (t < a → α a s = 0)

theorem mul_mem_exteriorPower {i j : ℕ}
    {x z : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^i M) (hz : z ∈ ⋀[R]^j M) :
    x * z ∈ ⋀[R]^(i + j) M := by
  rw [ExteriorAlgebra.exteriorPower, pow_add]
  exact Submodule.mul_mem_mul hx hz

theorem algebraMap_mem_exteriorPower_zero (r : R) :
    algebraMap R (ExteriorAlgebra R M) r ∈ ⋀[R]^0 M := by
  rw [ExteriorAlgebra.exteriorPower, pow_zero]
  exact Submodule.algebraMap_mem r

/-- The grade involution preserves every `⋀^i`. -/
theorem involute_mem_exteriorPower {i : ℕ}
    {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^i M) :
    CliffordAlgebra.involute (Q := (0 : QuadraticForm R M)) x ∈ ⋀[R]^i M := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [AlgHom.commutes]
    exact algebraMap_mem_exteriorPower_zero r
  | add x z i _ _ hx hz =>
    rw [map_add]
    exact Submodule.add_mem _ hx hz
  | mem_mul m hm i x hx ih =>
    obtain ⟨v, rfl⟩ := hm
    rw [map_mul, CliffordAlgebra.involute_ι, ← map_neg]
    have h1 : ExteriorAlgebra.ι R (-v) ∈ ⋀[R]^1 M := by
      rw [ExteriorAlgebra.exteriorPower, pow_one]
      exact LinearMap.mem_range_self _ _
    have h := mul_mem_exteriorPower h1 ih
    rwa [Nat.add_comm] at h

variable (σ : ExteriorAlgebra R M →+* ExteriorAlgebra R M)
  (hσ : ∀ (i : ℕ) (x : ExteriorAlgebra R M), x ∈ ⋀[R]^i M → σ x ∈ ⋀[R]^i M)

include hσ in
theorem ringHom_pow_mem_exteriorPower (k i : ℕ) {x : ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^i M) : (σ ^ k) x ∈ ⋀[R]^i M := by
  rw [RingHom.coe_pow]
  induction k with
  | zero => exact hx
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact hσ i _ ih

include hσ in
/-- **The product adds total degrees.** -/
theorem seqTotalHomogeneous_seqTotalMul {t t' : ℕ} {α β : ℕ → (ℕ → J) → ExteriorAlgebra R M}
    (hα : SeqTotalHomogeneous t α) (hβ : SeqTotalHomogeneous t' β) :
    SeqTotalHomogeneous (t + t') (seqTotalMul σ α β) := by
  intro c s
  have key : ∀ x ∈ Finset.antidiagonal c,
      (σ ^ x.2) (α x.1 s) * β x.2 (seqShift x.1 s) ∈ ⋀[R]^(t + t' - c) M ∧
        (t + t' < c → (σ ^ x.2) (α x.1 s) * β x.2 (seqShift x.1 s) = 0) := by
    intro x hx
    have hc : x.1 + x.2 = c := Finset.mem_antidiagonal.mp hx
    by_cases h1 : t < x.1
    · rw [(hα x.1 s).2 h1, map_zero, zero_mul]
      exact ⟨Submodule.zero_mem _, fun _ => rfl⟩
    by_cases h2 : t' < x.2
    · rw [(hβ x.2 (seqShift x.1 s)).2 h2, mul_zero]
      exact ⟨Submodule.zero_mem _, fun _ => rfl⟩
    refine ⟨?_, fun h => absurd h (by omega)⟩
    have e : t + t' - c = (t - x.1) + (t' - x.2) := by omega
    rw [e]
    exact mul_mem_exteriorPower (ringHom_pow_mem_exteriorPower σ hσ _ _ (hα x.1 s).1)
      (hβ x.2 _).1
  exact ⟨Submodule.sum_mem _ fun x hx => (key x hx).1,
    fun h => Finset.sum_eq_zero fun x hx => (key x hx).2 h⟩

theorem seqTotalHomogeneous_seqTotalOne :
    SeqTotalHomogeneous 0 (seqTotalOne (J := J) (A := ExteriorAlgebra R M)) := by
  intro a s
  cases a with
  | zero =>
    refine ⟨?_, fun h => absurd h (lt_irrefl 0)⟩
    have h := algebraMap_mem_exteriorPower_zero (R := R) (M := M) 1
    rwa [map_one] at h
  | succ a => exact ⟨Submodule.zero_mem _, fun _ => rfl⟩

include hσ in
/-- **A product of a list of cochains of total degree `1` has total degree the length.** -/
theorem seqTotalHomogeneous_seqTotalProd (l : List (ℕ → (ℕ → J) → ExteriorAlgebra R M))
    (hl : ∀ α ∈ l, SeqTotalHomogeneous 1 α) :
    SeqTotalHomogeneous l.length (seqTotalProd σ l) := by
  induction l with
  | nil => exact seqTotalHomogeneous_seqTotalOne
  | cons α l ih =>
    rw [seqTotalProd_cons, List.length_cons, Nat.add_comm]
    exact seqTotalHomogeneous_seqTotalMul σ hσ (hl α List.mem_cons_self)
      (ih fun β hβ => hl β (List.mem_cons_of_mem _ hβ))

end Homogeneous

section DeligneIllusie

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S] {n : ℕ}
  (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale)
  {L : Type w} [CommRing L] (π : L →+* S) (hπ : Function.Surjective π) (p : ℕ) [hp : Fact p.Prime]
  [CharP K p] {J : Type*} (F : J → (L →+* L)) (hF : ∀ j x, π (F j x) = π x ^ p)
  (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z)

omit hp [CharP K p] in
/-- **The degree-`1` Deligne–Illusie cocycle has total degree `1`.** -/
theorem seqTotalHomogeneous_diSeqCocycle (ω : Ω[S⁄K]) :
    SeqTotalHomogeneous 1 (diSeqCocycle y hy π hπ p F hF hker ω) := by
  intro a s
  rcases a with _ | _ | a
  · refine ⟨?_, fun h => absurd h (by omega)⟩
    show ExteriorAlgebra.ι S _ ∈ ⋀[S]^1 Ω[S⁄K]
    rw [ExteriorAlgebra.exteriorPower, pow_one]
    exact LinearMap.mem_range_self _ _
  · exact ⟨algebraMap_mem_exteriorPower_zero _, fun h => absurd h (lt_irrefl 1)⟩
  · exact ⟨Submodule.zero_mem _, fun _ => rfl⟩

omit hp [CharP K p] in
/-- **The component of Čech degree `a` of `φ¹(ω_1) ⋆ ⋯ ⋆ φ¹(ω_b)` is a `(b - a)`-form**, and it
vanishes for `a > b`. -/
theorem seqTotalHomogeneous_diSeqProd (ωs : List Ω[S⁄K]) :
    SeqTotalHomogeneous ωs.length (diSeqProd y hy π hπ p F hF hker ωs) := by
  have h := seqTotalHomogeneous_seqTotalProd (exteriorInvolute K S)
    (fun _ _ hx => involute_mem_exteriorPower hx)
    (ωs.map (diSeqCocycle y hy π hπ p F hF hker)) (fun α hα => by
      obtain ⟨ω, -, rfl⟩ := List.mem_map.mp hα
      exact seqTotalHomogeneous_diSeqCocycle y hy π hπ p F hF hker ω)
  rwa [List.length_map] at h

end DeligneIllusie

end MixedFujita
