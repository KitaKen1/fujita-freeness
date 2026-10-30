/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FrobeniusLiftHomotopy

/-!
The cocycle identity of the Deligne–Illusie homotopies (step 10).

For three Frobenius lifts `F₁, F₂, F₃` on the same lift modulo `p²` (check 407), the homotopies
`h_{ij} = (F_j - F_i)/p` of check 409 satisfy `h₁₃ = h₁₂ + h₂₃` and `h_{ii} = 0`, hence
`h_{ji} = -h_{ij}`: for the differences on `L` (`frobeniusLiftDifference_cocycle`,
`frobeniusLiftDifference_self`), for the homotopies on `S` (`frobeniusLiftHomotopy_cocycle`,
`frobeniusLiftHomotopy_self`, `frobeniusLiftHomotopy_symm`), and on the `1`-forms of an étale
chart (`frobeniusLiftHomotopyAux_cocycle`). These are the cocycle relations of the degree-`1`
Deligne–Illusie map `(φ_i, h_{ij})` on the Čech nerve.
-/

@[expose] public section

namespace MixedFujita

universe u v w

section Difference

variable {S : Type v} [CommRing S] {L : Type w} [CommRing L] (π : L →+* S) (p : ℕ)
  (F₁ F₂ F₃ : L →+* L) (hF₁ : ∀ x, π (F₁ x) = π x ^ p) (hF₂ : ∀ x, π (F₂ x) = π x ^ p)
  (hF₃ : ∀ x, π (F₃ x) = π x ^ p) (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z)
  (hann : ∀ z, (p : L) * z = 0 → π z = 0)

include hann in
/-- **The cocycle identity** `(F₃ - F₁)/p = (F₂ - F₁)/p + (F₃ - F₂)/p`. -/
theorem frobeniusLiftDifference_cocycle (x : L) :
    frobeniusLiftDifference π p F₁ F₃ hF₁ hF₃ hker x =
      frobeniusLiftDifference π p F₁ F₂ hF₁ hF₂ hker x +
        frobeniusLiftDifference π p F₂ F₃ hF₂ hF₃ hker x := by
  have h12 := frobeniusLiftDifference_spec π p F₁ F₂ hF₁ hF₂ hker x
  have h23 := frobeniusLiftDifference_spec π p F₂ F₃ hF₂ hF₃ hker x
  have h : F₃ x - F₁ x = (p : L) *
      (Classical.choose (hker (F₂ x - F₁ x) (frobeniusLift_sub_lift_mem π p F₁ F₂ hF₁ hF₂ x)) +
        Classical.choose (hker (F₃ x - F₂ x) (frobeniusLift_sub_lift_mem π p F₂ F₃ hF₂ hF₃ x))) := by
    rw [mul_add, ← h12, ← h23]
    ring
  rw [frobeniusLiftDifference_eq π p F₁ F₃ hF₁ hF₃ hker hann h, map_add]
  rfl

include hann in
theorem frobeniusLiftDifference_self (x : L) :
    frobeniusLiftDifference π p F₁ F₁ hF₁ hF₁ hker x = 0 := by
  have h : F₁ x - F₁ x = (p : L) * 0 := by rw [sub_self, mul_zero]
  rw [frobeniusLiftDifference_eq π p F₁ F₁ hF₁ hF₁ hker hann h, map_zero]

end Difference

section Homotopy

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S] {L : Type w} [CommRing L]
  (π : L →+* S) (hπ : Function.Surjective π) (p : ℕ)
  (F₁ F₂ F₃ : L →+* L) (hF₁ : ∀ x, π (F₁ x) = π x ^ p) (hF₂ : ∀ x, π (F₂ x) = π x ^ p)
  (hF₃ : ∀ x, π (F₃ x) = π x ^ p) (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z)
  (hann : ∀ z, (p : L) * z = 0 → π z = 0)

include hann in
/-- **The cocycle identity of the homotopies** `h₁₃ = h₁₂ + h₂₃`. -/
theorem frobeniusLiftHomotopy_cocycle (a : S) :
    frobeniusLiftHomotopy π hπ p F₁ F₃ hF₁ hF₃ hker a =
      frobeniusLiftHomotopy π hπ p F₁ F₂ hF₁ hF₂ hker a +
        frobeniusLiftHomotopy π hπ p F₂ F₃ hF₂ hF₃ hker a :=
  frobeniusLiftDifference_cocycle π p F₁ F₂ F₃ hF₁ hF₂ hF₃ hker hann _

include hann in
theorem frobeniusLiftHomotopy_self (a : S) :
    frobeniusLiftHomotopy π hπ p F₁ F₁ hF₁ hF₁ hker a = 0 :=
  frobeniusLiftDifference_self π p F₁ hF₁ hker hann _

include hann in
/-- `h₂₁ = -h₁₂`. -/
theorem frobeniusLiftHomotopy_symm (a : S) :
    frobeniusLiftHomotopy π hπ p F₂ F₁ hF₂ hF₁ hker a =
      -frobeniusLiftHomotopy π hπ p F₁ F₂ hF₁ hF₂ hker a := by
  have h := frobeniusLiftHomotopy_cocycle π hπ p F₁ F₂ F₁ hF₁ hF₂ hF₁ hker hann a
  rw [frobeniusLiftHomotopy_self π hπ p F₁ hF₁ hker hann] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

end Homotopy

section Chart

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S] {n : ℕ}
  (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale)
  {L : Type w} [CommRing L] (π : L →+* S) (hπ : Function.Surjective π) (p : ℕ) [hp : Fact p.Prime]
  [CharP K p] (F₁ F₂ F₃ : L →+* L) (hF₁ : ∀ x, π (F₁ x) = π x ^ p)
  (hF₂ : ∀ x, π (F₂ x) = π x ^ p) (hF₃ : ∀ x, π (F₃ x) = π x ^ p)
  (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z)
  (hann : ∀ z, (p : L) * z = 0 → π z = 0)

omit hp [CharP K p] in
include hann in
/-- **The cocycle identity on `1`-forms** of an étale chart. -/
theorem frobeniusLiftHomotopyAux_cocycle (ω : Ω[S⁄K]) :
    frobeniusLiftHomotopyAux y hy π hπ p F₁ F₃ hF₁ hF₃ hker ω =
      frobeniusLiftHomotopyAux y hy π hπ p F₁ F₂ hF₁ hF₂ hker ω +
        frobeniusLiftHomotopyAux y hy π hπ p F₂ F₃ hF₂ hF₃ hker ω := by
  simp only [frobeniusLiftHomotopyAux,
    frobeniusLiftHomotopy_cocycle π hπ p F₁ F₂ F₃ hF₁ hF₂ hF₃ hker hann, mul_add,
    Finset.sum_add_distrib]

end Chart

end MixedFujita
