/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.StrictTransformHyperplaneModel

/-!
The strict transform of a hypersurface is birational to it (step 9, the adjunction step of the
restriction theorem).

Let μ : A → C be an injective birational map of domains and P a prime of A whose localization is
a valuation ring, such as the discrete valuation ring of A at the generic point of the
hypersurface H = V(P). If π : C → B is a map to a domain whose kernel contracts to P, as for the
strict transform H' = Spec B, which maps onto H generically, then every c ∈ C is a fraction
μ(a)/μ(t) with t ∉ P (`exists_mul_eq_of_valuationRing`): write c = μ(r)/μ(s); in the valuation
ring A_P either s divides r, or r divides s by an element of P, and in the second case some
t ∉ P with μ(t) = c μ(a) and a ∈ P would lie in the kernel of π ∘ μ. Hence A/P → B is injective
and birational when B is birational over C (`birational_of_valuationRing`), which supplies the
injectivity and birationality hypotheses of the strict transform model of check-328 from the
local ring of the hyperplane (`strictTransformHyperplaneMap_injective_birational`).
-/

@[expose] public section

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section Birational

variable {A C B : Type*} [CommRing A] [IsDomain A] [CommRing C] [IsDomain C] [CommRing B]
  [IsDomain B]

omit [IsDomain B] in
/-- Every element of C is a fraction μ(a)/μ(t) with t ∉ P, if A_P is a valuation ring and the
kernel of π ∘ μ is P. -/
theorem exists_mul_eq_of_valuationRing (μ : A →+* C) (hμ : Function.Injective μ)
    (hbir : ∀ c : C, ∃ r s : A, s ≠ 0 ∧ μ s * c = μ r) (P : Ideal A) [P.IsPrime]
    [ValuationRing (Localization.AtPrime P)] (π : C →+* B)
    (hker : ∀ a : A, π (μ a) = 0 ↔ a ∈ P) (c : C) :
    ∃ a t : A, t ∉ P ∧ μ t * c = μ a := by
  obtain ⟨r, s, hs, hrs⟩ := hbir c
  have hμs : μ s ≠ 0 := fun h0 => hs (hμ (h0.trans (map_zero μ).symm))
  have hinj : Function.Injective (algebraMap A (Localization.AtPrime P)) :=
    IsLocalization.injective (Localization.AtPrime P) P.primeCompl_le_nonZeroDivisors
  obtain ⟨e, he⟩ := ValuationRing.cond (algebraMap A (Localization.AtPrime P) r)
    (algebraMap A (Localization.AtPrime P) s)
  obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl e
  have ht : (t : A) ∉ P := t.2
  rcases he with he | he
  · -- r a = s t
    have h1 : r * a = s * t := by
      apply hinj
      have h := congrArg (· * algebraMap A (Localization.AtPrime P) (t : A)) he
      simp only at h
      rw [mul_assoc, IsLocalization.mk'_spec] at h
      rw [map_mul, map_mul, h]
    have h1' : μ r * μ a = μ s * μ t := by
      have h := congrArg μ h1
      simpa only [map_mul] using h
    by_cases ha : a ∈ P
    · exfalso
      apply ht
      rw [← hker]
      have h3 : μ t = c * μ a := by
        apply mul_right_cancel₀ hμs
        linear_combination -h1' - μ a * hrs
      rw [h3, map_mul, (hker a).mpr ha, mul_zero]
    · refine ⟨t, a, ha, ?_⟩
      apply mul_left_cancel₀ hμs
      linear_combination μ a * hrs + h1'
  · -- s a = r t
    have h1 : s * a = r * t := by
      apply hinj
      have h := congrArg (· * algebraMap A (Localization.AtPrime P) (t : A)) he
      simp only at h
      rw [mul_assoc, IsLocalization.mk'_spec] at h
      rw [map_mul, map_mul, h]
    have h1' : μ s * μ a = μ r * μ t := by
      have h := congrArg μ h1
      simpa only [map_mul] using h
    refine ⟨a, t, ht, ?_⟩
    apply mul_left_cancel₀ hμs
    linear_combination μ t * hrs - h1'

/-- A/P → B is injective and birational, if A_P is a valuation ring, the kernel of π ∘ μ is P and
B is birational over C. -/
theorem birational_of_valuationRing (μ : A →+* C) (hμ : Function.Injective μ)
    (hbir : ∀ c : C, ∃ r s : A, s ≠ 0 ∧ μ s * c = μ r) (P : Ideal A) [P.IsPrime]
    [ValuationRing (Localization.AtPrime P)] (π : C →+* B)
    (hker : ∀ a : A, π (μ a) = 0 ↔ a ∈ P) (hπ : ∀ b : B, ∃ c d : C, π d ≠ 0 ∧ π d * b = π c)
    (b : B) : ∃ r s : A, s ∉ P ∧ π (μ s) * b = π (μ r) := by
  obtain ⟨c, d, hd, hb⟩ := hπ b
  obtain ⟨a₁, t₁, ht₁, h₁⟩ := exists_mul_eq_of_valuationRing μ hμ hbir P π hker c
  obtain ⟨a₂, t₂, ht₂, h₂⟩ := exists_mul_eq_of_valuationRing μ hμ hbir P π hker d
  have hπt₂ : π (μ t₂) ≠ 0 := fun h0 => ht₂ ((hker t₂).mp h0)
  have ha₂ : a₂ ∉ P := by
    intro ha
    have h0 : π (μ a₂) = 0 := (hker a₂).mpr ha
    rw [← h₂, map_mul] at h0
    exact mul_ne_zero hπt₂ hd h0
  refine ⟨a₁ * t₂, t₁ * a₂, fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim ht₁ ha₂, ?_⟩
  have e₁ := congrArg π h₁
  have e₂ := congrArg π h₂
  simp only [map_mul] at e₁ e₂ ⊢
  linear_combination (-(π (μ t₁)) * b) * e₂ + (π (μ t₁) * π (μ t₂)) * hb + π (μ t₂) * e₁

end Birational

section StrictTransform

universe u

variable {K : Type u} [Field K] {N : ℕ} {A C B : Type u} [CommRing A] [IsDomain A] [Algebra K A]
  [CommRing C] [IsDomain C] [Algebra K C] [CommRing B] [IsDomain B] [Algebra K B]

/-- The strict transform model of check-328 is injective and birational over the hyperplane when
the local ring of A at x_0 = 0 is a valuation ring and the strict transform maps onto the
hyperplane generically. -/
theorem strictTransformHyperplaneMap_injective_birational
    (φ : MvPolynomial (Fin (N + 1)) K →ₐ[K] A) (y : MvPolynomial (Fin (N + 1)) K →ₐ[K] C)
    (μ : A →ₐ[K] C) (hμ : Function.Injective μ)
    (hbir : ∀ c : C, ∃ r s : A, s ≠ 0 ∧ μ s * c = μ r) (w : C)
    (hw : μ (φ (MvPolynomial.X 0)) = y (MvPolynomial.X 0) * w)
    [(Ideal.span {φ (MvPolynomial.X 0)}).IsPrime]
    [ValuationRing (Localization.AtPrime (Ideal.span {φ (MvPolynomial.X 0)}))]
    (ρ : C ⧸ Ideal.span {y (MvPolynomial.X 0)} →ₐ[K] B)
    (hker : ∀ a : A, ρ (Ideal.Quotient.mk _ (μ a)) = 0 ↔ a ∈ Ideal.span {φ (MvPolynomial.X 0)})
    (hρ : ∀ b : B, ∃ c d : C, ρ (Ideal.Quotient.mk _ d) ≠ 0 ∧
      ρ (Ideal.Quotient.mk _ d) * b = ρ (Ideal.Quotient.mk _ c)) :
    Function.Injective (ρ.comp (strictTransformHyperplaneMap φ y μ w hw)) ∧
      ∀ b : B, ∃ r s : A ⧸ Ideal.span {φ (MvPolynomial.X 0)}, s ≠ 0 ∧
        ρ (strictTransformHyperplaneMap φ y μ w hw s) * b =
          ρ (strictTransformHyperplaneMap φ y μ w hw r) := by
  let P : Ideal A := Ideal.span {φ (MvPolynomial.X 0)}
  let π : C →+* B := ρ.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {y (MvPolynomial.X 0)}))
  have hker' : ∀ a : A, π (μ.toRingHom a) = 0 ↔ a ∈ P := hker
  refine ⟨?_, fun b => ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact (hker a).mp hz
  · obtain ⟨r, s, hs, h⟩ := birational_of_valuationRing μ.toRingHom hμ hbir P π hker' hρ b
    exact ⟨Ideal.Quotient.mk _ r, Ideal.Quotient.mk _ s,
      fun h0 => hs (Ideal.Quotient.eq_zero_iff_mem.mp h0), h⟩

end StrictTransform

end MixedFujita
