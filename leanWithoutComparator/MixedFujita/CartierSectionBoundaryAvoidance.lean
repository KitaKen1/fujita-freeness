/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierSectionFiniteAvoidance
public import MixedFujita.CartierSectionPrimeDecomposition

/-!
Intersecting the Bertini parameter open with finite point avoidance produces actual reduced
prime SNC cuts avoiding the old boundary generic points. The new prime family is disjoint
from the old one. A denominator-cleared boundary supported on the old family therefore keeps
its old coefficients, while the new components have precisely the chosen numerator.
The resulting interval bound concerns ambient prime coefficients. It does not assert the
klt discrepancy inequality on all birational models or construct pointed cuts.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))] [IsLocallyNoetherian X]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]

/-- The general reduced prime SNC cut can simultaneously avoid any finite set of points. -/
theorem cartierSections_general_reduced_prime_snc_avoiding [CharZero K] [CompactSpace X]
    (D : CartierDivisor X) {ι : Type*} [Fintype ι] (s : ι → Γ(D.sheaf, ⊤))
    (hs : CartierSectionsBasePointFree D s) {n r : ℕ} (ξ : Fin r → X)
    (hξ : IsSNCFamily K n ξ) (Z : Set X) (hZ : Z.Finite) :
    ∃ p : MvPolynomial ι K, p ≠ 0 ∧ (∃ t : ι → K, MvPolynomial.aeval t p ≠ 0) ∧
      ∀ t : ι → K, MvPolynomial.aeval t p ≠ 0 →
        ∃ (hst : (∑ i, t i • s i) ≠ 0) (q : ℕ) (η : Fin q → X),
          Smooth (cartierSectionZeroSchemeι D (∑ i, t i • s i) hst ≫
            (X ↘ Spec (CommRingCat.of K))) ∧ Function.Injective η ∧
          (∀ j, Order.coheight (η j) = 1) ∧
          cartierSectionZeroLocus D (∑ i, t i • s i) = ⋃ j, closure ({η j} : Set X) ∧
          IsSNCFamily K n (Fin.append ξ η) ∧
          (∀ x : CodimensionOnePoint X,
            cartierCoefficient (cartierSectionZeroDivisor D (∑ i, t i • s i) hst) (x : X) =
              if (x : X) ∈ Set.range η then 1 else 0) ∧
          (∀ x ∈ Z, x ∉ cartierSectionZeroLocus D (∑ i, t i • s i)) := by
  classical
  obtain ⟨p, hp, hpex, hgood⟩ := cartierSections_general_reduced_prime_snc D s hs ξ hξ
  obtain ⟨a, ha, havoid⟩ := cartierSections_finite_nonvanishing_polynomial (K := K) D s hs Z hZ
  refine ⟨p * a, mul_ne_zero hp ha, ?_, fun t ht => ?_⟩
  · by_contra h
    push Not at h
    apply mul_ne_zero hp ha
    apply MvPolynomial.funext
    intro t
    rw [map_zero]
    exact h t
  · rw [map_mul] at ht
    obtain ⟨hst, q, η, hsm, hinj, hη, hrange, hcover, hdis, hsnc, hcoeff⟩ :=
      hgood t (mul_ne_zero_iff.mp ht).1
    exact ⟨hst, q, η, hsm, hinj, hη, hcover, hsnc, hcoeff,
      havoid t (mul_ne_zero_iff.mp ht).2⟩

/-- Avoiding the old generic points separates the actual old and new prime families. -/
theorem cartierSection_component_ranges_disjoint
    (D : CartierDivisor X) (s : Γ(D.sheaf, ⊤)) {r q : ℕ}
    (ξ : Fin r → X) (η : Fin q → X)
    (hcover : cartierSectionZeroLocus D s = ⋃ j, closure ({η j} : Set X))
    (havoid : ∀ i, ξ i ∉ cartierSectionZeroLocus D s) :
    Disjoint (Set.range ξ) (Set.range η) := by
  rw [Set.disjoint_left]
  rintro x ⟨i, rfl⟩ ⟨j, hj⟩
  apply havoid i
  rw [hcover]
  exact Set.mem_iUnion.mpr ⟨j, hj ▸ subset_closure rfl⟩

/-- Disjoint old support and new reduced components preserve the cleared boundary interval. -/
theorem cartierSection_perturbation_coefficient_bounds
    (B D : CartierDivisor X) (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0)
    {r q : ℕ} (ξ : Fin r → X) (η : Fin q → X)
    (hdis : Disjoint (Set.range ξ) (Set.range η))
    (hsupport : ∀ x : CodimensionOnePoint X,
      (x : X) ∉ Set.range ξ → cartierCoefficient B (x : X) = 0)
    (hcoeff : ∀ x : CodimensionOnePoint X,
      cartierCoefficient (cartierSectionZeroDivisor D s hs) (x : X) =
        if (x : X) ∈ Set.range η then 1 else 0)
    (d k : ℕ) (hk : k < d)
    (hB : ∀ x : CodimensionOnePoint X,
      0 ≤ cartierCoefficient B (x : X) ∧ cartierCoefficient B (x : X) < (d : ℤ)) :
    ∀ x : CodimensionOnePoint X,
      0 ≤ cartierCoefficient (B + k • cartierSectionZeroDivisor D s hs) (x : X) ∧
      cartierCoefficient (B + k • cartierSectionZeroDivisor D s hs) (x : X) < (d : ℤ) := by
  intro x
  have hformula := cartierSection_perturbation_coefficient_formula B D s hs η hcoeff 1 k x
  simp only [one_nsmul, Nat.cast_one, one_mul] at hformula
  rw [hformula]
  by_cases hx : (x : X) ∈ Set.range η
  · have hnot : (x : X) ∉ Set.range ξ := fun h => Set.disjoint_left.mp hdis h hx
    rw [ite_eq_left hx, hsupport x hnot, zero_add]
    exact ⟨Nat.cast_nonneg _, by exact_mod_cast hk⟩
  · rw [ite_eq_right hx, add_zero]
    exact hB x

variable [IsNoetherian X]

/-- An actual boundary-compatible SNC cut with its prime decomposition and all interval bounds.
The supplied boundary interval is maintained for any numerator strictly below its denominator. -/
theorem cartierSections_exists_boundary_compatible_perturbation [CharZero K]
    (B D : CartierDivisor X) {ι : Type*} [Fintype ι] (s : ι → Γ(D.sheaf, ⊤))
    (hs : CartierSectionsBasePointFree D s) {n r : ℕ} (ξ : Fin r → X)
    (hξ : IsSNCFamily K n ξ)
    (hsupport : ∀ x : CodimensionOnePoint X,
      (x : X) ∉ Set.range ξ → cartierCoefficient B (x : X) = 0) :
    ∃ (t : ι → K) (hst : (∑ i, t i • s i) ≠ 0) (q : ℕ) (η : Fin q → X)
      (hη : ∀ j, Order.coheight (η j) = 1),
      Function.Injective η ∧
      Smooth (cartierSectionZeroSchemeι D (∑ i, t i • s i) hst ≫
        (X ↘ Spec (CommRingCat.of K))) ∧
      cartierSectionZeroLocus D (∑ i, t i • s i) = ⋃ j, closure ({η j} : Set X) ∧
      IsSNCFamily K n (Fin.append ξ η) ∧
      (∀ i, ξ i ∉ cartierSectionZeroLocus D (∑ i, t i • s i)) ∧
      Disjoint (Set.range ξ) (Set.range η) ∧
      (cartierSectionZeroDivisor D (∑ i, t i • s i) hst).toWeilDivisor =
        ∑ j, WeilDivisor.ofPoint (⟨η j, hη j⟩ : CodimensionOnePoint X) ∧
      (∀ x : CodimensionOnePoint X,
        cartierCoefficient (cartierSectionZeroDivisor D (∑ i, t i • s i) hst) (x : X) =
          if (x : X) ∈ Set.range η then 1 else 0) ∧
      (∀ (d k : ℕ), k < d →
        (∀ x : CodimensionOnePoint X,
          0 ≤ cartierCoefficient B (x : X) ∧ cartierCoefficient B (x : X) < (d : ℤ)) →
        ∀ x : CodimensionOnePoint X,
          0 ≤ cartierCoefficient (B + k • cartierSectionZeroDivisor D (∑ i, t i • s i) hst)
            (x : X) ∧
          cartierCoefficient (B + k • cartierSectionZeroDivisor D (∑ i, t i • s i) hst)
            (x : X) < (d : ℤ)) := by
  obtain ⟨p, hp, ⟨t, ht⟩, hgood⟩ := cartierSections_general_reduced_prime_snc_avoiding
    D s hs ξ hξ (Set.range ξ) (Set.finite_range ξ)
  obtain ⟨hst, q, η, hsm, hinj, hη, hcover, hsnc, hcoeff, havoid⟩ := hgood t ht
  have havoid' : ∀ i, ξ i ∉ cartierSectionZeroLocus D (∑ i, t i • s i) :=
    fun i => havoid (ξ i) ⟨i, rfl⟩
  have hdis := cartierSection_component_ranges_disjoint D _ ξ η hcover havoid'
  refine ⟨t, hst, q, η, hη, hinj, hsm, hcover, hsnc, havoid', hdis,
    cartierSectionZeroDivisor_toWeil_eq_sum_components D _ hst η hinj hη hcoeff,
    hcoeff, ?_⟩
  intro d k hk hB
  exact cartierSection_perturbation_coefficient_bounds B D _ hst ξ η hdis hsupport
    hcoeff d k hk hB

end MixedFujita
