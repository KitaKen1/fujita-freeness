/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierSectionBoundaryAvoidance
public import MixedFujita.KltPairs

/-!
Boundary-compatible cuts preserve old coefficients, insert precisely the chosen numerator
at new components and keep every normalized rational boundary coefficient in [0,1).
The actual Cartier presentation of K+B also satisfies LogPairBoundaryEffective.
The signed upper-bound version also permits negative old boundary coefficients.
LogPairIsKlt, which quantifies over every proper birational smooth model, is a separate goal.
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

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- The coefficients at the old prime points are unchanged by an avoiding cut. -/
theorem cartierSection_perturbation_old_coefficient
    (B D : CartierDivisor X) (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0)
    {r q : ℕ} (ξ : Fin r → X) (η : Fin q → X)
    (hdis : Disjoint (Set.range ξ) (Set.range η))
    (hcoeff : ∀ x : CodimensionOnePoint X,
      cartierCoefficient (cartierSectionZeroDivisor D s hs) (x : X) =
        if (x : X) ∈ Set.range η then 1 else 0)
    (k : ℕ) (x : CodimensionOnePoint X) (hx : (x : X) ∈ Set.range ξ) :
    cartierCoefficient (B + k • cartierSectionZeroDivisor D s hs) (x : X) =
      cartierCoefficient B (x : X) := by
  have hnot : (x : X) ∉ Set.range η := fun h => Set.disjoint_left.mp hdis hx h
  have h := cartierSection_perturbation_coefficient_formula B D s hs η hcoeff 1 k x
  simpa only [one_nsmul, Nat.cast_one, one_mul, ite_eq_right hnot, add_zero] using h

/-- At each genuinely new component the numerator is exactly k. -/
theorem cartierSection_perturbation_new_coefficient
    (B D : CartierDivisor X) (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0)
    {r q : ℕ} (ξ : Fin r → X) (η : Fin q → X)
    (hdis : Disjoint (Set.range ξ) (Set.range η))
    (hsupport : ∀ x : CodimensionOnePoint X,
      (x : X) ∉ Set.range ξ → cartierCoefficient B (x : X) = 0)
    (hcoeff : ∀ x : CodimensionOnePoint X,
      cartierCoefficient (cartierSectionZeroDivisor D s hs) (x : X) =
        if (x : X) ∈ Set.range η then 1 else 0)
    (k : ℕ) (x : CodimensionOnePoint X) (hx : (x : X) ∈ Set.range η) :
    cartierCoefficient (B + k • cartierSectionZeroDivisor D s hs) (x : X) = (k : ℤ) := by
  have hnot : (x : X) ∉ Set.range ξ := fun h => Set.disjoint_left.mp hdis h hx
  have h := cartierSection_perturbation_coefficient_formula B D s hs η hcoeff 1 k x
  simpa only [one_nsmul, Nat.cast_one, one_mul, ite_eq_left hx, hsupport x hnot,
    zero_add] using h

/-- Every normalized rational coefficient lies in [0,1) when the numerator is below d. -/
theorem cartierSection_perturbation_rational_coefficient_bounds
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
      0 ≤ (cartierCoefficient (B + k • cartierSectionZeroDivisor D s hs) (x : X) : ℚ) / d ∧
      (cartierCoefficient (B + k • cartierSectionZeroDivisor D s hs) (x : X) : ℚ) / d < 1 := by
  intro x
  have h := cartierSection_perturbation_coefficient_bounds B D s hs ξ η hdis hsupport
    hcoeff d k hk hB x
  have hd : (0 : ℚ) < d := by exact_mod_cast (Nat.zero_le k).trans_lt hk
  refine ⟨div_nonneg (by exact_mod_cast h.1) hd.le, ?_⟩
  apply (div_lt_one hd).mpr
  exact_mod_cast h.2

/-- The upper coefficient bound survives even when the old boundary has negative coefficients. -/
theorem cartierSection_signed_perturbation_coefficient_lt
    (B D : CartierDivisor X) (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0)
    {r q : ℕ} (ξ : Fin r → X) (η : Fin q → X)
    (hdis : Disjoint (Set.range ξ) (Set.range η))
    (hsupport : ∀ x : CodimensionOnePoint X,
      (x : X) ∉ Set.range ξ → cartierCoefficient B (x : X) = 0)
    (hcoeff : ∀ x : CodimensionOnePoint X,
      cartierCoefficient (cartierSectionZeroDivisor D s hs) (x : X) =
        if (x : X) ∈ Set.range η then 1 else 0)
    (d k : ℕ) (hk : k < d)
    (hB : ∀ x : CodimensionOnePoint X, cartierCoefficient B (x : X) < (d : ℤ)) :
    ∀ x : CodimensionOnePoint X,
      cartierCoefficient (B + k • cartierSectionZeroDivisor D s hs) (x : X) < (d : ℤ) := by
  intro x
  by_cases hx : (x : X) ∈ Set.range η
  · rw [cartierSection_perturbation_new_coefficient B D s hs ξ η hdis hsupport hcoeff k x hx]
    exact_mod_cast hk
  · have h := cartierSection_perturbation_coefficient_formula B D s hs η hcoeff 1 k x
    simp only [one_nsmul, Nat.cast_one, one_mul, ite_eq_right hx, add_zero] at h
    rw [h]
    exact hB x

/-- The normalized signed boundary coefficients remain strictly below one. -/
theorem cartierSection_signed_perturbation_rational_coefficient_lt_one
    (B D : CartierDivisor X) (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0)
    {r q : ℕ} (ξ : Fin r → X) (η : Fin q → X)
    (hdis : Disjoint (Set.range ξ) (Set.range η))
    (hsupport : ∀ x : CodimensionOnePoint X,
      (x : X) ∉ Set.range ξ → cartierCoefficient B (x : X) = 0)
    (hcoeff : ∀ x : CodimensionOnePoint X,
      cartierCoefficient (cartierSectionZeroDivisor D s hs) (x : X) =
        if (x : X) ∈ Set.range η then 1 else 0)
    (d k : ℕ) (hk : k < d)
    (hB : ∀ x : CodimensionOnePoint X, cartierCoefficient B (x : X) < (d : ℤ)) :
    ∀ x : CodimensionOnePoint X,
      (cartierCoefficient (B + k • cartierSectionZeroDivisor D s hs) (x : X) : ℚ) / d < 1 := by
  intro x
  have h := cartierSection_signed_perturbation_coefficient_lt B D s hs ξ η hdis hsupport
    hcoeff d k hk hB x
  have hd : (0 : ℚ) < d := by exact_mod_cast (Nat.zero_le k).trans_lt hk
  apply (div_lt_one hd).mpr
  exact_mod_cast h

section LogPair

variable {K : Type u} [Field K] [X.Over (Spec (CommRingCat.of K))] {n : ℕ}
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]

/-- The actual Cartier presentation of the perturbed pair has an effective boundary. -/
theorem cartierSection_perturbation_logPairBoundaryEffective
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (d : ℕ)
    (B D : CartierDivisor X) (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0)
    {q : ℕ} (η : Fin q → X)
    (hcoeff : ∀ x : CodimensionOnePoint X,
      cartierCoefficient (cartierSectionZeroDivisor D s hs) (x : X) =
        if (x : X) ∈ Set.range η then 1 else 0)
    (hB : ∀ x : CodimensionOnePoint X, 0 ≤ cartierCoefficient B (x : X)) (k : ℕ) :
    LogPairBoundaryEffective c₀ f₀ d
      (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) +
        (B + k • cartierSectionZeroDivisor D s hs)) := by
  intro c x hc hx
  have hbase := smooth_logPairBoundaryEffective_zero c₀ f₀ d c x hc hx
  have hpert : 0 ≤ cartierCoefficient (B + k • cartierSectionZeroDivisor D s hs) x := by
    rw [cartierCoefficient_add, cartierCoefficient_nsmul, hcoeff ⟨x, hx⟩]
    have hB' : 0 ≤ cartierCoefficient B x := hB ⟨x, hx⟩
    split_ifs <;> simp only [mul_one, mul_zero] <;> omega
  rw [cartierCoefficient_add]
  exact hbase.trans (le_add_of_nonneg_right hpert)

end LogPair

section GeneralCuts

variable {K : Type u} [Field K] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] [IsNoetherian X]

/-- An actual reduced SNC cut supplies every upper-bound perturbation of a signed old boundary. -/
theorem cartierSections_exists_signed_boundary_compatible_perturbation [CharZero K]
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
      IsSNCFamily K n (Fin.append ξ η) ∧ Disjoint (Set.range ξ) (Set.range η) ∧
      (cartierSectionZeroDivisor D (∑ i, t i • s i) hst).toWeilDivisor =
        ∑ j, WeilDivisor.ofPoint (⟨η j, hη j⟩ : CodimensionOnePoint X) ∧
      (∀ (d k : ℕ), k < d →
        (∀ x : CodimensionOnePoint X, cartierCoefficient B (x : X) < (d : ℤ)) →
        ∀ x : CodimensionOnePoint X,
          (cartierCoefficient (B + k • cartierSectionZeroDivisor D (∑ i, t i • s i) hst)
            (x : X) : ℚ) / d < 1) := by
  obtain ⟨t, hst, q, η, hη, hinj, hsm, hcover, hsnc, havoid, hdis, hWeil, hcoeff, hbounds⟩ :=
    cartierSections_exists_boundary_compatible_perturbation B D s hs ξ hξ hsupport
  refine ⟨t, hst, q, η, hη, hinj, hsm, hsnc, hdis, hWeil, ?_⟩
  intro d k hk hB
  exact cartierSection_signed_perturbation_rational_coefficient_lt_one B D _ hst ξ η
    hdis hsupport hcoeff d k hk hB

end GeneralCuts

end MixedFujita
