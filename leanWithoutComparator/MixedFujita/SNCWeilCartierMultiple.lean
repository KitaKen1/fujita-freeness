/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCComponentCartier
public import MixedFujita.FloorDivisorLifting
public import MixedFujita.RationalWeilDenominator
public import MixedFujita.RationalCartierWeilDictionary
public import MixedFujita.SNCBoundaryKlt

/-! A signed finite Weil divisor supported on an actual SNC family has a constructed
Cartier multiple. Rational coefficients strictly below one then give an actual all-model
sub-klt canonical-plus-boundary pair. No nonnegativity or general local factoriality is used. -/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
  [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [IsSeparated (X ↘ Spec (CommRingCat.of K))]

/-- The actual SNC component Cartier divisors represent every signed integral Weil divisor
supported on the family. -/
theorem exists_snc_integer_weil_cartier {r : ℕ} (ξ : Fin r → X)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ) (N : CodimensionOnePoint X →₀ ℤ)
    (hsupport : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ → N z = 0) :
    ∃ C : CartierDivisor X, ∀ z : CodimensionOnePoint X, cartierCoefficient C (z : X) = N z := by
  classical
  obtain ⟨E, hE, hEI, hEc⟩ := exists_snc_component_cartier ξ hξ hsnc
  let a : Fin r → ℤ := fun i => N ⟨ξ i, hξ i⟩
  refine ⟨∑ i, a i • E i, fun z => ?_⟩
  rcases cartierCoefficient_member_combination ξ hinj E hEc a z with
    ⟨j, hj, hC⟩ | ⟨hz, hC⟩
  · rw [hC]
    change N ⟨ξ j, hξ j⟩ = N z
    congr 1
    exact Subtype.ext hj.symm
  · rw [hC, hsupport z hz]

/-- Clear rational denominators and construct an actual Cartier divisor with those coefficients. -/
theorem exists_snc_rational_weil_cartier_multiple {r : ℕ} (ξ : Fin r → X)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ) (b : CodimensionOnePoint X →₀ ℚ)
    (hsupport : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ → b z = 0) :
    ∃ (m : ℕ), 0 < m ∧ ∃ C : CartierDivisor X,
      ∀ z : CodimensionOnePoint X, (cartierCoefficient C (z : X) : ℚ) = (m : ℚ) * b z := by
  obtain ⟨m, hm, N, hN⟩ := rational_finsupp_exists_integral_multiple b
  have hNs : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ → N z = 0 := by
    intro z hz
    apply Int.cast_injective (α := ℚ)
    rw [Int.cast_zero, hN z, hsupport z hz, mul_zero]
  obtain ⟨C, hC⟩ := exists_snc_integer_weil_cartier ξ hinj hξ hsnc N hNs
  exact ⟨m, hm, C, fun z => by rw [hC z, hN z]⟩

/-- Every signed rational Weil divisor with actual SNC support is Q-Cartier. -/
theorem snc_rational_weil_isQCartier {r : ℕ} (ξ : Fin r → X)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ) (b : CodimensionOnePoint X →₀ ℚ)
    (hsupport : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ → b z = 0) :
    OAI.RelativeDenominators.IsQCartier X b := by
  exact (isQCartier_iff_exists_actual_cartier_multiple
    (isSNCFamily_stalk_isIntegrallyClosed hsnc) b).mpr
    (exists_snc_rational_weil_cartier_multiple ξ hinj hξ hsnc b hsupport)

variable [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]

/-- The same actual Cartier multiple realizes coefficients below one as an all-model klt pair.
The boundary may have negative coefficients. -/
theorem exists_snc_rational_weil_sub_klt_pair (c : EtaleChart K X n)
    {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (b : CodimensionOnePoint X →₀ ℚ)
    (hsupport : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ → b z = 0)
    (hb : ∀ z, b z < 1) :
    ∃ (m : ℕ), 0 < m ∧ ∃ C : CartierDivisor X,
      (∀ z : CodimensionOnePoint X, (cartierCoefficient C (z : X) : ℚ) = (m : ℚ) * b z) ∧
      LogPairIsKlt c 1 m (m • (smoothCanonicalDivisor c + principalCartierDivisor X 1) + C) := by
  obtain ⟨m, hm, C, hC⟩ := exists_snc_rational_weil_cartier_multiple ξ hinj hξ hsnc b hsupport
  refine ⟨m, hm, C, hC, isSNCFamily_logPairIsKlt c 1 m (by omega) C ξ hinj hξ hsnc ?_ ?_⟩
  · intro z hz
    apply Int.cast_injective (α := ℚ)
    rw [Int.cast_zero, hC z, hsupport z hz, mul_zero]
  · intro i
    have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
    have hcQ : (cartierCoefficient C (ξ i) : ℚ) < (m : ℚ) := by
      change (cartierCoefficient C (⟨ξ i, hξ i⟩ : CodimensionOnePoint X) : ℚ) < (m : ℚ)
      rw [hC ⟨ξ i, hξ i⟩]
      exact (mul_lt_mul_of_pos_left (hb ⟨ξ i, hξ i⟩) hmQ).trans_eq (mul_one _)
    exact_mod_cast hcQ

end MixedFujita
