/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RationalCartierWeilDictionary

/-!
Actual principal Cartier divisors rationalize to OAI's principal Weil divisors.
An integral Cartier presentation therefore gives a rational linear equivalence
after clearing exactly its supplied positive denominator.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]

/-- The two actual principal divisor constructions have the same rational Weil coefficients. -/
theorem rationalCartierWeilDivisor_principal (ψ : X.functionFieldˣ) :
    rationalCartierWeilDivisor (principalCartierDivisor X ψ) =
      OAI.RelativeDenominators.rationalPrincipalDivisor X ψ := by
  apply Finsupp.ext
  intro z
  rw [rationalCartierWeilDivisor_apply, cartierCoefficient_principal]
  rfl

/-- Natural Cartier multiplicity is rational scalar multiplication after rationalization. -/
theorem rationalCartierWeilDivisor_nsmul_rat (m : ℕ) (C : CartierDivisor X) :
    rationalCartierWeilDivisor (m • C) = (m : ℚ) • rationalCartierWeilDivisor C := by
  rw [rationalCartierWeilDivisor_nsmul, Nat.cast_smul_eq_nsmul]

/-- An actual Cartier presentation supplies the principal witness for rational linear equivalence. -/
theorem rationalCartierWeilDivisor_presentation_linear_equivalence
    (A F : CartierDivisor X) (d : ℕ) (hd : 0 < d) (m : ℕ) (ψ : X.functionFieldˣ)
    (hA : A = m • F + principalCartierDivisor X ψ) :
    OAI.RelativeDenominators.RationallyLinearlyEquivalent X
      ((1 / (d : ℚ)) • rationalCartierWeilDivisor A)
      (((m : ℚ) / (d : ℚ)) • rationalCartierWeilDivisor F) := by
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have h1 : (d : ℚ) * (1 / (d : ℚ)) = 1 := by field_simp
  have h2 : (d : ℚ) * ((m : ℚ) / (d : ℚ)) = m := by field_simp
  refine ⟨d, hd, ψ, ?_⟩
  rw [smul_sub, smul_smul, smul_smul, h1, h2, one_smul, hA,
    rationalCartierWeilDivisor_add, rationalCartierWeilDivisor_nsmul_rat,
    rationalCartierWeilDivisor_principal]
  abel

end MixedFujita
