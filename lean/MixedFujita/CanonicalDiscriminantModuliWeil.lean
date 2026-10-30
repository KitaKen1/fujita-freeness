/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RationalCartierWeilLinearEquivalence

/-!
Construct a finite rational Weil moduli part from a canonical Cartier divisor,
an actual finite discriminant and the specified Cartier presentation on the base.
Their sum is Q-Cartier and its actual pullback is computed. This algebraic
construction does not assert moduli descent or positivity, or Q-Cartierness of
the discriminant separately.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

variable {B : Scheme.{u}} [IsIntegral B] [IsNoetherian B]

/-- The finite rational Weil moduli part associated to the specified base presentation. -/
noncomputable def moduliWeilPart (C H : CartierDivisor B)
    (Δ : CodimensionOnePoint B →₀ ℚ) (a : ℚ) : CodimensionOnePoint B →₀ ℚ :=
  a • rationalCartierWeilDivisor H - rationalCartierWeilDivisor C - Δ

/-- Canonical, discriminant and moduli parts recover the specified rational Cartier class. -/
theorem moduliWeilPart_recombine (C H : CartierDivisor B)
    (Δ : CodimensionOnePoint B →₀ ℚ) (a : ℚ) :
    rationalCartierWeilDivisor C + Δ + moduliWeilPart C H Δ a =
      a • rationalCartierWeilDivisor H := by
  unfold moduliWeilPart
  abel

/-- The moduli part is the unique finite Weil divisor satisfying the recombination identity. -/
theorem moduliWeilPart_unique (C H : CartierDivisor B)
    (Δ M : CodimensionOnePoint B →₀ ℚ) (a : ℚ)
    (hM : rationalCartierWeilDivisor C + Δ + M = a • rationalCartierWeilDivisor H) :
    M = moduliWeilPart C H Δ a := by
  apply add_left_cancel (a := rationalCartierWeilDivisor C + Δ)
  exact hM.trans (moduliWeilPart_recombine C H Δ a).symm

/-- Q-Cartierness belongs to the required sum without assuming it for the discriminant. -/
theorem moduliWeilPart_combination_isQCartier (C H : CartierDivisor B)
    (Δ : CodimensionOnePoint B →₀ ℚ) (a : ℚ) :
    OAI.RelativeDenominators.IsQCartier B
      (rationalCartierWeilDivisor C + Δ + moduliWeilPart C H Δ a) := by
  rw [moduliWeilPart_recombine]
  exact OAI.RelativeDenominators.isQCartier_smul (rationalCartierWeilDivisor_isQCartier H) a

/-- The actual Q-Cartier pullback of the sum agrees with the supplied Cartier pullback. -/
theorem moduliWeilPart_combination_pullback
    {T : Scheme.{u}} [IsIntegral T] [IsNoetherian T]
    (hnormB : ∀ b : B, IsIntegrallyClosed (B.presheaf.stalk b))
    (q : T ⟶ B) [IsDominant q] (C H : CartierDivisor B)
    (Δ : CodimensionOnePoint B →₀ ℚ) (a : ℚ) :
    OAI.RelativeDenominators.pullbackQCartier hnormB q
      (rationalCartierWeilDivisor C + Δ + moduliWeilPart C H Δ a)
      (moduliWeilPart_combination_isQCartier C H Δ a) =
      a • rationalCartierWeilDivisor (cartierPullback q H) := by
  simp only [moduliWeilPart_recombine]
  rw [OAI.RelativeDenominators.pullbackQCartier_smul
    hnormB q (rationalCartierWeilDivisor_isQCartier H) a,
    rationalCartierWeilDivisor_pullback]

end MixedFujita
