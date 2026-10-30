/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CanonicalDiscriminantModuliWeil
public import MixedFujita.CartierDivisorCoefficients

/-! Clear the actual discriminant and moduli Cartier denominators together.
The rational coefficient identity becomes an exact equality of actual Cartier
divisors on the normal base; the original presentation divisor is arbitrary. -/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- The actual moduli Cartier multiple has an exact integral presentation after
clearing both the original and discriminant denominators. -/
theorem moduli_cartier_integral_presentation
    {B : Scheme.{u}} [IsIntegral B] [IsNoetherian B]
    (hnormB : ∀ b : B, IsIntegrallyClosed (B.presheaf.stalk b))
    (C H CΔ CM : CartierDivisor B) (Δ : CodimensionOnePoint B →₀ ℚ)
    (d : ℕ) (hd : 0 < d) (m ℓ s : ℕ)
    (hCΔ : ∀ β : CodimensionOnePoint B,
      (cartierCoefficient CΔ (β : B) : ℚ) = (m : ℚ) * Δ β)
    (hCM : ∀ β : CodimensionOnePoint B,
      (cartierCoefficient CM (β : B) : ℚ) =
        (ℓ : ℚ) * moduliWeilPart C H Δ ((s : ℚ) / (d : ℚ)) β) :
    (d * m) • CM = (ℓ * m * s) • H - (d * m * ℓ) • C - (d * ℓ) • CΔ := by
  apply cartierDivisor_eq_of_forall_coefficient_eq hnormB
  intro β
  apply Int.cast_injective (α := ℚ)
  simp only [cartierCoefficient_nsmul, cartierCoefficient_sub, Int.cast_sub,
    Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
  rw [hCM β, hCΔ β]
  simp only [moduliWeilPart, Finsupp.sub_apply, Finsupp.smul_apply,
    smul_eq_mul, rationalCartierWeilDivisor_apply]
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

end MixedFujita
