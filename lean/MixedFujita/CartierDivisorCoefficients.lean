/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RegularEquationCartier
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Order
public import TauCeti.AlgebraicGeometry.CartierDivisor.LocalEquations

/-!
Coefficients of Cartier divisors along prime divisors (step 1). On a locally Noetherian integral
scheme the coefficient of a Cartier divisor D along the prime divisor with generic point ξ is the
order of vanishing at ξ of a local equation of D at ξ. Two local equations differ by a regular
unit near ξ, which has order zero, so the coefficient does not depend on the choice. Local
equations multiply under addition and invert under negation, so the coefficient is additive;
the coefficient of div f is the order of f, and a divisor with a regular local equation at ξ has
nonnegative coefficient there. These are the coefficients a_E of the discrepancy divisors that
define klt pairs.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- The coefficient of D along the prime divisor with generic point ξ: the order at ξ of a local
equation of D at ξ. -/
noncomputable def cartierCoefficient (D : CartierDivisor X) (ξ : X) : ℤ :=
  X.ord ((Classical.choose (D.exists_isLocalEquationAt ξ) : X.functionFieldˣ) : X.functionField) ξ

/-- Two local equations at ξ have the same order at ξ. -/
theorem ord_eq_of_isLocalEquationAt {D : CartierDivisor X} {ξ : X} {f g : X.functionFieldˣ}
    (hf : D.IsLocalEquationAt ξ f) (hg : D.IsLocalEquationAt ξ g) :
    X.ord (f : X.functionField) ξ = X.ord (g : X.functionField) ξ := by
  obtain ⟨V, hξV, hV⟩ := CartierDivisor.isLocalEquationAt_iff.mp hf
  obtain ⟨W, hξW, hW⟩ := CartierDivisor.isLocalEquationAt_iff.mp hg
  have : Nonempty V := ⟨⟨ξ, hξV⟩⟩
  have : Nonempty W := ⟨⟨ξ, hξW⟩⟩
  have : Nonempty (V ⊓ W : X.Opens) := ⟨⟨ξ, hξV, hξW⟩⟩
  obtain ⟨r, hr⟩ := (rationalUnitClass_eq_rationalUnitClass_iff X (V ⊓ W) f g).mp
    ((CartierDivisor.rationalUnitClass_eq_of_le inf_le_left hV).trans
      (CartierDivisor.rationalUnitClass_eq_of_le inf_le_right hW).symm)
  have hu : X.ord ((regularUnitToFunctionField X (V ⊓ W) r : X.functionFieldˣ) :
      X.functionField) ξ = 0 := by
    rw [regularUnitToFunctionField_apply]
    exact X.ord_of_isUnit r.isUnit ⟨hξV, hξW⟩
  rw [← hr, Units.val_mul, Scheme.ord_mul (Units.ne_zero _) (Units.ne_zero _), hu, zero_add]

/-- The coefficient is the order of any local equation. -/
theorem cartierCoefficient_eq_ord {D : CartierDivisor X} {ξ : X} {f : X.functionFieldˣ}
    (hf : D.IsLocalEquationAt ξ f) : cartierCoefficient D ξ = X.ord (f : X.functionField) ξ :=
  ord_eq_of_isLocalEquationAt (Classical.choose_spec (D.exists_isLocalEquationAt ξ)) hf

theorem cartierCoefficient_add (D E : CartierDivisor X) (ξ : X) :
    cartierCoefficient (D + E) ξ = cartierCoefficient D ξ + cartierCoefficient E ξ := by
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt ξ
  obtain ⟨g, hg⟩ := E.exists_isLocalEquationAt ξ
  rw [cartierCoefficient_eq_ord (hf.mul hg), cartierCoefficient_eq_ord hf,
    cartierCoefficient_eq_ord hg, Units.val_mul, Scheme.ord_mul (Units.ne_zero _) (Units.ne_zero _)]

theorem cartierCoefficient_neg (D : CartierDivisor X) (ξ : X) :
    cartierCoefficient (-D) ξ = -cartierCoefficient D ξ := by
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt ξ
  rw [cartierCoefficient_eq_ord hf.inv, cartierCoefficient_eq_ord hf, Units.val_inv_eq_inv_val,
    TauCeti.AlgebraicGeometry.Scheme.ord_inv]

theorem cartierCoefficient_sub (D E : CartierDivisor X) (ξ : X) :
    cartierCoefficient (D - E) ξ = cartierCoefficient D ξ - cartierCoefficient E ξ := by
  rw [sub_eq_add_neg, cartierCoefficient_add, cartierCoefficient_neg, ← sub_eq_add_neg]

theorem cartierCoefficient_zero (ξ : X) : cartierCoefficient (0 : CartierDivisor X) ξ = 0 := by
  rw [cartierCoefficient_eq_ord (CartierDivisor.isLocalEquationAt_zero ξ), Units.val_one,
    TauCeti.AlgebraicGeometry.Scheme.ord_one]

theorem cartierCoefficient_nsmul (D : CartierDivisor X) (m : ℕ) (ξ : X) :
    cartierCoefficient (m • D) ξ = m * cartierCoefficient D ξ := by
  induction m with
  | zero => rw [zero_nsmul, cartierCoefficient_zero, Nat.cast_zero, zero_mul]
  | succ m ih =>
    rw [succ_nsmul, cartierCoefficient_add, ih]
    push_cast
    ring

/-- The coefficient of a principal divisor is the order of the function. -/
theorem cartierCoefficient_principal (f : X.functionFieldˣ) (ξ : X) :
    cartierCoefficient (principalCartierDivisor X f) ξ = X.ord (f : X.functionField) ξ :=
  cartierCoefficient_eq_ord (CartierDivisor.isLocalEquationAt_principalCartierDivisor ξ f)

/-- A Cartier divisor with a local equation at ξ regular at ξ has nonnegative coefficient at ξ. -/
theorem cartierCoefficient_nonneg_of_mem_range {D : CartierDivisor X} {ξ : X}
    {f : X.functionFieldˣ} (hf : D.IsLocalEquationAt ξ f)
    (hreg : (f : X.functionField) ∈ (algebraMap (X.presheaf.stalk ξ) X.functionField).range) :
    0 ≤ cartierCoefficient D ξ := by
  rw [cartierCoefficient_eq_ord hf]
  obtain ⟨a, ha⟩ := hreg
  obtain ⟨U, hU, s, rfl⟩ := X.presheaf.exists_germ_eq a
  have : Nonempty U := ⟨⟨ξ, hU⟩⟩
  rw [← ha, Scheme.algebraMap_germ_eq_germToFunctionField]
  exact TauCeti.AlgebraicGeometry.Scheme.ord_germToFunctionField_nonneg s hU

end MixedFujita
