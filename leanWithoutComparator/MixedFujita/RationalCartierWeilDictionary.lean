/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.NormalCartierOrderGluing
public import MixedFujita.CartierSectionPrimeDecomposition
public import OAI.AlgebraicGeometry.SectionFields.QCartier

/-!
Relate the actual Tau Ceti Cartier divisor, its rational Weil coefficients,
and OAI's local-order definition of Q-Cartierness. On a normal Noetherian
scheme Q-Cartierness is equivalent to existence of an actual Cartier multiple.
The two actual function-field maps and the resulting pullbacks agree.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]

/-- The actual rational Weil divisor of a Cartier divisor. -/
noncomputable def rationalCartierWeilDivisor (C : CartierDivisor X) : CodimensionOnePoint X →₀ ℚ :=
  C.toWeilDivisor.mapRange (Int.castAddHom ℚ) (map_zero _)

/-- The rational Weil coefficient is precisely the cast actual Cartier coefficient. -/
theorem rationalCartierWeilDivisor_apply (C : CartierDivisor X) (z : CodimensionOnePoint X) :
    rationalCartierWeilDivisor C z = (cartierCoefficient C (z : X) : ℚ) := by
  exact congrArg (fun n : ℤ => (n : ℚ)) (cartier_toWeilDivisor_coeff_eq_cartierCoefficient C z)

/-- Rationalization commutes with actual addition of Cartier divisors. -/
theorem rationalCartierWeilDivisor_add (C E : CartierDivisor X) :
    rationalCartierWeilDivisor (C + E) = rationalCartierWeilDivisor C + rationalCartierWeilDivisor E := by
  ext z
  simp only [Finsupp.add_apply, rationalCartierWeilDivisor_apply, cartierCoefficient_add, Int.cast_add]

/-- Rationalization commutes with actual integral multiples. -/
theorem rationalCartierWeilDivisor_nsmul (m : ℕ) (C : CartierDivisor X) :
    rationalCartierWeilDivisor (m • C) = m • rationalCartierWeilDivisor C := by
  ext z
  simp only [Finsupp.smul_apply, rationalCartierWeilDivisor_apply, cartierCoefficient_nsmul]
  simp only [Int.cast_mul, Int.cast_natCast, nsmul_eq_mul]

/-- Rational Weil coefficients determine the actual Cartier divisor on a normal scheme. -/
theorem rationalCartierWeilDivisor_injective
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) :
    Function.Injective (rationalCartierWeilDivisor (X := X)) := by
  intro C E h
  apply cartierDivisor_eq_of_forall_coefficient_eq hnorm C E
  intro z
  have hz := congrArg (fun b : CodimensionOnePoint X →₀ ℚ => b z) h
  simp only [rationalCartierWeilDivisor_apply] at hz
  exact_mod_cast hz

/-- OAI's local-order Q-Cartier predicate constructs an actual Cartier multiple, and conversely. -/
theorem isQCartier_iff_exists_actual_cartier_multiple
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (b : CodimensionOnePoint X →₀ ℚ) :
    OAI.RelativeDenominators.IsQCartier X b ↔
      ∃ (m : ℕ), 0 < m ∧ ∃ C : CartierDivisor X,
        ∀ z : CodimensionOnePoint X, (cartierCoefficient C (z : X) : ℚ) = (m : ℚ) * b z := by
  classical
  constructor
  · rintro ⟨m, hm, hloc⟩
    choose U hmem f hf using hloc
    let v : CodimensionOnePoint X → ℤ := fun z => X.ord (f (z : X) : X.functionField) (z : X)
    obtain ⟨C, hC, _⟩ := normal_existsUnique_cartier_of_local_orders hnorm v (by
      intro x
      refine ⟨U x, hmem x, f x, fun z hz => ?_⟩
      apply Int.cast_injective (α := ℚ)
      exact (hf x z hz).symm.trans (hf (z : X) z (hmem (z : X))))
    refine ⟨m, hm, C, fun z => ?_⟩
    rw [hC z]
    exact (hf (z : X) z (hmem (z : X))).symm
  · rintro ⟨m, hm, C, hC⟩
    refine ⟨m, hm, fun x => ?_⟩
    obtain ⟨f, hf⟩ := C.exists_isLocalEquationAt x
    obtain ⟨U, hxU, hU⟩ := CartierDivisor.isLocalEquationAt_iff.mp hf
    letI : Nonempty U := ⟨⟨x, hxU⟩⟩
    refine ⟨U, hxU, f, fun z hz => ?_⟩
    rw [← hC z, cartierCoefficient_eq_ord
      (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hU hz)]

/-- Every actual Cartier divisor gives OAI Q-Cartier data with denominator one. -/
theorem rationalCartierWeilDivisor_isQCartier (C : CartierDivisor X) :
    OAI.RelativeDenominators.IsQCartier X (rationalCartierWeilDivisor C) := by
  refine ⟨1, by omega, fun x => ?_⟩
  obtain ⟨f, hf⟩ := C.exists_isLocalEquationAt x
  obtain ⟨U, hxU, hU⟩ := CartierDivisor.isLocalEquationAt_iff.mp hf
  letI : Nonempty U := ⟨⟨x, hxU⟩⟩
  refine ⟨U, hxU, f, fun z hz => ?_⟩
  rw [Nat.cast_one, one_mul, rationalCartierWeilDivisor_apply,
    cartierCoefficient_eq_ord (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hU hz)]

/-- The OAI and project maps of actual function fields are the same ring homomorphism. -/
theorem oai_functionFieldPullback_eq_dominantFunctionFieldMap
    {Y : Scheme.{u}} [IsIntegral Y] (q : X ⟶ Y) [IsDominant q] :
    OAI.RelativeDenominators.functionFieldPullback q = (dominantFunctionFieldMap q).hom := rfl

/-- OAI Q-Cartier pullback of an actual Cartier divisor is its actual Cartier pullback, coefficientwise. -/
theorem rationalCartierWeilDivisor_pullback
    {Y : Scheme.{u}} [IsIntegral Y] [IsNoetherian Y]
    (hnormY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (q : X ⟶ Y) [IsDominant q] (C : CartierDivisor Y) :
    OAI.RelativeDenominators.pullbackQCartier hnormY q (rationalCartierWeilDivisor C)
      (rationalCartierWeilDivisor_isQCartier C) = rationalCartierWeilDivisor (cartierPullback q C) := by
  ext p
  obtain ⟨f, hf⟩ := C.exists_isLocalEquationAt (q (p : X))
  obtain ⟨U, hpU, hU⟩ := CartierDivisor.isLocalEquationAt_iff.mp hf
  letI : Nonempty U := ⟨⟨q (p : X), hpU⟩⟩
  have hlocal : ∀ z : CodimensionOnePoint Y, (z : Y) ∈ U →
      (1 : ℚ) * rationalCartierWeilDivisor C z = (Y.ord (f : Y.functionField) (z : Y) : ℚ) := by
    intro z hz
    rw [one_mul, rationalCartierWeilDivisor_apply,
      cartierCoefficient_eq_ord (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hU hz)]
  rw [OAI.RelativeDenominators.pullbackQCartier_apply_of_local hnormY q
    (rationalCartierWeilDivisor C) (rationalCartierWeilDivisor_isQCartier C) 1 (by omega) U f hlocal p hpU,
    Nat.cast_one, div_one, rationalCartierWeilDivisor_apply,
    cartierCoefficient_eq_ord (cartierPullback_isLocalEquationAt q C (p : X) hf),
    oai_functionFieldPullback_eq_dominantFunctionFieldMap]
  rfl

end MixedFujita
