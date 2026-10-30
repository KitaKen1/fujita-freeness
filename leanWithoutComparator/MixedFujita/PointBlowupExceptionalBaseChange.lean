/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.StandardPointBlowupExceptionalRestriction

/-!
The exceptional restriction identity after an arbitrary homomorphism from a standard
blow-up chart. The target may be an étale chart ring or one of its localizations.
The quotient is by the image of X_k; the remaining variables evaluate the dehomogenized
leading polynomial. No substitution of a formal series at a nonzero point is used.
-/

@[expose] public section
open AlgebraicGeometry
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {K : Type u} [Field K] {A : Type v} [CommRing A] {n : ℕ}

/-- Evaluation on the exceptional quotient after any base change of a standard chart. -/
noncomputable def pointBlowupExceptionalEvaluation
    (τ : MvPolynomial (Fin n) K →+* A) (k : Fin n) :
    MvPolynomial {i : Fin n // i ≠ k} K →+*
      A ⧸ Ideal.span {τ (MvPolynomial.X k)} :=
  MvPolynomial.eval₂Hom
    ((Ideal.Quotient.mk _).comp (τ.comp MvPolynomial.C))
    (fun i => Ideal.Quotient.mk _ (τ (MvPolynomial.X i.1)))

theorem pointBlowupExceptionalEvaluation_C
    (τ : MvPolynomial (Fin n) K →+* A) (k : Fin n) (c : K) :
    pointBlowupExceptionalEvaluation τ k (MvPolynomial.C c) =
      Ideal.Quotient.mk _ (τ (MvPolynomial.C c)) :=
  MvPolynomial.eval₂Hom_C _ _ c

theorem pointBlowupExceptionalEvaluation_X
    (τ : MvPolynomial (Fin n) K →+* A) (k : Fin n) (i : {i : Fin n // i ≠ k}) :
    pointBlowupExceptionalEvaluation τ k (MvPolynomial.X i) =
      Ideal.Quotient.mk _ (τ (MvPolynomial.X i.1)) :=
  MvPolynomial.eval₂Hom_X' _ _ i

theorem pointBlowupExceptionalEvaluation_killX
    (τ : MvPolynomial (Fin n) K →+* A) (k : Fin n) (g : MvPolynomial (Fin n) K) :
    pointBlowupExceptionalEvaluation τ k (CoordinateSubspace.killX K k g) =
      Ideal.Quotient.mk _ (τ g) := by
  have hX (i : Fin n) :
      pointBlowupExceptionalEvaluation τ k (CoordinateSubspace.killX K k (MvPolynomial.X i)) =
        Ideal.Quotient.mk _ (τ (MvPolynomial.X i)) := by
    by_cases hi : i = k
    · subst i
      rw [CoordinateSubspace.killX_X_self, map_zero]
      symm
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact Ideal.subset_span (Set.mem_singleton _)
    · rw [CoordinateSubspace.killX_X_of_ne K k hi, pointBlowupExceptionalEvaluation_X]
  induction g using MvPolynomial.induction_on with
  | C c =>
    have hc : CoordinateSubspace.killX K k (MvPolynomial.C c) = MvPolynomial.C c :=
      (CoordinateSubspace.killX K k).commutes c
    rw [hc, pointBlowupExceptionalEvaluation_C]
  | add g h hg hh => simp only [map_add, hg, hh]
  | mul_X g i hg => simp only [map_mul, hg, hX]

theorem polynomialPointBlowupStrictTransform_baseChange_factor
    (τ : MvPolynomial (Fin n) K →+* A) (k : Fin n) (m : ℕ)
    (g : MvPolynomial (Fin n) K) (hg : (m : ℕ∞) ≤ (g : MvPowerSeries (Fin n) K).order) :
    τ (polynomialPointBlowupMap k g) =
      τ (MvPolynomial.X k) ^ m * τ (polynomialPointBlowupStrictTransform k m g) := by
  rw [polynomialPointBlowupMap_factor k m g hg, map_mul, map_pow]

theorem polynomialPointBlowupStrictTransform_baseChange_exceptional
    (τ : MvPolynomial (Fin n) K →+* A) (k : Fin n) (m : ℕ)
    (g : MvPolynomial (Fin n) K) (hg : (m : ℕ∞) ≤ (g : MvPowerSeries (Fin n) K).order) :
    Ideal.Quotient.mk (Ideal.span {τ (MvPolynomial.X k)})
        (τ (polynomialPointBlowupStrictTransform k m g)) =
      pointBlowupExceptionalEvaluation τ k
        (projectiveDehomogenize K k (homogeneousTaylorForm m (g : MvPowerSeries (Fin n) K))) := by
  rw [← polynomialPointBlowupStrictTransform_exceptional k m g hg,
    pointBlowupExceptionalEvaluation_killX]

end MixedFujita
