/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.IntegerNewtonReconstruction
public import MixedFujita.TopDimensionalMixedEuler

/-! 元Cartierの実Euler多項式と最高次係数の普通の階乗規格化。 See reports/check-222-euler-newton-hilbert-normalization.json for the verified scope. General multivariate intersection identification and mixed ample-pullback positivity remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open Polynomial Finset

/-- The original Cartier Euler polynomial, defined from the original actual
Cartier sheaf Euler differences with the same factorial convention. -/
noncomputable def cartierEulerPolynomial
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] (n : ℕ) (H E : CartierDivisor X) : ℚ[X] :=
  rationalNewtonPolynomial n (fun k =>
    (cartierMixedEulerDifference K (List.replicate k H) E : ℚ))


/-- The ordinary rational polynomial equals the actual Euler characteristic
of every signed multiple of the ORIGINAL Cartier divisor. -/
theorem proper_cartierEulerPolynomial_eval_int
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X ≤ n) (H E : CartierDivisor X) (z : ℤ) :
    (cartierEulerPolynomial K n H E).eval (z : ℚ) =
      (Scheme.Modules.eulerChar (X ↘ Spec (CommRingCat.of K)) (E + z • H).sheaf : ℚ) := by
  exact rationalNewtonPolynomial_eval_affine_of_mixed_nilpotence
    (fun F : CartierDivisor X => Scheme.Modules.eulerChar (X ↘ Spec (CommRingCat.of K)) F.sheaf)
    n H E
    (fun t => proper_cartierMixedEulerDifference_vanish_of_length K n hdim
      (List.replicate (n + 1) H) (by simp only [List.length_replicate]; omega) (E + t • H)) z


/-- The original polynomial has ordinary degree at most the geometric bound. -/
theorem cartierEulerPolynomial_natDegree_le
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] (n : ℕ) (H E : CartierDivisor X) :
    (cartierEulerPolynomial K n H E).natDegree ≤ n :=
  rationalNewtonPolynomial_natDegree_le n _


/-- Its ordinary top coefficient multiplied by n! is exactly the original
diagonal mixed Cartier Euler coefficient. -/
theorem cartierEulerPolynomial_coeff_top
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] (n : ℕ) (H E : CartierDivisor X) :
    (n.factorial : ℚ) * (cartierEulerPolynomial K n H E).coeff n =
      (cartierMixedEulerDifference K (List.replicate n H) E : ℚ) :=
  factorial_mul_rationalNewtonPolynomial_coeff_top n _


/-- The highest ordinary coefficient is independent of the base twist,
by actual geometric nilpotence rather than a supplied polynomial identity. -/
theorem proper_cartierEulerPolynomial_top_coeff_base_independent
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X ≤ n) (H E F : CartierDivisor X) :
    (cartierEulerPolynomial K n H E).coeff n = (cartierEulerPolynomial K n H F).coeff n := by
  have hE := cartierEulerPolynomial_coeff_top K n H E
  have hF := cartierEulerPolynomial_coeff_top K n H F
  have h := proper_cartierMixedEulerDifference_top_base_independent K n hdim
    (List.replicate n H) (List.length_replicate ..) E F
  rw [h] at hE
  exact mul_left_cancel₀ (by exact_mod_cast n.factorial_ne_zero) (hE.trans hF.symm)

end MixedFujita
