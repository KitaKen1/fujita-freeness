/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.IntegerNewtonReconstruction
public import MixedFujita.TopDimensionalMixedEuler

/-! 非被約proper源の実連接Euler多項式・全符号付き倍数と支持次元評価。 See reports/check-222-euler-newton-hilbert-normalization.json for the verified scope. General multivariate intersection identification and mixed ample-pullback positivity remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open Polynomial Finset

/-- The actual rational Euler polynomial of the original pulled Cartier
line with an actual coefficient module. Its coefficients are actual Euler
differences, without a supplied Hilbert polynomial. -/
noncomputable def cartierPulledModuleEulerPolynomial
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] (p : Y ⟶ X) (M : Y.Modules)
    (n : ℕ) (H E : CartierDivisor X) : ℚ[X] :=
  rationalNewtonPolynomial n (fun k =>
    (cartierPulledModuleMixedEulerDifference K p M (List.replicate k H) E : ℚ))


/-- Actual proper coherent Euler characteristic agrees with this explicit
polynomial at every positive AND negative integer power. No polynomiality,
finite cohomology or vanishing premise is supplied. -/
theorem proper_cartierPulledModuleEulerPolynomial_eval_int
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) (M : Y.Modules) [M.IsCoherent]
    (n : ℕ) (hdim : topologicalKrullDim Y ≤ n) (H E : CartierDivisor X) (z : ℤ) :
    (cartierPulledModuleEulerPolynomial K p M n H E).eval (z : ℚ) =
      (Scheme.Modules.eulerChar (Y ↘ Spec (CommRingCat.of K))
        ((cartierPullbackTwistFunctor (E + z • H) p).obj M) : ℚ) := by
  exact rationalNewtonPolynomial_eval_affine_of_mixed_nilpotence
    (fun F : CartierDivisor X => Scheme.Modules.eulerChar (Y ↘ Spec (CommRingCat.of K))
      ((cartierPullbackTwistFunctor F p).obj M)) n H E
    (fun t => proper_cartierPulledModuleMixedEulerDifference_vanish_of_length K n hdim p M
      (List.replicate (n + 1) H) (by simp only [List.length_replicate]; omega) (E + t • H)) z


/-- This is an ordinary polynomial of geometric degree at most n. -/
theorem cartierPulledModuleEulerPolynomial_natDegree_le
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] (p : Y ⟶ X) (M : Y.Modules)
    (n : ℕ) (H E : CartierDivisor X) :
    (cartierPulledModuleEulerPolynomial K p M n H E).natDegree ≤ n :=
  rationalNewtonPolynomial_natDegree_le n _


/-- The actual highest Euler coefficient has the ordinary n! normalization. -/
theorem cartierPulledModuleEulerPolynomial_coeff_top
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] (p : Y ⟶ X) (M : Y.Modules)
    (n : ℕ) (H E : CartierDivisor X) :
    (n.factorial : ℚ) * (cartierPulledModuleEulerPolynomial K p M n H E).coeff n =
      (cartierPulledModuleMixedEulerDifference K p M (List.replicate n H) E : ℚ) :=
  factorial_mul_rationalNewtonPolynomial_coeff_top n _


/-- The actual Euler polynomial does not depend on choosing a larger
geometric bound. It is the same ordinary polynomial, not merely the same
highest coefficient. -/
theorem proper_cartierPulledModuleEulerPolynomial_bound_independent
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) (M : Y.Modules) [M.IsCoherent]
    (n m : ℕ) (hn : topologicalKrullDim Y ≤ n) (hm : topologicalKrullDim Y ≤ m)
    (H E : CartierDivisor X) :
    cartierPulledModuleEulerPolynomial K p M n H E =
      cartierPulledModuleEulerPolynomial K p M m H E := by
  apply rationalPolynomial_eq_of_eval_nat
  intro j
  have h₁ := proper_cartierPulledModuleEulerPolynomial_eval_int K p M n hn H E (j : ℤ)
  have h₂ := proper_cartierPulledModuleEulerPolynomial_eval_int K p M m hm H E (j : ℤ)
  simpa only [Int.cast_natCast] using h₁.trans h₂.symm


/-- Actual modules supported on a closed source have an Euler polynomial
of degree bounded by that source dimension, even when the ambient proper
scheme has larger dimension and the coefficient has nilpotent layers. -/
theorem proper_cartierPulledModuleEulerPolynomial_eval_int_of_closed_support
    (K : Type u) [Field K] {X Y Z : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] [Z.Over (Spec (CommRingCat.of K))]
    [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) (i : Z ⟶ Y) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of K))]
    (M : Y.Modules) [M.IsCoherent] (hM : CohomologyAux.VanishesOff M (Set.range i))
    (n : ℕ) (hdim : topologicalKrullDim Z ≤ n) (H E : CartierDivisor X) (z : ℤ) :
    (cartierPulledModuleEulerPolynomial K p M n H E).eval (z : ℚ) =
      (Scheme.Modules.eulerChar (Y ↘ Spec (CommRingCat.of K))
        ((cartierPullbackTwistFunctor (E + z • H) p).obj M) : ℚ) := by
  let : IsProper (Z ↘ Spec (CommRingCat.of K)) := by
    have heq : i ≫ (Y ↘ Spec (CommRingCat.of K)) = Z ↘ Spec (CommRingCat.of K) :=
      HomIsOver.comp_over
    rw [← heq]
    infer_instance
  apply rationalNewtonPolynomial_eval_affine_of_mixed_nilpotence
    (fun F : CartierDivisor X => Scheme.Modules.eulerChar (Y ↘ Spec (CommRingCat.of K))
      ((cartierPullbackTwistFunctor F p).obj M)) n H E ?_ z
  intro t
  apply cartierPulledModuleMixedEulerDifference_vanish_of_closed_support
    K p (List.replicate (n + 1) H) (E + t • H) i ?_ M hM
  intro N hN
  let := hN
  exact proper_cartierPulledModuleMixedEulerDifference_vanish_of_length K n hdim (i ≫ p)
    N (List.replicate (n + 1) H) (by simp only [List.length_replicate]; omega) (E + t • H)

end MixedFujita
