/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SquarefreeNewtonCoefficient
public import MixedFujita.RationalMvPolynomialUniqueness
public import MixedFujita.PulledModuleEulerPolynomial

/-! 非被約proper源の実多変数Euler多項式・閉支持総次数上界。 See reports/check-223-multivariate-euler-intersection.json for the verified scope. Mixed positivity and the manuscript numerical-dimension dictionary remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
universe u
namespace MixedFujita
open Finset
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- The actual multivariate Euler polynomial for the original Cartier
directions pulled to an arbitrary coefficient source. -/
noncomputable def cartierPulledModuleEulerMvPolynomial
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] (p : Y ⟶ X) (M : Y.Modules)
    (r n : ℕ) (D : Fin r → CartierDivisor X) (E : CartierDivisor X) :
    MvPolynomial (Fin r) ℚ :=
  multivariateNewtonPolynomial r n D (fun F : CartierDivisor X =>
    Scheme.Modules.eulerChar (Y ↘ Spec (CommRingCat.of K))
      ((cartierPullbackTwistFunctor F p).obj M)) E


/-- The ordinary TOTAL degree of the actual Euler polynomial is bounded by n. -/
theorem cartierPulledModuleEulerMvPolynomial_totalDegree_le
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] (p : Y ⟶ X) (M : Y.Modules)
    (r n : ℕ) (D : Fin r → CartierDivisor X) (E : CartierDivisor X) :
    (cartierPulledModuleEulerMvPolynomial K p M r n D E).totalDegree ≤ n :=
  multivariateNewtonPolynomial_totalDegree_le r n D _ E


/-- The actual proper coherent multivariate Euler function is one rational
polynomial on ALL signed integer tuples, with no polynomiality or vanishing
premise. The source may be nonintegral and nonreduced. -/
theorem proper_cartierPulledModuleEulerMvPolynomial_eval_int
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) (M : Y.Modules) [M.IsCoherent]
    (r n : ℕ) (hdim : topologicalKrullDim Y ≤ n)
    (D : Fin r → CartierDivisor X) (E : CartierDivisor X) (z : Fin r → ℤ) :
    MvPolynomial.eval (fun i => (z i : ℚ)) (cartierPulledModuleEulerMvPolynomial K p M r n D E) =
      (Scheme.Modules.eulerChar (Y ↘ Spec (CommRingCat.of K))
        ((cartierPullbackTwistFunctor (E + ∑ i, z i • D i) p).obj M) : ℚ) := by
  exact multivariateNewtonPolynomial_eval_int_of_mixed_nilpotence r n D
    (fun F : CartierDivisor X => Scheme.Modules.eulerChar (Y ↘ Spec (CommRingCat.of K))
      ((cartierPullbackTwistFunctor F p).obj M)) E
    (fun L hL F => proper_cartierPulledModuleMixedEulerDifference_vanish_of_length
      K n hdim p M L hL F) z


/-- The squarefree top coefficient of the actual multivariate Euler
polynomial is the original integral mixed Euler difference, without n!. -/
theorem cartierPulledModuleEulerMvPolynomial_squarefree_top_coeff
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] (p : Y ⟶ X) (M : Y.Modules)
    (n : ℕ) (D : Fin n → CartierDivisor X) (E : CartierDivisor X) :
    (cartierPulledModuleEulerMvPolynomial K p M n n D E).coeff (squarefreeExponent n) =
      (cartierPulledModuleMixedEulerDifference K p M (List.ofFn D) E : ℚ) :=
  multivariateNewtonPolynomial_squarefree_top_coeff n D _ E


/-- Actual Euler polynomial uniqueness removes dependence on the chosen
ordinary dimension bound, for every number of variables. -/
theorem proper_cartierPulledModuleEulerMvPolynomial_bound_independent
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) (M : Y.Modules) [M.IsCoherent]
    (r n m : ℕ) (hn : topologicalKrullDim Y ≤ n) (hm : topologicalKrullDim Y ≤ m)
    (D : Fin r → CartierDivisor X) (E : CartierDivisor X) :
    cartierPulledModuleEulerMvPolynomial K p M r n D E =
      cartierPulledModuleEulerMvPolynomial K p M r m D E := by
  apply rationalMvPolynomial_eq_of_eval_int
  intro z
  rw [proper_cartierPulledModuleEulerMvPolynomial_eval_int K p M r n hn D E z,
    proper_cartierPulledModuleEulerMvPolynomial_eval_int K p M r m hm D E z]


/-- Closed-support dimension bounds the TOTAL degree of the multivariate
Euler polynomial, including all nilpotent layers in the coefficient. -/
theorem proper_cartierPulledModuleEulerMvPolynomial_eval_int_of_closed_support
    (K : Type u) [Field K] {X Y Z : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] [Z.Over (Spec (CommRingCat.of K))]
    [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) (i : Z ⟶ Y) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of K))]
    (M : Y.Modules) [M.IsCoherent] (hM : CohomologyAux.VanishesOff M (Set.range i))
    (r n : ℕ) (hdim : topologicalKrullDim Z ≤ n)
    (D : Fin r → CartierDivisor X) (E : CartierDivisor X) (z : Fin r → ℤ) :
    MvPolynomial.eval (fun j => (z j : ℚ)) (cartierPulledModuleEulerMvPolynomial K p M r n D E) =
      (Scheme.Modules.eulerChar (Y ↘ Spec (CommRingCat.of K))
        ((cartierPullbackTwistFunctor (E + ∑ j, z j • D j) p).obj M) : ℚ) := by
  let : IsProper (Z ↘ Spec (CommRingCat.of K)) := by
    have heq : i ≫ (Y ↘ Spec (CommRingCat.of K)) = Z ↘ Spec (CommRingCat.of K) :=
      HomIsOver.comp_over
    rw [← heq]
    infer_instance
  apply multivariateNewtonPolynomial_eval_int_of_mixed_nilpotence r n D
    (fun F : CartierDivisor X => Scheme.Modules.eulerChar (Y ↘ Spec (CommRingCat.of K))
      ((cartierPullbackTwistFunctor F p).obj M)) E ?_ z
  intro L hL F
  apply cartierPulledModuleMixedEulerDifference_vanish_of_closed_support K p L F i ?_ M hM
  intro N hN
  let := hN
  exact proper_cartierPulledModuleMixedEulerDifference_vanish_of_length K n hdim (i ≫ p) N L hL F

end MixedFujita
