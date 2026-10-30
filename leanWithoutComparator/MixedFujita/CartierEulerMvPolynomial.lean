/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SquarefreeNewtonCoefficient
public import MixedFujita.TopDimensionalMixedEuler

/-! 元Cartier方向の実多変数Euler多項式と整数最高次係数。 See reports/check-223-multivariate-euler-intersection.json for the verified scope. Mixed positivity and the manuscript numerical-dimension dictionary remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
universe u
namespace MixedFujita
open Finset
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- The multivariate polynomial from the ORIGINAL Cartier sheaf Euler
characteristic, with no replacement definition of numerical dimension. -/
noncomputable def cartierEulerMvPolynomial
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] (r n : ℕ)
    (D : Fin r → CartierDivisor X) (E : CartierDivisor X) : MvPolynomial (Fin r) ℚ :=
  multivariateNewtonPolynomial r n D (fun F : CartierDivisor X =>
    Scheme.Modules.eulerChar (X ↘ Spec (CommRingCat.of K)) F.sheaf) E


/-- The original multivariate Euler polynomial has ordinary total degree at most n. -/
theorem cartierEulerMvPolynomial_totalDegree_le
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] (r n : ℕ)
    (D : Fin r → CartierDivisor X) (E : CartierDivisor X) :
    (cartierEulerMvPolynomial K r n D E).totalDegree ≤ n :=
  multivariateNewtonPolynomial_totalDegree_le r n D _ E


/-- The original proper Cartier Euler function is the value of the actual
multivariate polynomial at every signed integer tuple. -/
theorem proper_cartierEulerMvPolynomial_eval_int
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (r n : ℕ) (hdim : topologicalKrullDim X ≤ n)
    (D : Fin r → CartierDivisor X) (E : CartierDivisor X) (z : Fin r → ℤ) :
    MvPolynomial.eval (fun i => (z i : ℚ)) (cartierEulerMvPolynomial K r n D E) =
      (Scheme.Modules.eulerChar (X ↘ Spec (CommRingCat.of K)) (E + ∑ i, z i • D i).sheaf : ℚ) := by
  exact multivariateNewtonPolynomial_eval_int_of_mixed_nilpotence r n D
    (fun F : CartierDivisor X => Scheme.Modules.eulerChar (X ↘ Spec (CommRingCat.of K)) F.sheaf) E
    (fun L hL F => proper_cartierMixedEulerDifference_vanish_of_length K n hdim L hL F) z


/-- The original squarefree highest coefficient is exactly its actual
integer mixed difference, in the ordinary mixed-intersection convention. -/
theorem cartierEulerMvPolynomial_squarefree_top_coeff
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] (n : ℕ)
    (D : Fin n → CartierDivisor X) (E : CartierDivisor X) :
    (cartierEulerMvPolynomial K n n D E).coeff (squarefreeExponent n) =
      (cartierMixedEulerDifference K (List.ofFn D) E : ℚ) :=
  multivariateNewtonPolynomial_squarefree_top_coeff n D _ E

end MixedFujita
