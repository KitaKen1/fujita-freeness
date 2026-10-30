/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.PulledModuleEulerMvPolynomial
public import MixedFujita.CartierEulerMvPolynomial

/-! 一意な実Euler多項式の通常最高次係数としての混合Cartier交点数。 See reports/check-223-multivariate-euler-intersection.json for the verified scope. Mixed positivity and the manuscript numerical-dimension dictionary remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
universe u
namespace MixedFujita
open Finset
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Ordinary TOP mixed intersection for pulled Cartier bundles on a proper
source. The dimension/arity equality excludes lower Euler coefficients.
The theorem below proves the usual unique squarefree Euler-coefficient
definition, including arbitrary nonreduced sources. -/
noncomputable def cartierMixedIntersectionOn
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) (D : List (CartierDivisor X))
    (_hdim : topologicalKrullDim Y = D.length) : ℤ :=
  cartierPulledModuleMixedEulerDifference K p (SheafOfModules.unit Y.ringCatSheaf) D 0


/-- Ordinary TOP mixed Cartier intersection on the original proper integral
scheme, with its dimension equal to the number of supplied factors. -/
noncomputable def cartierMixedIntersection
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (D : List (CartierDivisor X)) (_hdim : topologicalKrullDim X = D.length) : ℤ :=
  cartierMixedEulerDifference K D 0


/-- The ordinary pulled intersection is the integer squarefree top
coefficient of the UNIQUE actual Euler polynomial in all signed variables.
Properness supplies genuine finite coherent cohomology internally. -/
theorem proper_cartierMixedIntersectionOn_unique_Euler_coefficient
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) (D : List (CartierDivisor X)) (hdim : topologicalKrullDim Y = D.length) :
    ∃! P : MvPolynomial (Fin D.length) ℚ,
      P.totalDegree ≤ D.length ∧
      (∀ z : Fin D.length → ℤ, MvPolynomial.eval (fun i => (z i : ℚ)) P =
        (Scheme.Modules.eulerChar (Y ↘ Spec (CommRingCat.of K))
          ((Scheme.Modules.pullback p).obj (∑ i, z i • D.get i).sheaf) : ℚ)) ∧
      P.coeff (squarefreeExponent D.length) = (cartierMixedIntersectionOn K p D hdim : ℚ) := by
  let O : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let : O.IsCoherent := invertible_module_isCoherent (X := Y) O
  let P := cartierPulledModuleEulerMvPolynomial K p O D.length D.length D.get 0
  have hdeg : P.totalDegree ≤ D.length := cartierPulledModuleEulerMvPolynomial_totalDegree_le ..
  have heval (z : Fin D.length → ℤ) : MvPolynomial.eval (fun i => (z i : ℚ)) P =
      (Scheme.Modules.eulerChar (Y ↘ Spec (CommRingCat.of K))
        ((Scheme.Modules.pullback p).obj (∑ i, z i • D.get i).sheaf) : ℚ) := by
    have h := proper_cartierPulledModuleEulerMvPolynomial_eval_int K p O D.length D.length
      hdim.le D.get 0 z
    let a : ((cartierPullbackTwistFunctor (0 + ∑ i, z i • D.get i) p).obj O) ≅
        (Scheme.Modules.pullback p).obj (∑ i, z i • D.get i).sheaf :=
      rightUnitor ((Scheme.Modules.pullback p).obj (0 + ∑ i, z i • D.get i).sheaf) ≪≫
        (Scheme.Modules.pullback p).mapIso
          (eqToIso (congrArg CartierDivisor.sheaf (zero_add (∑ i, z i • D.get i))))
    exact h.trans (congrArg (fun v : ℤ => (v : ℚ)) (moduleEulerChar_congr K a))
  have hcoeff : P.coeff (squarefreeExponent D.length) =
      (cartierMixedIntersectionOn K p D hdim : ℚ) := by
    simpa only [cartierMixedIntersectionOn, List.ofFn_get] using
      cartierPulledModuleEulerMvPolynomial_squarefree_top_coeff K p O D.length D.get 0
  refine ⟨P, ⟨hdeg, heval, hcoeff⟩, ?_⟩
  intro Q hQ
  apply rationalMvPolynomial_eq_of_eval_int
  intro z
  exact (hQ.2.1 z).trans (heval z).symm


/-- The original ordinary mixed intersection satisfies exactly the unique
squarefree actual multivariate Euler-polynomial definition, with an INTEGER
coefficient and no assumed polynomial or identification. -/
theorem proper_cartierMixedIntersection_unique_Euler_coefficient
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (D : List (CartierDivisor X)) (hdim : topologicalKrullDim X = D.length) :
    ∃! P : MvPolynomial (Fin D.length) ℚ,
      P.totalDegree ≤ D.length ∧
      (∀ z : Fin D.length → ℤ, MvPolynomial.eval (fun i => (z i : ℚ)) P =
        (Scheme.Modules.eulerChar (X ↘ Spec (CommRingCat.of K))
          (∑ i, z i • D.get i).sheaf : ℚ)) ∧
      P.coeff (squarefreeExponent D.length) = (cartierMixedIntersection K D hdim : ℚ) := by
  let P := cartierEulerMvPolynomial K D.length D.length D.get 0
  have hdeg : P.totalDegree ≤ D.length := cartierEulerMvPolynomial_totalDegree_le ..
  have heval (z : Fin D.length → ℤ) : MvPolynomial.eval (fun i => (z i : ℚ)) P =
      (Scheme.Modules.eulerChar (X ↘ Spec (CommRingCat.of K)) (∑ i, z i • D.get i).sheaf : ℚ) := by
    have h := proper_cartierEulerMvPolynomial_eval_int K D.length D.length hdim.le D.get 0 z
    exact h.trans (congrArg (fun v : ℤ => (v : ℚ)) (moduleEulerChar_congr K
      (eqToIso (congrArg CartierDivisor.sheaf (zero_add (∑ i, z i • D.get i))))))
  have hcoeff : P.coeff (squarefreeExponent D.length) = (cartierMixedIntersection K D hdim : ℚ) := by
    simpa only [cartierMixedIntersection, List.ofFn_get] using
      cartierEulerMvPolynomial_squarefree_top_coeff K D.length D.get 0
  refine ⟨P, ⟨hdeg, heval, hcoeff⟩, ?_⟩
  intro Q hQ
  apply rationalMvPolynomial_eq_of_eval_int
  intro z
  exact (hQ.2.1 z).trans (heval z).symm


/-- Identity pullback gives the original ordinary mixed intersection. -/
theorem cartierMixedIntersectionOn_id
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (D : List (CartierDivisor X)) (hdim : topologicalKrullDim X = D.length) :
    cartierMixedIntersectionOn K (𝟙 X) D hdim = cartierMixedIntersection K D hdim :=
  cartierPulledModuleMixedEulerDifference_id_unit K D 0


/-- Every base twist computes the SAME original ordinary top intersection. -/
theorem proper_cartierMixedIntersection_eq_mixedEuler_any_base
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (D : List (CartierDivisor X)) (hdim : topologicalKrullDim X = D.length)
    (E : CartierDivisor X) :
    cartierMixedIntersection K D hdim = cartierMixedEulerDifference K D E :=
  proper_cartierMixedEulerDifference_top_base_independent K D.length hdim.le D rfl 0 E

end MixedFujita
