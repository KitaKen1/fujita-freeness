/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FibreChartGerms
public import MixedFujita.AmpleRelationNormalization

/-!
Charts with the same coordinates in the function field (step 10, R4-3).

The chart invariants that enter the local equations of the canonical divisor and of the boundary
depend only on the germs of the coordinates:
* `etaleChartFunctionFieldCoords_eq_of_germ`: charts whose coordinates have the same germs have the
  same coordinates in the function field;
* `etaleChartCanonicalEquation_congr`: then they have the same canonical equations (the bases of
  differentials agree, `etaleCoordinateBasis_congr`);
* `etaleChartCoordinateRationalUnit_congr`, `logTwistMonomial_congr`: and the same coordinate units
  and coordinate monomials.

Also the map `T → T_A` to the closure pulls the homogeneous equations of `T_A` back to those of `T`
(`projectiveClosureMap_homogeneousEquation`).

On `T_K` this compares the charts of `T` (with the coordinates `y_i`) with the fibre charts of the
closure (with the spread coordinates `ψ_i`, check 536).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra

universe u

section Charts

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  {n : ℕ}

/-- Equal coordinates give equal bases of differentials. -/
theorem etaleCoordinateBasis_congr {R : Type u} [CommRing R] [Algebra K R]
    {x x' : MvPolynomial (Fin n) K →ₐ[K] R} (h : x = x') (hx : x.toRingHom.FormallyEtale)
    (hx' : x'.toRingHom.FormallyEtale) : etaleCoordinateBasis x hx = etaleCoordinateBasis x' hx' := by
  subst h
  rfl

/-- **Charts whose coordinates have the same germs have the same coordinates in the function
field.** -/
theorem etaleChartFunctionFieldCoords_eq_of_germ {c c' : EtaleChart K X n}
    (h : ∀ j, X.germToFunctionField c.U (c.coords (MvPolynomial.X j)) =
      X.germToFunctionField c'.U (c'.coords (MvPolynomial.X j))) :
    etaleChartFunctionFieldCoords c = etaleChartFunctionFieldCoords c' := by
  apply MvPolynomial.algHom_ext
  intro j
  exact h j

/-- **Charts with the same function field coordinates have the same canonical equations.** -/
theorem etaleChartCanonicalEquation_congr {c₀ c₀' c c' : EtaleChart K X n}
    (h₀ : etaleChartFunctionFieldCoords c₀ = etaleChartFunctionFieldCoords c₀')
    (h : etaleChartFunctionFieldCoords c = etaleChartFunctionFieldCoords c') :
    etaleChartCanonicalEquation c₀ c = etaleChartCanonicalEquation c₀' c' := by
  apply Units.ext
  rw [etaleChartCanonicalEquation_val, etaleChartCanonicalEquation_val, etaleChartBasis,
    etaleChartBasis, etaleChartBasis, etaleChartBasis,
    etaleCoordinateBasis_congr h (etaleChartFunctionFieldCoords_formallyEtale c)
      (etaleChartFunctionFieldCoords_formallyEtale c'),
    etaleCoordinateBasis_congr h₀ (etaleChartFunctionFieldCoords_formallyEtale c₀)
      (etaleChartFunctionFieldCoords_formallyEtale c₀')]

/-- Charts whose coordinates have the same germs have the same coordinate units. -/
theorem etaleChartCoordinateRationalUnit_congr {c c' : EtaleChart K X n}
    (h : ∀ j, X.germToFunctionField c.U (c.coords (MvPolynomial.X j)) =
      X.germToFunctionField c'.U (c'.coords (MvPolynomial.X j))) (j : Fin n) :
    etaleChartCoordinateRationalUnit c j = etaleChartCoordinateRationalUnit c' j := by
  apply Units.ext
  rw [etaleChartCoordinateRationalUnit, etaleChartCoordinateRationalUnit,
    regularEquationRationalUnit_val, regularEquationRationalUnit_val]
  exact h j

/-- Charts whose coordinates have the same germs have the same coordinate monomials. -/
theorem logTwistMonomial_congr {c c' : EtaleChart K X n}
    (h : ∀ j, X.germToFunctionField c.U (c.coords (MvPolynomial.X j)) =
      X.germToFunctionField c'.U (c'.coords (MvPolynomial.X j))) (S : Finset (Fin n))
    (r : Fin n → ℕ) : logTwistMonomial c S r = logTwistMonomial c' S r := by
  rw [logTwistMonomial, logTwistMonomial]
  exact Finset.prod_congr rfl fun j _ => by rw [etaleChartCoordinateRationalUnit_congr h j]

end Charts

section Closure

variable {n : ℕ} {A S : Type u} [CommRing A] [CommRing S] (c : A →+* S) {Y : Scheme.{u}}
  (e : Y ⟶ polynomialProjectiveScheme n S)

/-- **The map to the closure pulls the homogeneous equations back to those of `Y`.** -/
theorem projectiveClosureMap_homogeneousEquation (k : Fin n) (d : ℕ) (f : MvPolynomial (Fin n) A)
    (hf : f.IsHomogeneous d) :
    (projectiveClosureMap c e).appLE _ _ (projectiveClosureMap_preimage_chart c e k).ge
        (projectivePullbackHomogeneousEquation (projectiveClosureι c e) k d f hf) =
      projectivePullbackHomogeneousEquation e k d (MvPolynomial.map c f) (hf.map c) := by
  rw [projectivePullbackHomogeneousEquation, projectivePullbackHomogeneousEquation,
    ← coefficientMap_appLE_homogeneousEquation c k d f hf]
  change (projectiveClosureMap c e).appLE
      ((projectiveClosureι c e) ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) A)
        (MvPolynomial.X k)) _ (projectiveClosureMap_preimage_chart c e k).ge
      ((projectiveClosureι c e).app _ (projectiveHomogeneousEquation A k d f hf)) = e.app _ _
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE, ← ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE,
    appLE_congr_hom (projectiveClosureMap_comp_ι c e)]
  rfl

end Closure

end MixedFujita
