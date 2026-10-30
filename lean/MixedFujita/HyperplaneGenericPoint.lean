/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.NondegenerateStrictTransformCharts

/-!
The generic point of a coordinate hyperplane and the sign of the relative canonical divisor
(step 9, inputs of the strict transform charts).

For global étale coordinates x_0, …, x_N of a smooth K-domain A with (x_0) prime, the prime (x_0)
is a codimension-one point b of Spec A (Krull's principal ideal theorem), and the first coordinate
of the global chart has order one there (`exists_hyperplane_generic_point`): it vanishes at b and
the stalk is a discrete valuation ring. So div(x_0) has coefficient h = 1 along the hyperplane,
which makes its strict transform a member of the family of a principalizing model with h = 1
(check-341). On a model of a smooth variety the crepant boundary of the pair (Y, 0), the negative
of the relative canonical divisor, has nonpositive coefficients
(`crepantBoundaryCartier_coefficient_nonpos`): k ≥ 0 for the bad member in check-340.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

universe u

section GenericPoint

variable {K : Type u} [Field K]

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra
  functionFieldBaseAlgebra specAlgebraOver

/-- The generic point of the hyperplane x_0 = 0 of global étale coordinates is a codimension-one
point at which the first coordinate has order one. -/
theorem exists_hyperplane_generic_point (A : Type u) [CommRing A] [IsDomain A] [Algebra K A]
    [IsNoetherianRing A] {N : ℕ} [SmoothOfRelativeDimension (N + 1) (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of K))]
    (φ : MvPolynomial (Fin (N + 1)) K →ₐ[K] A) (hφ : φ.toRingHom.FormallyEtale)
    [(Ideal.span {φ (MvPolynomial.X 0)}).IsPrime] :
    ∃ b : CodimensionOnePoint (Spec (CommRingCat.of A)),
      (b : Spec (CommRingCat.of A)).asIdeal = Ideal.span {φ (MvPolynomial.X 0)} ∧
      (Spec (CommRingCat.of A)).ord
        (etaleChartCoordinateRationalUnit (specAlgebraEtaleChart φ hφ) 0 :
          (Spec (CommRingCat.of A)).functionField) (b : Spec (CommRingCat.of A)) = 1 := by
  haveI : Algebra.Smooth K A := algebraSmooth_of_smoothOfRelativeDimension (K := K) (n := N + 1)
  have hsm := specAlgebraOver_smooth (K := K) A
  let P : Ideal A := Ideal.span {φ (MvPolynomial.X 0)}
  let e : Spec (CommRingCat.of A) := ⟨P, inferInstance⟩
  have hx0 : φ (MvPolynomial.X 0) ≠ 0 := etaleCoordinate_ne_zero φ hφ 0
  have hcoh : Order.coheight e = 1 := by
    rw [← idealHeight_eq_coheight]
    change P.height = 1
    apply le_antisymm
    · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes P P
        (by rw [Ideal.minimalPrimes_eq_subsingleton_self]; rfl)
    · rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
      intro h
      apply hx0
      have hmem : φ (MvPolynomial.X 0) ∈ P := Ideal.subset_span rfl
      rw [h] at hmem
      exact (Submodule.mem_bot A).mp hmem
  let eC : CodimensionOnePoint (Spec (CommRingCat.of A)) := ⟨e, hcoh⟩
  haveI : IsDiscreteValuationRing ((Spec (CommRingCat.of A)).presheaf.stalk (eC : _)) :=
    smoothOverField_codimensionOne_stalk_DVR (K := K) eC
  refine ⟨eC, rfl, ?_⟩
  apply etaleChart_coordinate_ord_one (specAlgebraEtaleChart φ hφ) 0 eC trivial
  change ¬ IsUnit ((Spec (CommRingCat.of A)).presheaf.germ ⊤ e trivial
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (φ (MvPolynomial.X 0))))
  rw [spec_germ_isUnit_iff, not_not]
  exact Ideal.subset_span rfl

end GenericPoint

section Sign

variable {K : Type u} [Field K] {n : ℕ} {Y T : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))] [SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of K))]
  [IsIntegral T] [IsLocallyNoetherian T] [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ Y) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- The crepant boundary of the smooth pair (Y, 0) on a model, the negative of the relative
canonical divisor, has nonpositive coefficients. -/
theorem crepantBoundaryCartier_coefficient_nonpos
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ)) (cY : EtaleChart K Y n)
    (cT : EtaleChart K T n) (z : T) :
    cartierCoefficient (crepantBoundaryCartier ρ hρ cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) cT
      etaleCharts_cover) z ≤ 0 := by
  rw [crepantBoundaryCartier_eq_neg_discrepancy, cartierCoefficient_neg]
  have h := zeroBoundary_logDiscrepancy_coefficient_nonneg cY ρ hρ cT z
  linarith

end Sign

end MixedFujita
