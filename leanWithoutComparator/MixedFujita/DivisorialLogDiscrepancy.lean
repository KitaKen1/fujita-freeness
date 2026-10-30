/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.JacobianCriterionCharts

/-!
The log discrepancy of a divisorial valuation is 1 + ord_E K_{T/X} (step 6). Let ρ : T → X be a
dominant morphism over K of smooth integral schemes, c a chart at ρ(t), and c' a chart at t whose
j-th coordinate y_j vanishes at t and is prime in the local ring, so that E = {y_j = 0} is a prime
divisor through t with local ring S. In Taylor coordinates of c' centred at t, the monomial test
valuation with weight e_j is ord_E, and the log discrepancy 1 + v(det J) of this test valuation
has v(det J) = ord_E(a), where a is the determinant of the relative Jacobian of the stalk map at
t; a is the local equation of K_{T/X} at t, by the comparison of the function field and stalk
Jacobians. Hence A(ord_E) = 1 + ord_E(K_{T/X}): the log discrepancy of test valuations is the usual
log discrepancy of divisors, for every completion coordinate system at ρ(t).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

variable {n : ℕ} {K : Type u} [Field K] {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- A(ord_E) = 1 + ord_E(K_{T/X}) for E = {y_j = 0}: the e_j-weighted order of the formal Jacobian
determinant of the map of completed local rings is the order along E of the stalk Jacobian
determinant a, whose image in the function field is the local equation J(c, c') of K_{T/X}. -/
theorem divisorialLogDiscrepancy_eq_relativeCanonical [CharZero K] (ρ : T ⟶ X) [IsDominant ρ]
    [ρ.IsOver (Spec (CommRingCat.of K))] (t : T) (c : EtaleChart K X n) (hc : ρ t ∈ c.U)
    (c' : EtaleChart K T n) (hc' : t ∈ c'.U) (j : Fin n) (β : X.presheaf.stalk (ρ t) →ₐ[K] K)
    (β' : T.presheaf.stalk t →ₐ[K] K)
    (hβ' : β' (etaleChartStalkCoords c' t hc' (MvPolynomial.X j)) = 0)
    [IsNoetherianRing (T.presheaf.stalk t)]
    (hprime : Prime (etaleChartStalkCoords c' t hc' (MvPolynomial.X j)))
    [(Ideal.span {etaleChartStalkCoords c' t hc' (MvPolynomial.X j)}).IsPrime] (S : Type*)
    [CommRing S] [Algebra (T.presheaf.stalk t) S]
    [IsLocalization.AtPrime S (Ideal.span {etaleChartStalkCoords c' t hc' (MvPolynomial.X j)})]
    [IsLocalRing S]
    (ep : AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk t)) (T.presheaf.stalk t) ≃ₐ[K]
      MvPowerSeries (Fin n) K)
    (hep : ∀ i, stalkTaylorExpansion t ep
      (etaleChartCenteredStalkCoords c' t hc' β' (MvPolynomial.X i)) = MvPowerSeries.X i)
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk (ρ t)))
      (X.presheaf.stalk (ρ t)) ≃ₐ[K] MvPowerSeries (Fin n) K) :
    (powerSeriesJacobian (schemeCompletedStalkMap ρ t ez ep)).det.weightedOrder (Pi.single j 1) =
        localAdicOrder S (algebraMap (T.presheaf.stalk t) S
          (etaleRelativeJacobian (schemeStalkMapAlgHom (K := K) ρ t)
            (etaleChartStalkCoords c (ρ t) hc) (etaleChartStalkCoords c' t hc')
            (etaleChartStalkCoords_formallyEtale c' t hc')).det) ∧
      stalkFunctionFieldAlgHom (K := K) t
          (etaleRelativeJacobian (schemeStalkMapAlgHom (K := K) ρ t)
            (etaleChartStalkCoords c (ρ t) hc) (etaleChartStalkCoords c' t hc')
            (etaleChartStalkCoords_formallyEtale c' t hc')).det =
        chartRelativeJacobianDet ρ c c' := by
  refine ⟨?_, (chartRelativeJacobianDet_eq_stalk ρ t c hc c' hc').symm⟩
  obtain ⟨ez₀, hez₀, -⟩ := etaleChart_exists_taylorCoordinates c (ρ t) hc β
  -- the test valuation side, in the centred coordinates
  rw [schemeTestValuation_jacobian_weightedOrder_eq_relative ρ t ez ez₀ ep
      (etaleChartCenteredStalkCoords c (ρ t) hc β) (etaleChartCenteredStalkCoords c' t hc' β')
      (etaleChartCenteredStalkCoords_formallyEtale c' t hc' β') hez₀ hep (Pi.single j 1),
    etaleRelativeJacobian_eq_of_sub_const _ (etaleChartStalkCoords c (ρ t) hc) _ _
      (etaleChartCenteredStalkCoords_variable c (ρ t) hc β) (etaleChartStalkCoords c' t hc') _
      (etaleChartStalkCoords_formallyEtale c' t hc') _ _
      (etaleChartCenteredStalkCoords_variable c' t hc' β'), stalkTaylorExpansion_apply]
  -- the divisor side: the coordinate y_j is sent to X_j
  have hcent := etaleChartCenteredStalkCoords_variable c' t hc' β' j
  have hα : rationalAffineGermPoint (U := c'.U) t hc' β' (c'.coords (MvPolynomial.X j)) = 0 := hβ'
  rw [hα, map_zero, sub_zero] at hcent
  have he : ep (algebraMap (T.presheaf.stalk t)
      (AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk t)) (T.presheaf.stalk t))
        (etaleChartStalkCoords c' t hc' (MvPolynomial.X j))) = MvPowerSeries.X j := by
    have h1 := hep j
    rw [hcent, stalkTaylorExpansion_apply] at h1
    exact h1
  exact (localAdicOrder_localization_eq_weightedOrder ep hprime j he S _).symm

end MixedFujita
