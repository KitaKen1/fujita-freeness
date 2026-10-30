/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCBoundaryKlt

/-!
Orders of the components of a simple normal crossing family along a prime divisor of a smooth
birational model (step 12, section 6.2 of the manuscript).

Let X be smooth over a field with a simple normal crossing family ξ_1, …, ξ_r of codimension-one
points, ρ : T → X a birational morphism from a smooth T and t a codimension-one point of T.
There are nonnegative integers o_1, …, o_r, the orders at t of the pullbacks of the coordinates
cutting out the members of the family near ρ(t), such that

* o_i ≠ 0 only if ρ(t) lies in the closure of ξ_i;
* for every Cartier divisor B of X supported on the family, the coefficient of ρ*B at t is
  Σ_i (coefficient of B at ξ_i) · o_i;
* for every boundary B supported on the family and every denominator d, d times the log
  discrepancy of t, d + (coefficient of the discrepancy divisor at t), is at least
  Σ_i (d − coefficient of B at ξ_i) · o_i.

One vector serves all divisors at once: the local product formula holds on any simple normal
crossing chart at ρ(t). These are the numbers ord_F(E_j) and the inequality r_F ≤ a_F of the
manuscript, on actual models.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

section Coordinates

variable {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
  [IsLocallyNoetherian X] [IsLocallyNoetherian T]
  (ρ : T ⟶ X) [IsDominant ρ]

omit [IsLocallyNoetherian X] in
/-- The pullback of the coordinate of a member of a simple normal crossing family has order zero
at every point not over the closure of that member: the coordinate is invertible there. -/
theorem sncChartComponentEquation_pullback_ord_eq_zero_of_notMem_closure
    {K : Type u} [Field K] [X.Over (Spec (CommRingCat.of K))] {n r : ℕ}
    (c : EtaleChart K X n) (ξ : Fin r → X) (σ : Fin r → Option (Fin n))
    (hcsnc : IsSNCChart c ξ σ) (t : T) (hc : ρ t ∈ c.U) (i : Fin r)
    (hnot : ρ t ∉ closure ({ξ i} : Set X)) :
    T.ord ((dominantFunctionFieldMap ρ).hom
      (sncChartComponentEquation c σ i : X.functionField)) t = 0 := by
  cases hσ : σ i with
  | none =>
    simp only [sncChartComponentEquation, hσ, Option.elim_none, Units.val_one,
      map_one, TauCeti.AlgebraicGeometry.Scheme.ord_one]
  | some a =>
    have hset := hcsnc.2 i
    rw [hσ, Option.elim_some] at hset
    have hb : ρ t ∈ X.basicOpen (c.coords (MvPolynomial.X a)) := by
      by_contra hb
      apply hnot
      have hmem : ρ t ∈ X.zeroLocus ({c.coords (MvPolynomial.X a)} : Set Γ(X, c.U)) ∩ c.U :=
        ⟨by rw [Scheme.zeroLocus_singleton]; exact hb, hc⟩
      rw [← hset] at hmem
      exact hmem.1
    have hunit : IsUnit (X.presheaf.germ c.U (ρ t) hc (c.coords (MvPolynomial.X a))) :=
      (X.mem_basicOpen _ (ρ t) hc).mp hb
    simp only [sncChartComponentEquation, hσ, Option.elim_some,
      etaleChartCoordinateRationalUnit, regularEquationRationalUnit_val]
    rw [← X.algebraMap_germ_eq_germToFunctionField hc,
      dominantFunctionFieldMap_algebraMap]
    exact scheme_ord_stalk_unit t (hunit.map (ρ.stalkMap t).hom).unit

end Coordinates

section Orders

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra

variable {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian X] [IsLocallyNoetherian T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

/-- The orders of the members of a simple normal crossing family along a prime divisor of a
smooth birational model: nonnegative integers, zero for the members whose closure does not
contain the image of the prime, computing the coefficient of the pullback of every Cartier
divisor supported on the family, and bounding the log discrepancy of the prime from below for
every boundary supported on the family. -/
theorem exists_snc_orders_at_prime {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (t : CodimensionOnePoint T) :
    ∃ o : Fin r → ℤ, (∀ i, 0 ≤ o i) ∧
      (∀ i, o i ≠ 0 → ρ (t : T) ∈ closure ({ξ i} : Set X)) ∧
      (∀ B : CartierDivisor X, (∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
          cartierCoefficient B (z : X) = 0) →
        cartierCoefficient (cartierPullback ρ B) (t : T) =
          ∑ i, cartierCoefficient B (ξ i) * o i) ∧
      ∀ (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (d : ℕ) (B : CartierDivisor X),
        (∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
          cartierCoefficient B (z : X) = 0) → ∀ c'₀ : EtaleChart K T n,
        (d : ℤ) * ∑ i, o i - ∑ i, cartierCoefficient B (ξ i) * o i ≤
          (d : ℤ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
            (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
            c'₀ etaleCharts_cover) (t : T) := by
  have : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnorm : ∀ z : X, IsIntegrallyClosed (X.presheaf.stalk z) :=
    isSNCFamily_stalk_isIntegrallyClosed hsnc
  have : ∀ z : CodimensionOnePoint X, IsRegularLocalRing (X.presheaf.stalk (z : X)) :=
    fun z => isSNCFamily_stalk_regular hsnc (z : X)
  have : ∀ z : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (z : X)) :=
    fun z => inferInstance
  obtain ⟨c, σ, hc, hcsnc⟩ := hsnc (ρ (t : T))
  obtain ⟨c', hc'⟩ : ∃ c' : EtaleChart K T n, (t : T) ∈ c'.U :=
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := T) (n := n)).symm ▸
      Opens.mem_top (t : T))
  have hP2 : ∀ B : CartierDivisor X, (∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient B (z : X) = 0) →
      cartierCoefficient (cartierPullback ρ B) (t : T) =
        ∑ i, cartierCoefficient B (ξ i) * T.ord ((dominantFunctionFieldMap ρ).hom
          (sncChartComponentEquation c σ i : X.functionField)) (t : T) := by
    intro B hsupport
    obtain ⟨f, hf, u, hu⟩ := normal_isSNCChart_boundary_local_product hnorm B c ξ hinj hξ σ
      hcsnc hsupport (ρ (t : T)) hc
    exact cartierPullback_coefficient_of_local_product ρ B t f hf u _ _ hu
  refine ⟨fun i => T.ord ((dominantFunctionFieldMap ρ).hom
      (sncChartComponentEquation c σ i : X.functionField)) (t : T),
    fun i => sncChartComponentEquation_pullback_ord_nonneg ρ c σ (t : T) hc i,
    fun i hoi => ?_, hP2, ?_⟩
  · by_contra hnot
    exact hoi (sncChartComponentEquation_pullback_ord_eq_zero_of_notMem_closure ρ c ξ σ hcsnc
      (t : T) hc i hnot)
  · intro c₀ f₀ d B hsupport c'₀
    rw [logDiscrepancyDivisor_boundary_add, cartierCoefficient_sub, cartierCoefficient_nsmul,
      hP2 B hsupport]
    have hloc := relativeCanonicalDivisor_isLocalEquationAt ρ c₀ etaleCharts_cover c'₀
      etaleCharts_cover (isUnit_chartRelativeJacobianDet_of_bijective ρ hρ c₀ c'₀)
      (t : T) c hc c' hc'
    unfold birationalRelativeCanonicalDivisor
    rw [cartierCoefficient_eq_ord hloc, IsUnit.unit_spec]
    have hsum := actual_snc_coordinate_sum_le_jacobian ρ hρ t c hc ξ σ hcsnc c' hc'
    have hd : (0 : ℤ) ≤ d := Int.natCast_nonneg d
    nlinarith [mul_le_mul_of_nonneg_left hsum hd]

end Orders

end MixedFujita
