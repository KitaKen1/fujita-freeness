/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCChartLocalProduct

/-!
The monomial of component equations as a monomial in the chart coordinates (step 9, strict
transform charts).

In a simple normal crossing chart the component equation of a member ξ_i is the coordinate
y_{σ i} when the member has a coordinate and 1 otherwise. For natural exponents e_i the monomial
∏_i (component equation)^{e_i} of the local products (check-337) is the image in the function field
of the chart monomial ∏_s y_s^{m_s} with m_s = Σ_{σ i = s} e_i
(`sncChart_component_monomial_eq`), so the local product equations become equations of chart
functions, which can be sent to the ring B of a strict transform chart (check-334).
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

section Monomial

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  {n : ℕ}

/-- The monomial of the component equations with natural exponents is the image of the chart
monomial with the exponents gathered by coordinate. -/
theorem sncChart_component_monomial_eq (c : EtaleChart K X n) {r : ℕ}
    (σ : Fin r → Option (Fin n)) (e : Fin r → ℕ) :
    ((∏ i, sncChartComponentEquation c σ i ^ (e i : ℤ) : X.functionFieldˣ) : X.functionField) =
      X.germToFunctionField c.U (∏ s : Fin n, c.coords (MvPolynomial.X s) ^
        (∑ i ∈ Finset.univ.filter (fun i => σ i = some s), e i)) := by
  classical
  have hcoord : ∀ s : Fin n, X.germToFunctionField c.U (c.coords (MvPolynomial.X s)) =
      (etaleChartCoordinateRationalUnit c s : X.functionField) := fun s => by
    rw [← etaleChartFunctionFieldCoords_X]
    rfl
  rw [Units.coe_prod, map_prod]
  simp_rw [map_pow]
  rw [show (∏ s : Fin n, X.germToFunctionField c.U (c.coords (MvPolynomial.X s)) ^
      (∑ i ∈ Finset.univ.filter (fun i => σ i = some s), e i)) =
      ∏ s : Fin n, ∏ i : Fin r, (if σ i = some s then
        X.germToFunctionField c.U (c.coords (MvPolynomial.X s)) ^ e i else 1) from
    Finset.prod_congr rfl fun s _ => by rw [← Finset.prod_pow_eq_pow_sum, Finset.prod_filter]]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [zpow_natCast, Units.val_pow_eq_pow_val]
  unfold sncChartComponentEquation
  cases hσ : σ i with
  | none => simp
  | some a => simp [hcoord]

end Monomial

end MixedFujita
