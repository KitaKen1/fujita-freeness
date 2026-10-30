/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.DominantChartRelation
public import MixedFujita.PointClosureHyperplaneEquivalence

/-!
Ratios of boundary coordinates of two charts (step 10, R4-3).

On a simple normal crossing chart the component equation of `E_k` (the coordinate of `E_k`, or `1`)
is a local equation of `E_k` at every point of the chart
(`sncChartComponentEquation_isLocalEquationAt`). So on the overlap of two charts the two component
equations of `E_k` differ by a unit (`exists_boundaryRatio_unit`, check 534): the boundary coordinate
of one chart is a unit multiple of that of the other, or a unit.

On the closure, with the coordinates `ψ` of check 536 and units `w^A` spread from `T` (check 535),
the component sections (`componentSection`: the coordinate or `1`) satisfy the same relation
(`componentSection_relation`, injectivity of check 544). These relations make the Frobenius one-forms
of check 491 regular on the Čech intersections (R4-6).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] structureSectionsAlgebra Classical.propDecidable

universe u

section Ratio

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  [IsLocallyNoetherian X] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [∀ z : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (z : X))]
  (hnorm : ∀ z : X, IsIntegrallyClosed (X.presheaf.stalk z))
  {n r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
  (E : Fin r → CartierDivisor X)
  (hEc : ∀ (k : Fin r) (z : CodimensionOnePoint X),
    cartierCoefficient (E k) (z : X) = if (z : X) = ξ k then 1 else 0)

include hnorm hinj hξ hEc in
/-- **The component equation of `E_k` is a local equation on the whole chart.** -/
theorem sncChartComponentEquation_isLocalEquationAt (c : EtaleChart K X n)
    (σ : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σ) (k : Fin r) :
    ∀ x ∈ c.U, (E k).IsLocalEquationAt x (sncChartComponentEquation c σ k) := by
  intro x hx
  obtain ⟨f, hf, u, hu⟩ :=
    exists_isLocalEquationAt_eq_unit_mul_sncChartComponentEquation hnorm ξ hinj hξ E hEc c σ hc x
      hx k
  refine isLocalEquationAt_stalkUnit_mul hf u⁻¹ ?_
  rw [hu, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]

include hnorm hinj hξ hEc in
/-- **The component equations of two charts differ by a unit on the overlap.** -/
theorem exists_boundaryRatio_unit (c c' : EtaleChart K X n) (σ σ' : Fin r → Option (Fin n))
    (hc : IsSNCChart c ξ σ) (hc' : IsSNCChart c' ξ σ') (k : Fin r) :
    letI := integral_opens_inter_nonempty X c.U c'.U
    ∃ w : Γ(X, c.U ⊓ c'.U)ˣ, X.germToFunctionField (c.U ⊓ c'.U) (w : Γ(X, c.U ⊓ c'.U)) =
      ((sncChartComponentEquation c σ k * (sncChartComponentEquation c' σ' k)⁻¹ :
        X.functionFieldˣ) : X.functionField) := by
  let _ := integral_opens_inter_nonempty X c.U c'.U
  exact exists_unit_germ_eq_of_isLocalEquationAt
    (fun y hy => sncChartComponentEquation_isLocalEquationAt hnorm ξ hinj hξ E hEc c σ hc k y hy.1)
    (fun y hy => sncChartComponentEquation_isLocalEquationAt hnorm ξ hinj hξ E hEc c' σ' hc' k y
      hy.2)

end Ratio

section Closure

variable {A : Type u} [CommRing A] {X T : Scheme.{u}} [X.Over (Spec (CommRingCat.of A))] {n r : ℕ}

/-- The section on an open of the base giving the equation of `E_k`: the coordinate of `E_k`, or
`1`. -/
noncomputable def componentSection {V : X.Opens} (y : MvPolynomial (Fin n) A →ₐ[A] Γ(X, V))
    (σ : Fin r → Option (Fin n)) (k : Fin r) : Γ(X, V) :=
  (σ k).elim 1 fun i => y (MvPolynomial.X i)

variable [IsIntegral X] [IsIntegral T] (φ : T ⟶ X) [IsDominant φ]

omit [IsIntegral X] [IsDominant φ] in
/-- The germ of a component section is the component equation of a chart with the same coordinate
germs. -/
theorem pullbackGerm_componentSection {K : Type u} [Field K] [T.Over (Spec (CommRingCat.of K))]
    {V : X.Opens} [Nonempty (φ ⁻¹ᵁ V)] (y : MvPolynomial (Fin n) A →ₐ[A] Γ(X, V))
    (c : EtaleChart K T n)
    (hy : ∀ j, pullbackGerm φ V (y (MvPolynomial.X j)) =
      T.germToFunctionField c.U (c.coords (MvPolynomial.X j))) (σ : Fin r → Option (Fin n))
    (k : Fin r) :
    pullbackGerm φ V (componentSection y σ k) =
      (sncChartComponentEquation c σ k : T.functionField) := by
  rw [componentSection, sncChartComponentEquation]
  cases σ k with
  | none => simp
  | some i =>
    simp only [Option.elim_some]
    rw [hy, etaleChartCoordinateRationalUnit, regularEquationRationalUnit_val]

/-- **The component sections of two charts of the closure satisfy the ratio relation**, from the
germs on `T`. -/
theorem componentSection_relation {K : Type u} [Field K] [T.Over (Spec (CommRingCat.of K))]
    {V V' : X.Opens} [Nonempty (V ⊓ V' : X.Opens)] [Nonempty (φ ⁻¹ᵁ V)] [Nonempty (φ ⁻¹ᵁ V')]
    [Nonempty (φ ⁻¹ᵁ (V ⊓ V'))]
    (y : MvPolynomial (Fin n) A →ₐ[A] Γ(X, V)) (y' : MvPolynomial (Fin n) A →ₐ[A] Γ(X, V'))
    (c c' : EtaleChart K T n)
    (hy : ∀ j, pullbackGerm φ V (y (MvPolynomial.X j)) =
      T.germToFunctionField c.U (c.coords (MvPolynomial.X j)))
    (hy' : ∀ j, pullbackGerm φ V' (y' (MvPolynomial.X j)) =
      T.germToFunctionField c'.U (c'.coords (MvPolynomial.X j)))
    (σ σ' : Fin r → Option (Fin n)) (k : Fin r) (wA : Γ(X, V ⊓ V'))
    (hw : pullbackGerm φ (V ⊓ V') wA =
      ((sncChartComponentEquation c σ k * (sncChartComponentEquation c' σ' k)⁻¹ :
        T.functionFieldˣ) : T.functionField)) :
    X.presheaf.map (homOfLE (inf_le_left : V ⊓ V' ≤ V)).op (componentSection y σ k) =
      wA * X.presheaf.map (homOfLE (inf_le_right : V ⊓ V' ≤ V')).op
        (componentSection y' σ' k) := by
  apply pullbackGerm_injective_of_isDominant φ (V ⊓ V')
  rw [map_mul, pullbackGerm_restrict, pullbackGerm_restrict, hw,
    pullbackGerm_componentSection φ y c hy σ k, pullbackGerm_componentSection φ y' c' hy' σ' k,
    Units.val_mul, Units.val_inv_eq_inv_val, mul_assoc, inv_mul_cancel₀ (Units.ne_zero _),
    mul_one]

end Closure

end MixedFujita
