/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCChartPullbackPrime

/-!
Local products in a simple normal crossing chart, as equations of chart functions (step 9,
strict transform charts).

A local equation f at a point t of a simple normal crossing chart c of a Cartier divisor B
supported on the family is a stalk unit times the monomial ∏ (component equations)^{coeff}
(`normal_isSNCChart_boundary_local_product` together with the uniqueness of local equations up to
stalk units). The stalk at t is the localization of Γ(c.U) at the prime of t, so the unit is a
fraction a/b of chart functions not vanishing at t, and f · b = a · ∏ in the function field
(`exists_chart_local_product`). These are the factorizations up to units at the point of the
strict transform charts (check-334), for the relative canonical divisor (det J(μ)), the pullback
of the hyperplane (μ(x_0) = y_0 w) and the pullbacks of the functions g_j.
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

section LocalProduct

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] {n : ℕ}

/-- A local equation at a point of a simple normal crossing chart of a divisor supported on the
family is a fraction a/b of chart functions not vanishing at the point times the monomial of the
component equations. -/
theorem exists_chart_local_product
    [∀ z : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (z : X))]
    (hnorm : ∀ z : X, IsIntegrallyClosed (X.presheaf.stalk z))
    (B : CartierDivisor X) (c : EtaleChart K X n) {r : ℕ} (ξ : Fin r → X)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (σ : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σ)
    (hsupport : ∀ z : CodimensionOnePoint X,
      (z : X) ∉ Set.range ξ → cartierCoefficient B (z : X) = 0)
    (t : X) (ht : t ∈ c.U) (f : X.functionFieldˣ) (hf : B.IsLocalEquationAt t f) :
    ∃ a b : Γ(X, c.U), a ∉ (c.isAffine.primeIdealOf ⟨t, ht⟩).asIdeal ∧
      b ∉ (c.isAffine.primeIdealOf ⟨t, ht⟩).asIdeal ∧
      (f : X.functionField) * X.germToFunctionField c.U b =
        X.germToFunctionField c.U a *
          ((∏ i, sncChartComponentEquation c σ i ^ cartierCoefficient B (ξ i) :
            X.functionFieldˣ) : X.functionField) := by
  obtain ⟨f', hf', u, hu⟩ := normal_isSNCChart_boundary_local_product hnorm B c ξ hinj hξ σ hc
    hsupport t ht
  obtain ⟨u', hu'⟩ := hf.exists_unit_mul_eq hf'
  -- the stalk at t is the localization of Γ(c.U) at the prime of t
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨t, ht⟩ : c.U)
  haveI := c.isAffine.isLocalization_stalk (⟨t, ht⟩ : c.U)
  let P := (c.isAffine.primeIdealOf ⟨t, ht⟩).asIdeal
  obtain ⟨⟨a, s⟩, hw0⟩ := IsLocalization.mk'_surjective P.primeCompl
    ((u' * u : (X.presheaf.stalk t)ˣ) : X.presheaf.stalk t)
  have hw : IsLocalization.mk' (X.presheaf.stalk t) a s =
      ((u' * u : (X.presheaf.stalk t)ˣ) : X.presheaf.stalk t) := hw0
  have hunit : IsUnit (IsLocalization.mk' (X.presheaf.stalk t) a s) := by
    rw [hw]
    exact (u' * u).isUnit
  have ha : a ∈ P.primeCompl :=
    (IsLocalization.AtPrime.isUnit_mk'_iff (X.presheaf.stalk t) P a s).mp hunit
  refine ⟨a, s, ha, s.2, ?_⟩
  have hgerm : ∀ g : Γ(X, c.U), X.germToFunctionField c.U g =
      algebraMap (X.presheaf.stalk t) X.functionField
        (algebraMap Γ(X, c.U) (X.presheaf.stalk t) g) := fun g =>
    (Scheme.algebraMap_germ_eq_germToFunctionField X ht g).symm
  have hspec := IsLocalization.mk'_spec (X.presheaf.stalk t) a s
  have hf'' : (f : X.functionField) = algebraMap (X.presheaf.stalk t) X.functionField
      ((u' * u : (X.presheaf.stalk t)ˣ) : X.presheaf.stalk t) *
        ((∏ i, sncChartComponentEquation c σ i ^ cartierCoefficient B (ξ i) :
          X.functionFieldˣ) : X.functionField) := by
    rw [← hu', hu, Units.val_mul, map_mul, mul_assoc]
  rw [hf'', hgerm, hgerm, ← hw, mul_right_comm, ← map_mul, hspec]

end LocalProduct

end MixedFujita
