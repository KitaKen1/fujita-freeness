/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SmoothPointInteriorWeight
public import MixedFujita.RealizationThresholdReduction
public import MixedFujita.SNCWeightProfileExistence

/-!
The ordinary-point interior construction on a possibly singular source.
Only the chosen point must belong to the reference etale chart and have zero boundary there:
D = div(f^d) locally, where the reference top form is f dx_1 ... dx_n.
No smoothness of the entire source or global zero-boundary presentation is required.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Extraction

variable {K : Type u} [Field K] {n : ℕ} {Y T : Scheme.{u}} [IsIntegral Y] [IsIntegral T]
  [Y.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]

/-- Translating source chart coordinates by constants preserves the relative Jacobian. -/
theorem chartRelativeJacobianDet_centered_source (σ : T ⟶ Y) [IsDominant σ]
    [σ.IsOver (Spec (CommRingCat.of K))] (c : EtaleChart K Y n)
    (α : Γ(Y, c.U) →ₐ[K] K) (cT : EtaleChart K T n) :
    chartRelativeJacobianDet σ (etaleChartCentered c α) cT =
      chartRelativeJacobianDet σ c cT := by
  have hX : ∀ i, etaleChartFunctionFieldCoords (etaleChartCentered c α) (MvPolynomial.X i) =
      etaleChartFunctionFieldCoords c (MvPolynomial.X i) -
        algebraMap K Y.functionField (α (c.coords (MvPolynomial.X i))) := by
    intro i
    change (sectionGermAlgHom (K := K) c.U)
      ((centeredPolynomialChart c.coords α) (MvPolynomial.X i)) =
      (sectionGermAlgHom (K := K) c.U) (c.coords (MvPolynomial.X i)) - _
    simp only [centeredPolynomialChart_variable, map_sub, AlgHom.commutes]
  exact congrArg Matrix.det (etaleRelativeJacobian_eq_of_sub_const
    (dominantFunctionFieldAlgHom (K := K) σ) _ _ _ hX
    (etaleChartFunctionFieldCoords cT) (etaleChartFunctionFieldCoords cT)
    (etaleChartFunctionFieldCoords_formallyEtale cT)
    (etaleChartFunctionFieldCoords_formallyEtale cT) (fun _ => 0) (by intro i; simp))

/-- Ordinary-point extraction needs one chart containing x, even when Y is singular elsewhere. -/
theorem exists_extraction_prime_at_chart_rational_point (hn : 1 ≤ n)
    (c : EtaleChart K Y n) (x : Y) (hx : x ∈ c.U) (β : Y.presheaf.stalk x →ₐ[K] K) :
    ∃ (U : Scheme.{u}) (_ : IsIntegral U) (_ : IsLocallyNoetherian U)
      (_ : U.Over (Spec (CommRingCat.of K)))
      (_ : SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K)))
      (σ : U ⟶ Y) (_ : IsDominant σ) (_ : σ.IsOver (Spec (CommRingCat.of K)))
      (_ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
      (cU : EtaleChart K U n) (e : U),
      Order.coheight e = 1 ∧ e ∈ cU.U ∧ σ e = x ∧
      U.ord (chartRelativeJacobianDet σ c cU) e = (n : ℤ) - 1 := by
  have hw : (fun _ : Fin n => 1) ≠ (0 : Fin n → ℕ) := fun h => by
    have h1 := congrFun h ⟨0, hn⟩
    simp at h1
  obtain ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, g, w', hg, hgw, he, hecU, hxe,
    hord, hjac⟩ := exists_toric_extraction_model
      (etaleChartCentered c (rationalAffineGermPoint x hx β)) x hx (fun _ => 1) hw
      (fun a _ => etaleChartCentered_germ_not_isUnit c x hx β a)
  have hw' : ∀ a, w' a = 1 := fun a =>
    Nat.dvd_one.mp ⟨g, (hgw a).trans (Nat.mul_comm _ _)⟩
  have hσe : σ e = x := by
    have hsp : σ e ⤳ x := specializes_iff_mem_closure.mpr hxe
    have hyU : σ e ∈ c.U := hsp.mem_open c.U.isOpen hx
    refine etaleChartCentered_eq_of_specializes c x hx β (σ e) hsp hyU fun a hunit => ?_
    have h1 := hord a
    rw [hw' a] at h1
    have h0 : U.ord (dominantFunctionFieldAlgHom (K := K) σ (etaleChartFunctionFieldCoords
        (etaleChartCentered c (rationalAffineGermPoint x hx β)) (MvPolynomial.X a))) e = 0 := by
      change U.ord ((dominantFunctionFieldMap σ).hom (Y.germToFunctionField c.U
        ((etaleChartCentered c (rationalAffineGermPoint x hx β)).coords (MvPolynomial.X a)))) e = 0
      rw [← Y.algebraMap_germ_eq_germToFunctionField hyU, dominantFunctionFieldMap_algebraMap]
      exact scheme_ord_stalk_unit e (hunit.map (σ.stalkMap e).hom).unit
    rw [h0] at h1
    exact absurd h1 (by norm_num)
  refine ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, he, hecU, hσe, ?_⟩
  rw [chartRelativeJacobianDet_centered_source] at hjac
  simpa [hw'] using hjac

end Extraction

section Discrepancy

variable {K : Type u} [Field K] {n : ℕ} {Y T : Scheme.{u}} [IsIntegral Y] [IsIntegral T]
  [Y.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [IsLocallyNoetherian T] [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]

/-- At a point with zero boundary in the reference chart, the discrepancy coefficient is
d times the relative Jacobian order. Only the smooth model T needs a global canonical divisor. -/
theorem logDiscrepancyDivisor_coefficient_of_local_boundary_zero
    (σ : T ⟶ Y) [IsDominant σ] [σ.IsOver (Spec (CommRingCat.of K))]
    (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (D₀ : CartierDivisor Y)
    (cT : EtaleChart K T n) (e : T) (he : e ∈ cT.U)
    (hD : D₀.IsLocalEquationAt (σ e) (fY ^ d)) :
    cartierCoefficient (logDiscrepancyDivisor n σ hσ cY fY d D₀ cT etaleCharts_cover) e =
      (d : ℤ) * T.ord (chartRelativeJacobianDet σ cY cT) e := by
  have hK : cartierCoefficient (canonicalDivisor n cT etaleCharts_cover) e = 0 := by
    rw [cartierCoefficient_eq_ord (canonicalDivisor_isLocalEquationAt cT etaleCharts_cover cT he),
      etaleChartCanonicalEquation_val, Module.Basis.det_self, Scheme.ord_one]
  have hF : dominantFunctionFieldAlgHom (K := K) σ (fY : Y.functionField) ≠ 0 :=
    (map_ne_zero _).mpr (Units.ne_zero fY)
  have hDcoef : cartierCoefficient (cartierPullback σ D₀) e =
      (d : ℤ) * T.ord (dominantFunctionFieldAlgHom (K := K) σ (fY : Y.functionField)) e := by
    rw [cartierCoefficient_eq_ord (cartierPullback_isLocalEquationAt σ D₀ e hD)]
    change T.ord (dominantFunctionFieldAlgHom (K := K) σ ((fY : Y.functionField) ^ d)) e = _
    rw [map_pow, scheme_ord_pow hF]
  rw [logDiscrepancyDivisor, cartierCoefficient_sub, cartierCoefficient_nsmul,
    pullbackFormDivisor, cartierCoefficient_add, hK, cartierCoefficient_principal, hDcoef]
  simp only [Units.val_mul, IsUnit.unit_spec]
  change (d : ℤ) * (0 + T.ord
    (dominantFunctionFieldAlgHom (K := K) σ (fY : Y.functionField) *
      chartRelativeJacobianDet σ cY cT) e) -
    (d : ℤ) * T.ord (dominantFunctionFieldAlgHom (K := K) σ (fY : Y.functionField)) e = _
  rw [Scheme.ord_mul hF (isUnit_chartRelativeJacobianDet_of_bijective σ hσ cY cT).ne_zero]
  ring

end Discrepancy

end MixedFujita
