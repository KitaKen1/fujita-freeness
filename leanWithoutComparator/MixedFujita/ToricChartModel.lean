/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.AffineEtaleChartModel
public import MixedFujita.ToricChartAlgebra
public import MixedFujita.EtaleChartPolynomialMaps
public import MixedFujita.SmoothProperCurveSections

/-!
The toric chart over an étale chart extracts a monomial valuation (step 12, section 6.1 of the
manuscript). Let c be an étale chart of an integral scheme locally of finite type over a field,
y a point of the chart and w ≠ 0 weights on the coordinates, supported on coordinates vanishing at
y. The stellar subdivision gives a composite M of blow-up charts of strata inside the support with
column k equal to w/g. The spectrum of the ring of the toric chart of M is a smooth affine
birational model with a prime divisor e, a component of u_k = 0, with y in the closure of its
image, along which the coordinate x_a has order w_a/g and the Jacobian determinant of the model
has order Σ_a w_a/g - 1: the monomial valuation with weights w is g times the order along e, and
its log discrepancy is Σ_a w_a.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] {n : ℕ}

attribute [local instance] cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- The toric chart extracting the monomial valuation with weights w at a point y of an étale
chart: a smooth affine birational model with a codimension-one point e over a point specializing
to y, along which the coordinates of the chart have orders w/g and the Jacobian determinant has
order Σ_a w_a/g - 1. -/
theorem exists_toric_extraction_model (c : EtaleChart K X n) (y : X) (hy : y ∈ c.U)
    (w : Fin n → ℕ) (hw : w ≠ 0)
    (hwy : ∀ a, w a ≠ 0 → ¬ IsUnit (X.presheaf.germ c.U y hy (c.coords (MvPolynomial.X a)))) :
    ∃ (U : Scheme.{u}) (_ : IsIntegral U) (_ : IsLocallyNoetherian U)
      (_ : U.Over (Spec (CommRingCat.of K)))
      (_ : SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K)))
      (σ : U ⟶ X) (_ : IsDominant σ) (_ : σ.IsOver (Spec (CommRingCat.of K)))
      (_ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
      (cU : EtaleChart K U n) (e : U) (g : ℕ) (w' : Fin n → ℕ),
      1 ≤ g ∧ (∀ a, w a = g * w' a) ∧ Order.coheight e = 1 ∧ e ∈ cU.U ∧
      y ∈ closure ({σ e} : Set X) ∧
      (∀ a, U.ord (dominantFunctionFieldAlgHom (K := K) σ
        (etaleChartFunctionFieldCoords c (MvPolynomial.X a))) e = (w' a : ℤ)) ∧
      U.ord (chartRelativeJacobianDet σ c cU) e = (∑ a, (w' a : ℤ)) - 1 := by
  classical
  obtain ⟨L, k, g, hg, hL, hLS⟩ := exists_toricChart_column_supported w hw
  obtain ⟨N, hMN, hNM⟩ := exists_int_inverse_toricChartProduct L
  -- the ring of the chart as an étale algebra over the polynomial ring
  let _ : Algebra (MvPolynomial (Fin n) K) Γ(X, c.U) := c.coords.toRingHom.toAlgebra
  have : IsScalarTower K (MvPolynomial (Fin n) K) Γ(X, c.U) :=
    IsScalarTower.of_algebraMap_eq fun k => (c.coords.commutes k).symm
  have : Algebra.Etale (MvPolynomial (Fin n) K) Γ(X, c.U) := etaleChart_coords_etale c
  have : Nonempty c.U := c.nonempty
  have hdomB : IsDomain (ToricChartAlgebra K (toricChartProduct L) Γ(X, c.U)) :=
    toricChartAlgebra_isDomain K (toricChartProduct L) Γ(X, c.U) N hMN hNM
  have hkk : w k ≠ 0 := by
    rw [hL k]
    have := one_le_toricChartProduct_diag L k
    exact Nat.mul_ne_zero (by omega) (by omega)
  -- the prime of the toric chart over y
  obtain ⟨𝔓, h𝔓prime, h𝔓comap, h𝔓k⟩ := exists_toricChart_prime K (toricChartProduct L)
    Γ(X, c.U) {a | w a ≠ 0}
    (fun i hi l => toricChartProduct_apply_of_forall_notMem L i
      (fun p hp hip => hi (hLS p hp i hip)) l)
    (one_le_toricChartProduct_diag L) (c.isAffine.primeIdealOf ⟨y, hy⟩).asIdeal
    (fun i hi => by
      let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨y, hy⟩ : c.U)
      have hloc := c.isAffine.isLocalization_stalk (⟨y, hy⟩ : c.U)
      by_contra hnot
      exact hwy i hi ((IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk y)
        (c.isAffine.primeIdealOf ⟨y, hy⟩).asIdeal (c.coords (MvPolynomial.X i))).mpr hnot))
  obtain ⟨U, hUint, hUnoeth, hUover, hUsm, σ, hσdom, hσover, hσbij, cU, e, he, hrel, hcoh,
      hclos, hnonunit⟩ :=
    exists_affine_birational_model c (toricChartInclusion K (toricChartProduct L) Γ(X, c.U))
      (toricChartInclusion_injective K (toricChartProduct L) Γ(X, c.U) N hMN hNM)
      (toricChartInclusion_exists_fraction K (toricChartProduct L) Γ(X, c.U) N hMN hNM)
      (toricChartCoords K (toricChartProduct L) Γ(X, c.U))
      (toricChartCoords_etale K (toricChartProduct L) Γ(X, c.U))
      (toricSubst (toricChartProduct L))
      (fun p => toricChartInclusion_algebraMap K (toricChartProduct L) Γ(X, c.U) p)
      y hy 𝔓 h𝔓comap (MvPolynomial.X k) (h𝔓k k hkk)
      (toricChartCoords_X_ne_zero K (toricChartProduct L) Γ(X, c.U) N hMN hNM k)
  refine ⟨U, hUint, hUnoeth, hUover, hUsm, σ, hσdom, hσover, hσbij, cU, e, g,
    fun a => toricChartProduct L a k, hg, hL, hcoh, he, hclos, ?_, ?_⟩
  all_goals
    have : Smooth (U ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
    let x : CodimensionOnePoint U := ⟨e, hcoh⟩
    have hdvr : IsDiscreteValuationRing (U.presheaf.stalk (x : U)) :=
      smoothOverField_codimensionOne_stalk_DVR (K := K) x
  · intro a
    rw [hrel, toricSubst_X]
    exact etaleChartFunctionFieldCoords_monomial_ord cU x he k hnonunit
      (matrixRowExponent (toricChartProduct L) a)
  · have hdet : Matrix.det (Matrix.of fun i j => MvPolynomial.pderiv j
        (toricSubst (K := K) (toricChartProduct L) (MvPolynomial.X i))) =
          MvPolynomial.monomial (jacobianExponent (toricChartProduct L)) 1 := by
      have h := det_toricSubstJacobian (K := K) (toricChartProduct_row_ne_zero L)
        (one_le_toricChartProduct_colSum L)
      rw [det_toricChartProduct, MvPolynomial.C_1, one_mul] at h
      exact h
    rw [chartRelativeJacobianDet_of_polynomial σ c cU (toricSubst (toricChartProduct L)) hrel,
      hdet]
    have h := etaleChartFunctionFieldCoords_monomial_ord cU x he k hnonunit
      (jacobianExponent (toricChartProduct L))
    rw [h]
    have hcol := one_le_toricChartProduct_colSum L k
    simp only [jacobianExponent, Finsupp.coe_equivFunOnFinite_symm]
    rw [Nat.cast_sub hcol, Nat.cast_sum, Nat.cast_one]

end MixedFujita
