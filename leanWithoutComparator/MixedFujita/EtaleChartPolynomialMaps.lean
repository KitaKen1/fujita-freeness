/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCBoundaryLocalProduct
public import MixedFujita.RelativeCanonicalDivisor
public import MixedFujita.ToricSubstitutionBirational

/-!
Morphisms given by polynomials in étale coordinates, and the orders of the coordinates at a prime
divisor (step 12, section 6.1 of the manuscript). The coordinate derivations of étale coordinates
restrict to the partial derivatives on polynomials in the coordinates, so if a map sends the
coordinates x_i of the target to polynomials φ(x_i) in the coordinates of the source, its relative
Jacobian is the image of the Jacobian of φ; this holds for the chart Jacobian of a dominant
morphism of integral schemes. At a point whose local ring is a discrete valuation ring at most one
coordinate of an étale chart vanishes: a vanishing coordinate x_a is a uniformizer, and x_b = t x_a
would give 1 = ∂_b x_b = x_a ∂_b t. Hence at a codimension-one point where the k-th coordinate
vanishes the coordinates have orders δ_lk, and a monomial in the coordinates has order its k-th
exponent.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section Algebra

variable {K R S : Type*} [Field K] [CommRing R] [Algebra K R] [CommRing S] [Algebra K S] {n : ℕ}

/-- Coordinate derivations restrict to the partial derivatives on polynomials in the
coordinates. -/
theorem etaleCoordinateDerivation_polynomial (y : MvPolynomial (Fin n) K →ₐ[K] S)
    (hy : y.toRingHom.FormallyEtale) (j : Fin n) (p : MvPolynomial (Fin n) K) :
    etaleCoordinateDerivation y hy j (y p) = y (MvPolynomial.pderiv j p) := by
  let _ : Algebra (MvPolynomial (Fin n) K) S := y.toRingHom.toAlgebra
  have : IsScalarTower K (MvPolynomial (Fin n) K) S :=
    IsScalarTower.of_algebraMap_eq fun c => (y.commutes c).symm
  let d₁ : Derivation K (MvPolynomial (Fin n) K) S :=
    (etaleCoordinateDerivation y hy j).compAlgebraMap (MvPolynomial (Fin n) K)
  let d₂ : Derivation K (MvPolynomial (Fin n) K) S :=
    (Algebra.linearMap (MvPolynomial (Fin n) K) S).compDer (MvPolynomial.pderiv j)
  have h : d₁ = d₂ := MvPolynomial.derivation_ext fun i => by
    change etaleCoordinateDerivation y hy j (y (MvPolynomial.X i)) =
      y (MvPolynomial.pderiv j (MvPolynomial.X i))
    rw [etaleCoordinateDerivation_coordinate, MvPolynomial.pderiv_X, Pi.single_apply]
    by_cases hij : i = j
    · rw [ite_eq_left hij, ite_eq_left hij, map_one]
    · rw [ite_eq_right hij, ite_eq_right hij, map_zero]
  exact congr($h p)

/-- The relative Jacobian determinant of a map given by polynomials in the coordinates is the
image of the Jacobian determinant of the polynomials. -/
theorem etaleRelativeJacobian_det_of_polynomial (ψ : R →ₐ[K] S)
    (x : MvPolynomial (Fin n) K →ₐ[K] R) (y : MvPolynomial (Fin n) K →ₐ[K] S)
    (hy : y.toRingHom.FormallyEtale) (φ : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K)
    (hφ : ∀ p, ψ (x p) = y (φ p)) :
    (etaleRelativeJacobian ψ x y hy).det =
      y (Matrix.det (Matrix.of fun i j => MvPolynomial.pderiv j (φ (MvPolynomial.X i)))) := by
  have h : etaleRelativeJacobian ψ x y hy = (y : MvPolynomial (Fin n) K →+* S).mapMatrix
      (Matrix.of fun i j => MvPolynomial.pderiv j (φ (MvPolynomial.X i))) := by
    refine Matrix.ext fun i j => ?_
    change etaleCoordinateDerivation y hy j (ψ (x (MvPolynomial.X i))) =
      y (MvPolynomial.pderiv j (φ (MvPolynomial.X i)))
    rw [hφ, etaleCoordinateDerivation_polynomial]
  rw [h]
  exact (RingHom.map_det (y : MvPolynomial (Fin n) K →+* S) _).symm

end Algebra

section Scheme

universe u

variable {K : Type u} [Field K] {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))] {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- The chart Jacobian of a dominant morphism which is given by polynomials in the chart
coordinates is the image of the Jacobian determinant of the polynomials. -/
theorem chartRelativeJacobianDet_of_polynomial (ρ : T ⟶ X) [IsDominant ρ]
    [ρ.IsOver (Spec (CommRingCat.of K))] (c : EtaleChart K X n) (c' : EtaleChart K T n)
    (φ : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K)
    (hφ : ∀ p, dominantFunctionFieldAlgHom (K := K) ρ (etaleChartFunctionFieldCoords c p) =
      etaleChartFunctionFieldCoords c' (φ p)) :
    chartRelativeJacobianDet ρ c c' = etaleChartFunctionFieldCoords c'
      (Matrix.det (Matrix.of fun i j => MvPolynomial.pderiv j (φ (MvPolynomial.X i)))) :=
  etaleRelativeJacobian_det_of_polynomial _ _ _ _ φ hφ

omit [IsIntegral T] [T.Over (Spec (CommRingCat.of K))] in
/-- The coordinate of a chart in the function field is the rational unit of the coordinate. -/
theorem etaleChartFunctionFieldCoords_X (c : EtaleChart K X n) (l : Fin n) :
    etaleChartFunctionFieldCoords c (MvPolynomial.X l) =
      (etaleChartCoordinateRationalUnit c l : X.functionField) :=
  rfl

variable [IsLocallyNoetherian X] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]

omit [IsIntegral T] [T.Over (Spec (CommRingCat.of K))] [IsLocallyNoetherian X] in
/-- At a point whose local ring is a discrete valuation ring at most one coordinate of an étale
chart vanishes. -/
theorem etaleChart_coordinate_germ_isUnit_of_ne (c : EtaleChart K X n) (x : X) (hx : x ∈ c.U)
    [IsDiscreteValuationRing (X.presheaf.stalk x)] {a b : Fin n} (hab : a ≠ b)
    (ha : ¬ IsUnit (X.presheaf.germ c.U x hx (c.coords (MvPolynomial.X a)))) :
    IsUnit (X.presheaf.germ c.U x hx (c.coords (MvPolynomial.X b))) := by
  by_contra hb
  have hga : X.presheaf.germ c.U x hx (c.coords (MvPolynomial.X a)) ≠ 0 := fun h =>
    etaleChart_coordinate_ne_zero c a
      (germ_injective_of_isIntegral X x hx (h.trans (map_zero _).symm))
  have hirr := dvr_irreducible_of_radical_span _ hga ha
    (etaleChart_coordinate_germ_span_isRadical c a x hx)
  have hmem : X.presheaf.germ c.U x hx (c.coords (MvPolynomial.X b)) ∈
      Ideal.span ({(X.presheaf.germ c.U x hx (c.coords (MvPolynomial.X a)))} :
        Set (X.presheaf.stalk x)) := by
    rw [← hirr.maximalIdeal_eq]
    exact (IsLocalRing.mem_maximalIdeal _).mpr hb
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hmem
  have h1 := etaleCoordinateDerivation_coordinate (etaleChartStalkCoords c x hx)
    (etaleChartStalkCoords_formallyEtale c x hx) b b
  have h0 := etaleCoordinateDerivation_coordinate (etaleChartStalkCoords c x hx)
    (etaleChartStalkCoords_formallyEtale c x hx) a b
  rw [ite_eq_left rfl] at h1
  rw [ite_eq_right hab] at h0
  change etaleCoordinateDerivation (etaleChartStalkCoords c x hx)
    (etaleChartStalkCoords_formallyEtale c x hx) b
      (X.presheaf.germ c.U x hx (c.coords (MvPolynomial.X b))) = 1 at h1
  change etaleCoordinateDerivation (etaleChartStalkCoords c x hx)
    (etaleChartStalkCoords_formallyEtale c x hx) b
      (X.presheaf.germ c.U x hx (c.coords (MvPolynomial.X a))) = 0 at h0
  rw [← ht, Derivation.leibniz, h0, smul_zero, zero_add, smul_eq_mul] at h1
  exact ha (IsUnit.of_mul_eq_one _ h1)

omit [IsIntegral T] [T.Over (Spec (CommRingCat.of K))] in
/-- At a codimension-one point whose local ring is a discrete valuation ring and where the k-th
coordinate vanishes, the coordinates have orders δ_lk. -/
theorem etaleChart_coordinate_ord_of_not_isUnit (c : EtaleChart K X n)
    (x : CodimensionOnePoint X) (hx : (x : X) ∈ c.U)
    [IsDiscreteValuationRing (X.presheaf.stalk (x : X))] (k : Fin n)
    (hk : ¬ IsUnit (X.presheaf.germ c.U (x : X) hx (c.coords (MvPolynomial.X k)))) (l : Fin n) :
    X.ord (etaleChartCoordinateRationalUnit c l : X.functionField) (x : X) =
      if l = k then 1 else 0 := by
  by_cases hlk : l = k
  · subst hlk
    rw [ite_eq_left rfl]
    exact etaleChart_coordinate_ord_one c l x hx hk
  · rw [ite_eq_right hlk]
    have hu := etaleChart_coordinate_germ_isUnit_of_ne c (x : X) hx (Ne.symm hlk) hk
    have h := scheme_ord_stalk_unit (x : X) hu.unit
    simpa only [IsUnit.unit_spec, X.algebraMap_germ_eq_germToFunctionField hx,
      etaleChartCoordinateRationalUnit, regularEquationRationalUnit_val] using h

omit [IsIntegral T] [T.Over (Spec (CommRingCat.of K))] in
/-- At such a point a monomial in the coordinates has order its k-th exponent. -/
theorem etaleChart_coordinate_prod_pow_ord (c : EtaleChart K X n)
    (x : CodimensionOnePoint X) (hx : (x : X) ∈ c.U)
    [IsDiscreteValuationRing (X.presheaf.stalk (x : X))] (k : Fin n)
    (hk : ¬ IsUnit (X.presheaf.germ c.U (x : X) hx (c.coords (MvPolynomial.X k))))
    (m : Fin n → ℕ) :
    X.ord (∏ l, etaleChartFunctionFieldCoords c (MvPolynomial.X l) ^ m l) (x : X) = m k := by
  have h := scheme_ord_prod_zpow (fun l => etaleChartCoordinateRationalUnit c l)
    (fun l => (m l : ℤ)) x
  have hval : ((∏ l, etaleChartCoordinateRationalUnit c l ^ (m l : ℤ) : X.functionFieldˣ) :
      X.functionField) = ∏ l, etaleChartFunctionFieldCoords c (MvPolynomial.X l) ^ m l := by
    rw [Units.coe_prod]
    exact Finset.prod_congr rfl fun l _ => by
      rw [zpow_natCast, Units.val_pow_eq_pow_val, etaleChartFunctionFieldCoords_X]
  rw [← hval, h, Finset.sum_congr rfl fun l _ => by
    rw [etaleChart_coordinate_ord_of_not_isUnit c x hx k hk l]]
  simp

omit [IsIntegral T] [T.Over (Spec (CommRingCat.of K))] in
/-- At such a point the image of a monomial in the coordinates has order its k-th exponent. -/
theorem etaleChartFunctionFieldCoords_monomial_ord (c : EtaleChart K X n)
    (x : CodimensionOnePoint X) (hx : (x : X) ∈ c.U)
    [IsDiscreteValuationRing (X.presheaf.stalk (x : X))] (k : Fin n)
    (hk : ¬ IsUnit (X.presheaf.germ c.U (x : X) hx (c.coords (MvPolynomial.X k))))
    (e : Fin n →₀ ℕ) :
    X.ord (etaleChartFunctionFieldCoords c (MvPolynomial.monomial e 1)) (x : X) = e k := by
  rw [ringHom_monomial_one]
  exact etaleChart_coordinate_prod_pow_ord c x hx k hk e

end Scheme

end MixedFujita
