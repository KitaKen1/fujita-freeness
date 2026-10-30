/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PointBlowupDifferentialDeterminant
public import MixedFujita.EtaleChartPolynomialMaps

/-! The point-blow-up equations in actual étale scheme charts determine the
actual relative canonical Cartier divisor. Its local equation is y_k^(n-1),
so at a codimension-one DVR point where y_k vanishes the coefficient is n-1
and its log discrepancy is n. Differential bases are constructed from étaleness,
not supplied as additional hypotheses. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem pointBlowup_etaleRelativeJacobian_det {K R S : Type*} [Field K] [CommRing R]
    [Algebra K R] [CommRing S] [Algebra K S] {n : ℕ}
    (β : R →ₐ[K] S) (x : MvPolynomial (Fin n) K →ₐ[K] R)
    (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale) (k : Fin n)
    (hcoord : ∀ i, β (x (MvPolynomial.X i)) =
      if i = k then y (MvPolynomial.X k) else y (MvPolynomial.X i) * y (MvPolynomial.X k)) :
    (etaleRelativeJacobian β x y hy).det = y (MvPolynomial.X k) ^ (n - 1) := by
  rw [etaleRelativeJacobian_det]
  exact pointBlowup_kaehler_determinant (fun i => y (MvPolynomial.X i))
    (fun i => β (x (MvPolynomial.X i))) k hcoord (etaleCoordinateBasis y hy)
    (etaleCoordinateBasis_apply y hy)

universe u
variable {K : Type u} [Field K] {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
  [X.Over (Spec (.of K))] [T.Over (Spec (.of K))] {n : ℕ}
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (.of K))]
attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

theorem pointBlowup_chartRelativeJacobianDet (t : T)
    (c : EtaleChart K X n) (hc : ρ t ∈ c.U) (c' : EtaleChart K T n) (hc' : t ∈ c'.U)
    (k : Fin n)
    (hcoord : ∀ i, schemeStalkMapAlgHom (K := K) ρ t
      (etaleChartStalkCoords c (ρ t) hc (MvPolynomial.X i)) =
        if i = k then etaleChartStalkCoords c' t hc' (MvPolynomial.X k)
        else etaleChartStalkCoords c' t hc' (MvPolynomial.X i) *
          etaleChartStalkCoords c' t hc' (MvPolynomial.X k)) :
    chartRelativeJacobianDet ρ c c' =
      (etaleChartFunctionFieldCoords c' (MvPolynomial.X k)) ^ (n - 1) := by
  rw [chartRelativeJacobianDet_eq_stalk ρ t c hc c' hc',
    pointBlowup_etaleRelativeJacobian_det _ _ _ _ k hcoord, map_pow]
  apply congrArg (fun a : T.functionField => a ^ (n - 1))
  exact AlgHom.congr_fun (etaleChart_stalkFunctionField_comp_stalkCoords c' t hc') _

theorem pointBlowup_relativeCanonical_isLocalEquationAt
    (c₀ : EtaleChart K X n) (hX : iSup (fun c : EtaleChart K X n => c.U) = ⊤)
    (c'₀ : EtaleChart K T n) (hT : iSup (fun c : EtaleChart K T n => c.U) = ⊤)
    (hR : IsUnit (chartRelativeJacobianDet ρ c₀ c'₀)) (t : T)
    (c : EtaleChart K X n) (hc : ρ t ∈ c.U) (c' : EtaleChart K T n) (hc' : t ∈ c'.U)
    (k : Fin n)
    (hcoord : ∀ i, schemeStalkMapAlgHom (K := K) ρ t
      (etaleChartStalkCoords c (ρ t) hc (MvPolynomial.X i)) =
        if i = k then etaleChartStalkCoords c' t hc' (MvPolynomial.X k)
        else etaleChartStalkCoords c' t hc' (MvPolynomial.X i) *
          etaleChartStalkCoords c' t hc' (MvPolynomial.X k)) :
    (relativeCanonicalDivisor n ρ c₀ hX c'₀ hT hR).IsLocalEquationAt t
      ((etaleChartCoordinateRationalUnit c' k) ^ (n - 1)) := by
  have h := relativeCanonicalDivisor_isLocalEquationAt ρ c₀ hX c'₀ hT hR t c hc c' hc'
  convert h using 1
  apply Units.ext
  rw [IsUnit.unit_spec, Units.val_pow_eq_pow_val]
  exact (pointBlowup_chartRelativeJacobianDet ρ t c hc c' hc' k hcoord).symm

variable [IsLocallyNoetherian T] [LocallyOfFiniteType (T ↘ Spec (.of K))]

theorem pointBlowup_relativeCanonical_coefficient
    (c₀ : EtaleChart K X n) (hX : iSup (fun c : EtaleChart K X n => c.U) = ⊤)
    (c'₀ : EtaleChart K T n) (hT : iSup (fun c : EtaleChart K T n => c.U) = ⊤)
    (hR : IsUnit (chartRelativeJacobianDet ρ c₀ c'₀)) (t : CodimensionOnePoint T)
    [IsDiscreteValuationRing (T.presheaf.stalk (t : T))]
    (c : EtaleChart K X n) (hc : ρ (t : T) ∈ c.U)
    (c' : EtaleChart K T n) (hc' : (t : T) ∈ c'.U) (k : Fin n)
    (hk : ¬ IsUnit (T.presheaf.germ c'.U (t : T) hc' (c'.coords (MvPolynomial.X k))))
    (hcoord : ∀ i, schemeStalkMapAlgHom (K := K) ρ (t : T)
      (etaleChartStalkCoords c (ρ (t : T)) hc (MvPolynomial.X i)) =
        if i = k then etaleChartStalkCoords c' (t : T) hc' (MvPolynomial.X k)
        else etaleChartStalkCoords c' (t : T) hc' (MvPolynomial.X i) *
          etaleChartStalkCoords c' (t : T) hc' (MvPolynomial.X k)) :
    cartierCoefficient (relativeCanonicalDivisor n ρ c₀ hX c'₀ hT hR) (t : T) = (n : ℤ) - 1 := by
  rw [cartierCoefficient_eq_ord (pointBlowup_relativeCanonical_isLocalEquationAt ρ
    c₀ hX c'₀ hT hR (t : T) c hc c' hc' k hcoord), Units.val_pow_eq_pow_val]
  have h := etaleChart_coordinate_prod_pow_ord c' t hc' k hk (Pi.single k (n - 1))
  have hn : 0 < n := by have := k.isLt; omega
  simpa [etaleChartFunctionFieldCoords_X, Pi.single_apply, Nat.cast_sub (by omega : 1 ≤ n)] using h

theorem pointBlowup_relativeCanonical_logDiscrepancy
    (c₀ : EtaleChart K X n) (hX : iSup (fun c : EtaleChart K X n => c.U) = ⊤)
    (c'₀ : EtaleChart K T n) (hT : iSup (fun c : EtaleChart K T n => c.U) = ⊤)
    (hR : IsUnit (chartRelativeJacobianDet ρ c₀ c'₀)) (t : CodimensionOnePoint T)
    [IsDiscreteValuationRing (T.presheaf.stalk (t : T))]
    (c : EtaleChart K X n) (hc : ρ (t : T) ∈ c.U)
    (c' : EtaleChart K T n) (hc' : (t : T) ∈ c'.U) (k : Fin n)
    (hk : ¬ IsUnit (T.presheaf.germ c'.U (t : T) hc' (c'.coords (MvPolynomial.X k))))
    (hcoord : ∀ i, schemeStalkMapAlgHom (K := K) ρ (t : T)
      (etaleChartStalkCoords c (ρ (t : T)) hc (MvPolynomial.X i)) =
        if i = k then etaleChartStalkCoords c' (t : T) hc' (MvPolynomial.X k)
        else etaleChartStalkCoords c' (t : T) hc' (MvPolynomial.X i) *
          etaleChartStalkCoords c' (t : T) hc' (MvPolynomial.X k)) :
    1 + cartierCoefficient (relativeCanonicalDivisor n ρ c₀ hX c'₀ hT hR) (t : T) = (n : ℤ) := by
  rw [pointBlowup_relativeCanonical_coefficient ρ c₀ hX c'₀ hT hR t c hc c' hc' k hk hcoord]
  ring

end MixedFujita
