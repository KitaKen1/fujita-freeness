/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.EtaleDVRCoordinateOrder

/-! The actual relative canonical coefficient can be computed using formally
étale stalk coordinates. A change to any scheme chart contributes a unit,
so these coordinates need not be spread to a new global affine chart. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

theorem coheight_eq_one_of_stalk_DVR {T : Scheme.{u}} (t : T)
    [IsDomain (T.presheaf.stalk t)] [IsDiscreteValuationRing (T.presheaf.stalk t)] :
    Order.coheight t = 1 := by
  have h := IsDiscreteValuationRing.ringKrullDim_eq_one (T.presheaf.stalk t)
  rw [ringKrullDim_stalk_eq_coheight] at h
  exact_mod_cast h

variable {K : Type u} [Field K] {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
  [X.Over (Spec (.of K))] [T.Over (Spec (.of K))] {n : ℕ}
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (.of K))]
attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

variable [IsLocallyNoetherian T]

theorem pointBlowup_stalk_relativeCanonical_coefficient
    (c₀ : EtaleChart K X n) (hX : iSup (fun c : EtaleChart K X n => c.U) = ⊤)
    (c'₀ : EtaleChart K T n) (hT : iSup (fun c : EtaleChart K T n => c.U) = ⊤)
    (hR : IsUnit (chartRelativeJacobianDet ρ c₀ c'₀)) (t : CodimensionOnePoint T)
    [IsDiscreteValuationRing (T.presheaf.stalk (t : T))]
    (c : EtaleChart K X n) (hc : ρ (t : T) ∈ c.U)
    (τ : MvPolynomial (Fin n) K →ₐ[K] T.presheaf.stalk (t : T))
    (hτ : τ.toRingHom.FormallyEtale) (k : Fin n) (hk : ¬ IsUnit (τ (MvPolynomial.X k)))
    (hcoord : ∀ i, schemeStalkMapAlgHom (K := K) ρ (t : T)
      (etaleChartStalkCoords c (ρ (t : T)) hc (MvPolynomial.X i)) =
        if i = k then τ (MvPolynomial.X k) else τ (MvPolynomial.X i) * τ (MvPolynomial.X k)) :
    cartierCoefficient (relativeCanonicalDivisor n ρ c₀ hX c'₀ hT hR) (t : T) = (n : ℤ) - 1 := by
  obtain ⟨c', hc'⟩ := Opens.mem_iSup.mp (hT.symm ▸ Opens.mem_top (t : T))
  let d := (etaleRelativeJacobian (schemeStalkMapAlgHom (K := K) ρ (t : T))
    (etaleChartStalkCoords c (ρ (t : T)) hc) (etaleChartStalkCoords c' (t : T) hc')
    (etaleChartStalkCoords_formallyEtale c' (t : T) hc')).det
  have hd : d ≠ 0 := by
    intro hd
    have hu := (isUnit_chartRelativeJacobianDet ρ c₀ c'₀ hR c c').ne_zero
    rw [chartRelativeJacobianDet_eq_stalk ρ (t : T) c hc c' hc'] at hu
    exact hu (by change stalkFunctionFieldAlgHom (K := K) (t : T) d = 0; rw [hd, map_zero])
  have ho : localAdicOrder (T.presheaf.stalk (t : T)) d = (n - 1 : ℕ) :=
    pointBlowup_etaleDVR_jacobian_order _ _ τ _ hτ _ k hk hcoord
  rw [cartierCoefficient_eq_ord (relativeCanonicalDivisor_isLocalEquationAt ρ
    c₀ hX c'₀ hT hR (t : T) c hc c' hc'), IsUnit.unit_spec,
    chartRelativeJacobianDet_eq_stalk ρ (t : T) c hc c' hc']
  change T.ord (algebraMap (T.presheaf.stalk (t : T)) T.functionField d) (t : T) = (n : ℤ) - 1
  have hn : 1 ≤ n := by have := k.isLt; omega
  simpa only [Nat.cast_sub hn, Nat.cast_one] using
    scheme_ord_regular_eq_localAdicOrder_nat t d hd (n - 1) ho

theorem pointBlowup_stalk_relativeCanonical_logDiscrepancy
    (c₀ : EtaleChart K X n) (hX : iSup (fun c : EtaleChart K X n => c.U) = ⊤)
    (c'₀ : EtaleChart K T n) (hT : iSup (fun c : EtaleChart K T n => c.U) = ⊤)
    (hR : IsUnit (chartRelativeJacobianDet ρ c₀ c'₀)) (t : CodimensionOnePoint T)
    [IsDiscreteValuationRing (T.presheaf.stalk (t : T))]
    (c : EtaleChart K X n) (hc : ρ (t : T) ∈ c.U)
    (τ : MvPolynomial (Fin n) K →ₐ[K] T.presheaf.stalk (t : T))
    (hτ : τ.toRingHom.FormallyEtale) (k : Fin n) (hk : ¬ IsUnit (τ (MvPolynomial.X k)))
    (hcoord : ∀ i, schemeStalkMapAlgHom (K := K) ρ (t : T)
      (etaleChartStalkCoords c (ρ (t : T)) hc (MvPolynomial.X i)) =
        if i = k then τ (MvPolynomial.X k) else τ (MvPolynomial.X i) * τ (MvPolynomial.X k)) :
    1 + cartierCoefficient (relativeCanonicalDivisor n ρ c₀ hX c'₀ hT hR) (t : T) = (n : ℤ) := by
  rw [pointBlowup_stalk_relativeCanonical_coefficient ρ c₀ hX c'₀ hT hR t c hc τ hτ k hk hcoord]
  ring

end MixedFujita
