/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCBoundaryLocalProduct
public import MixedFujita.EtaleChartPolynomialMaps
public import MixedFujita.SmoothStalkNormality
public import MixedFujita.LogPairDenominatorScaling

/-! Effective Cartier coefficients on an actual smooth SNC chart give
an actual stalk-unit times a product of coordinate germs with natural
exponents. The same factorization transports to any compatible Taylor
map, with a constructed power-series unit. Neither local factorization
nor its unit is supplied as an input. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}}
  [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (.of K))]
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra

set_option maxHeartbeats 900000 in
theorem snc_effective_localEquation_stalk_unit_product
    (D : CartierDivisor X) (hD : D.IsEffective) (c : EtaleChart K X n) {r : ℕ}
    (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (σ : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σ)
    (hsupport : ∀ t : CodimensionOnePoint X, (t : X) ∉ Set.range ξ → cartierCoefficient D (t : X) = 0)
    (x : X) (hx : x ∈ c.U) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
    (a : X.presheaf.stalk x) (ha : algebraMap (X.presheaf.stalk x) X.functionField a = (f : X.functionField)) :
    ∃ u : (X.presheaf.stalk x)ˣ, a = (u : X.presheaf.stalk x) *
      ∏ i, ((σ i).elim 1 fun j => etaleChartStalkCoords c x hx (MvPolynomial.X j)) ^
        (cartierCoefficient D (ξ i)).toNat := by
  classical
  let : Smooth (X ↘ Spec (.of K)) := SmoothOfRelativeDimension.smooth n _
  have : ∀ t : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (t : X)) :=
    fun t => smoothOverField_codimensionOne_stalk_DVR (K := K) t
  have hnorm : ∀ z : X, IsIntegrallyClosed (X.presheaf.stalk z) :=
    fun z => smooth_stalk_isIntegrallyClosed (K := K) z
  obtain ⟨f', hf', v, hv⟩ :=
    normal_isSNCChart_boundary_local_product hnorm D c ξ hinj hξ σ hc hsupport x hx
  obtain ⟨u', hu'⟩ := hf.exists_unit_mul_eq hf'
  have hm (i : Fin r) : ((cartierCoefficient D (ξ i)).toNat : ℤ) = cartierCoefficient D (ξ i) :=
    Int.toNat_of_nonneg (cartierCoefficient_nonneg_of_isEffective D hD (ξ i))
  let P : X.presheaf.stalk x := ∏ i,
    ((σ i).elim 1 fun j => etaleChartStalkCoords c x hx (MvPolynomial.X j)) ^
      (cartierCoefficient D (ξ i)).toNat
  have hprod : ((∏ i, sncChartComponentEquation c σ i ^ cartierCoefficient D (ξ i) :
      X.functionFieldˣ) : X.functionField) = algebraMap (X.presheaf.stalk x) X.functionField P := by
    dsimp only [P]
    rw [Units.coe_prod, map_prod]
    apply Finset.prod_congr rfl
    intro i hi
    rw [← hm i, zpow_natCast, Units.val_pow_eq_pow_val, map_pow]
    congr 1
    cases hσ : σ i with
    | none => simp [sncChartComponentEquation, hσ]
    | some j =>
      simp only [sncChartComponentEquation, hσ, Option.elim_some]
      exact (X.algebraMap_germ_eq_germToFunctionField hx _).symm
  refine ⟨u' * v, ?_⟩
  apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  rw [ha, ← hu', hv, hprod]
  simp only [Units.val_mul, map_mul, mul_assoc]
  rfl

theorem snc_effective_localEquation_taylor_unit_product
    (D : CartierDivisor X) (hD : D.IsEffective) (c : EtaleChart K X n) {r : ℕ}
    (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (σ : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σ)
    (hsupport : ∀ t : CodimensionOnePoint X, (t : X) ∉ Set.range ξ → cartierCoefficient D (t : X) = 0)
    (x : X) (hx : x ∈ c.U) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
    (a : X.presheaf.stalk x) (ha : algebraMap (X.presheaf.stalk x) X.functionField a = (f : X.functionField))
    (T : X.presheaf.stalk x →ₐ[K] MvPowerSeries (Fin n) K)
    (hT : ∀ j, T (etaleChartStalkCoords c x hx (MvPolynomial.X j)) = MvPowerSeries.X j) :
    ∃ u : (MvPowerSeries (Fin n) K)ˣ, T a = (u : MvPowerSeries (Fin n) K) *
      ∏ i, ((σ i).elim 1 MvPowerSeries.X) ^ (cartierCoefficient D (ξ i)).toNat := by
  obtain ⟨u, hu⟩ := snc_effective_localEquation_stalk_unit_product D hD c ξ hinj hξ σ hc hsupport x hx f hf a ha
  refine ⟨Units.map T.toMonoidHom u, ?_⟩
  rw [hu, map_mul, map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [map_pow]
  congr 1
  cases hσ : σ i with
  | none => simp [hσ]
  | some j => simpa only [hσ, Option.elim_some] using hT j

end MixedFujita
