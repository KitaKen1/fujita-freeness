/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCMonomialQuotientOrders
public import MixedFujita.SNCStalkIdealCompletedFactor

/-! Actual effective SNC divisor coefficients compute the restriction
orders of a regular completed quotient. Equality along the marked
component forces a nonzero restriction; no separate nonvanishing or
intermediate effective divisor is supplied. -/

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
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower cartierBaseOpenAlgebra

theorem snc_effective_completed_quotient_restriction_orders
    (D E : CartierDivisor X) (hD : D.IsEffective) (hE : E.IsEffective)
    (c : EtaleChart K X n) {r : ℕ} (ξ : Fin r → X)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (σ : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σ)
    (hD0 : ∀ t : CodimensionOnePoint X, (t : X) ∉ Set.range ξ → cartierCoefficient D (t : X) = 0)
    (hE0 : ∀ t : CodimensionOnePoint X, (t : X) ∉ Set.range ξ → cartierCoefficient E (t : X) = 0)
    (x : X) (hx : x ∈ c.U) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
    (a b : X.presheaf.stalk x) (ha : algebraMap (X.presheaf.stalk x) X.functionField a = (f : X.functionField))
    (hb : (effectiveCartierIdealSheaf E hE).stalkIdeal x = Ideal.span {b})
    (T : X.presheaf.stalk x →ₐ[K] MvPowerSeries (Fin n) K)
    (hT : ∀ j, T (etaleChartStalkCoords c x hx (MvPolynomial.X j)) = MvPowerSeries.X j)
    (N : ℕ) (J : MvPowerSeries (Fin n) K) (hquot : T a = (T b) ^ N * J)
    (e : Fin r) (k : Fin n) (he : σ e = some k)
    (hDe : cartierCoefficient D (ξ e) = (N : ℤ)) (hEe : cartierCoefficient E (ξ e) = 1) :
    (∀ (t : Fin r) (l : Fin n), σ t = some l →
      (N : ℤ) * cartierCoefficient E (ξ t) ≤ cartierCoefficient D (ξ t)) ∧
    powerSeriesDivisorRestriction k J ≠ 0 ∧
      ∀ (t : Fin r) (l : Fin n) (hlk : l ≠ k), σ t = some l →
        (powerSeriesDivisorRestriction k J).weightedOrder
          (Pi.single (⟨l, hlk⟩ : {i : Fin n // i ≠ k}) 1) =
            ((cartierCoefficient D (ξ t) - (N : ℤ) * cartierCoefficient E (ξ t)).toNat : ℕ∞) := by
  obtain ⟨u, hu⟩ := snc_effective_localEquation_taylor_unit_product D hD c ξ hinj hξ σ hc hD0 x hx f hf a ha T hT
  obtain ⟨v, hv⟩ := snc_effective_stalkIdeal_taylor_unit_product E hE c ξ hinj hξ σ hc hE0 x hx b hb T hT
  rw [hu, hv] at hquot
  have hle (t : Fin r) (l : Fin n) (ht : σ t = some l) :=
    selected_coordinate_regular_quotient_exponent_le u v σ _ _ hc.1 N J hquot t l ht
  have hDn (t : Fin r) : 0 ≤ cartierCoefficient D (ξ t) := cartierCoefficient_nonneg_of_isEffective D hD _
  have hEn (t : Fin r) : 0 ≤ cartierCoefficient E (ξ t) := cartierCoefficient_nonneg_of_isEffective E hE _
  have hleZ (t : Fin r) (l : Fin n) (ht : σ t = some l) :
      (N : ℤ) * cartierCoefficient E (ξ t) ≤ cartierCoefficient D (ξ t) := by
    have hz := Int.ofNat_le.mpr (hle t l ht)
    simpa only [Int.natCast_mul, Int.toNat_of_nonneg (hDn t), Int.toNat_of_nonneg (hEn t)] using hz
  obtain ⟨hJ, hord⟩ := selected_coordinate_regular_quotient_restriction u v σ _ _ hc.1 N J hquot e k he
    (by simp only [hDe, hEe, Int.toNat_natCast, Int.toNat_one, mul_one])
  refine ⟨hleZ, hJ, ?_⟩
  intro t l hlk ht
  rw [hord t l hlk ht, Int.toNat_sub'' (hDn t) (mul_nonneg (Int.natCast_nonneg N) (hEn t)),
    Int.toNat_mul (Int.natCast_nonneg N) (hEn t), Int.toNat_natCast]

end MixedFujita
