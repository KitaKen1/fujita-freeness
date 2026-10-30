/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PointBlowupStalkJacobian
public import MixedFujita.RelativeCanonicalEffectivity
public import MixedFujita.SNCCompletedQuotientOrders
public import MixedFujita.CenteredPolynomialFormalMap

/-! Compute the intermediate Jacobian restriction on an actual SNC
model directly from K_{T/X} and the pulled point-centre divisor. The
actual stalk chain rule and regularity force nonnegative coefficient
differences. Equality at the marked divisor derives nonvanishing after
restriction, with exact tangent orders. No relative canonical divisor
on the intermediate blow-up is constructed or assumed. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] {n : ℕ} {X Y T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian T]
  [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))] [T.Over (Spec (.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (.of K))]
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower cartierBaseOpenAlgebra

set_option maxHeartbeats 1500000 in
theorem pointBlowup_snc_completed_jacobian_orders
    (π : Y ⟶ X) [π.IsOver (Spec (.of K))]
    (g : T ⟶ Y) [g.IsOver (Spec (.of K))]
    (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (.of K))] (hg : g ≫ π = ρ)
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (c₀ : EtaleChart K X n) (cT₀ : EtaleChart K T n)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (E : CartierDivisor T) (hE : E.IsEffective)
    (hD0 : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (birationalRelativeCanonicalDivisor n ρ hρ c₀ etaleCharts_cover
        cT₀ etaleCharts_cover) (t : T) = 0)
    (hE0 : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ → cartierCoefficient E (t : T) = 0)
    (P : T) (c : EtaleChart K T n) (hPc : P ∈ c.U)
    (σ : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σ)
    (x : X) (hq : π (g P) = x) (cX : EtaleChart K X n) (hxcX : x ∈ cX.U)
    (β : Y.presheaf.stalk (g P) →ₐ[K] T.presheaf.stalk P)
    (hβ : β.toRingHom = (g.stalkMap P).hom)
    (k : Fin n) (τ : MvPolynomial (Fin n) K →ₐ[K] Y.presheaf.stalk (g P))
    (hτ : τ.toRingHom.FormallyEtale)
    (hcoord : ∀ a, stalkMapAtEq π (g P) x hq (etaleChartStalkCoords cX x hxcX a) =
      τ (polynomialPointBlowupMap k a))
    (hEI : (effectiveCartierIdealSheaf E hE).stalkIdeal P = Ideal.span {β (τ (MvPolynomial.X k))})
    (Taylor : T.presheaf.stalk P →ₐ[K] MvPowerSeries (Fin n) K)
    (hTaylor : ∀ j, Taylor (etaleChartStalkCoords c P hPc (MvPolynomial.X j)) = MvPowerSeries.X j)
    (e : Fin r) (he : σ e = some k)
    (hDe : cartierCoefficient (birationalRelativeCanonicalDivisor n ρ hρ c₀ etaleCharts_cover
      cT₀ etaleCharts_cover) (ξ e) = ((n - 1 : ℕ) : ℤ))
    (hEe : cartierCoefficient E (ξ e) = 1) :
    let ψ := centeredPolynomialFormalMap (Taylor.comp (β.comp τ))
    (∀ (t : Fin r) (l : Fin n), σ t = some l →
      ((n - 1 : ℕ) : ℤ) * cartierCoefficient E (ξ t) ≤
        cartierCoefficient (birationalRelativeCanonicalDivisor n ρ hρ c₀ etaleCharts_cover
          cT₀ etaleCharts_cover) (ξ t)) ∧
    powerSeriesDivisorRestriction k (powerSeriesJacobian ψ).det ≠ 0 ∧
      ∀ (t : Fin r) (l : Fin n) (hlk : l ≠ k), σ t = some l →
        (powerSeriesDivisorRestriction k (powerSeriesJacobian ψ).det).weightedOrder
          (Pi.single (⟨l, hlk⟩ : {i : Fin n // i ≠ k}) 1) =
            ((cartierCoefficient (birationalRelativeCanonicalDivisor n ρ hρ c₀ etaleCharts_cover
              cT₀ etaleCharts_cover) (ξ t) - ((n - 1 : ℕ) : ℤ) *
                cartierCoefficient E (ξ t)).toNat : ℕ∞) := by
  classical
  subst ρ
  let y := etaleChartStalkCoords c P hPc
  have hy := etaleChartStalkCoords_formallyEtale c P hPc
  let J := (etaleRelativeJacobian β τ y hy).det
  let F := (etaleRelativeJacobian (schemeStalkMapAlgHom (K := K) (g ≫ π) P)
    (etaleChartStalkCoords cX ((g ≫ π) P) (hq.symm ▸ hxcX)) y hy).det
  let D := birationalRelativeCanonicalDivisor n (g ≫ π) hρ c₀ etaleCharts_cover cT₀ etaleCharts_cover
  have hD : D.IsEffective := birationalRelativeCanonicalDivisor_isEffective (g ≫ π) hρ
    c₀ etaleCharts_cover cT₀ etaleCharts_cover
  let f := (isUnit_chartRelativeJacobianDet_of_bijective (g ≫ π) hρ cX c).unit
  have hf : D.IsLocalEquationAt P f := relativeCanonicalDivisor_isLocalEquationAt (g ≫ π)
    c₀ etaleCharts_cover cT₀ etaleCharts_cover
      (isUnit_chartRelativeJacobianDet_of_bijective (g ≫ π) hρ c₀ cT₀) P cX (hq.symm ▸ hxcX) c hPc
  have hF : algebraMap (T.presheaf.stalk P) T.functionField F = (f : T.functionField) := by
    rw [show (f : T.functionField) = chartRelativeJacobianDet (g ≫ π) cX c from IsUnit.unit_spec _]
    exact (chartRelativeJacobianDet_eq_stalk (g ≫ π) P cX (hq.symm ▸ hxcX) c hPc).symm
  have hchain : F = β (τ (MvPolynomial.X k)) ^ (n - 1) * J :=
    pointBlowup_actual_composite_stalkJacobian π g P β hβ x hq cX hxcX c hPc k τ hτ hcoord
  have hTchain : Taylor F = (Taylor (β (τ (MvPolynomial.X k)))) ^ (n - 1) * Taylor J := by
    rw [hchain, map_mul, map_pow]
  obtain ⟨hcoef, hJ0, hord⟩ := snc_effective_completed_quotient_restriction_orders D E hD hE c ξ hinj hξ
    σ hc hD0 hE0 P hPc f hf F _ hF hEI Taylor hTaylor (n - 1) (Taylor J) hTchain e k he hDe hEe
  dsimp only
  rw [centeredPolynomialFormalMap_jacobian_det β τ y hy Taylor hTaylor]
  exact ⟨hcoef, hJ0, hord⟩

end MixedFujita
