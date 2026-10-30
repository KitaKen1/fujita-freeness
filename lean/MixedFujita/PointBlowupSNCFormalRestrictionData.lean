/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PointBlowupSNCFormalMap
public import MixedFujita.PointBlowupSNCJacobianOrders

/-! Construct the same actual aligned formal map, normal factor and
supplied leading-form restrictions together with a nonzero restricted
Jacobian and exact tangent orders from the actual relative-canonical
and point-centre coefficients. The remaining fixed-part comparison is
separate; no Jacobian nonvanishing or order is supplied as an input. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] {n : ℕ}
  {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
  [IsLocallyNoetherian X] [IsLocallyNoetherian T]
  [X.Over (Spec (.of K))] [T.Over (Spec (.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (.of K))]
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra

set_option maxHeartbeats 1800000 in
theorem exists_pointBlowup_snc_formal_map_with_jacobian_orders
    (hn : topologicalKrullDim X = n) (x : X) (hx : IsClosed ({x} : Set X))
    (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (.of K))]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (c₀ : EtaleChart K X n) (cT₀ : EtaleChart K T n)
    (g : T ⟶ (pointClosureIdeal x).blowUp) (hg : g ≫ (pointClosureIdeal x).blowUpπ = ρ)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (e : Fin r) (hρe : ρ (ξ e) = x)
    (E : CartierDivisor T) (hE : E.IsEffective)
    (hEI : effectiveCartierIdealSheaf E hE = (pointClosureIdeal x).comap ρ)
    (hE0 : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ → cartierCoefficient E (t : T) = 0)
    (hEe : cartierCoefficient E (ξ e) = 1)
    (hD0 : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (birationalRelativeCanonicalDivisor n ρ hρ c₀ etaleCharts_cover
        cT₀ etaleCharts_cover) (t : T) = 0)
    (hDe : cartierCoefficient (birationalRelativeCanonicalDivisor n ρ hρ c₀ etaleCharts_cover
      cT₀ etaleCharts_cover) (ξ e) = (n : ℤ) - 1)
    (P : T) (hP : IsClosed ({P} : Set T)) (heP : P ∈ closure ({ξ e} : Set T))
    (sourceCompletion : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K) :
    let : (pointClosureIdeal x).blowUp.Over (Spec (.of K)) :=
      ⟨(pointClosureIdeal x).blowUpπ ≫ (X ↘ Spec (.of K))⟩
    ∃ (cX : EtaleChart K X n) (hxcX : x ∈ cX.U) (k : Fin n)
      (τ : MvPolynomial (Fin n) K →ₐ[K] (pointClosureIdeal x).blowUp.presheaf.stalk (g P))
      (β : (pointClosureIdeal x).blowUp.presheaf.stalk (g P) →ₐ[K] T.presheaf.stalk P)
      (c : EtaleChart K T n) (σ : Fin r → Option (Fin n)) (hPc : P ∈ c.U)
      (completion : AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk P))
        (T.presheaf.stalk P) ≃ₐ[K] MvPowerSeries (Fin n) K),
      let Taylor := stalkTaylorExpansion P completion
      let ψ := centeredPolynomialFormalMap (Taylor.comp (β.comp τ))
      τ.toRingHom.FormallyEtale ∧ β.toRingHom = (g.stalkMap P).hom ∧
      ((pointClosureIdeal x).comap (pointClosureIdeal x).blowUpπ).stalkIdeal (g P) =
        Ideal.span {τ (MvPolynomial.X k)} ∧
      (∀ (hq : (pointClosureIdeal x).blowUpπ (g P) = x) (a : MvPolynomial (Fin n) K),
        stalkMapAtEq (pointClosureIdeal x).blowUpπ (g P) x hq
          (etaleChartStalkCoords cX x hxcX a) = τ (polynomialPointBlowupMap k a)) ∧
      IsSNCChart c ξ σ ∧ σ e = some k ∧
      (∀ i, P ∈ closure ({ξ i} : Set T) ↔ ∃ j, σ i = some j) ∧
      (∀ j, Taylor (etaleChartStalkCoords c P hPc (MvPolynomial.X j)) = MvPowerSeries.X j) ∧
      (∀ a, (Taylor a).order = localAdicOrder (T.presheaf.stalk P) a) ∧
      (powerSeriesJacobian ψ).det = Taylor
        (etaleRelativeJacobian β τ (etaleChartStalkCoords c P hPc)
          (etaleChartStalkCoords_formallyEtale c P hPc)).det ∧
      (∀ (t : Fin r) (l : Fin n), σ t = some l →
        ((n - 1 : ℕ) : ℤ) * cartierCoefficient E (ξ t) ≤
          cartierCoefficient (birationalRelativeCanonicalDivisor n ρ hρ c₀ etaleCharts_cover
            cT₀ etaleCharts_cover) (ξ t)) ∧
      powerSeriesDivisorRestriction k (powerSeriesJacobian ψ).det ≠ 0 ∧
      (∀ (t : Fin r) (l : Fin n) (hlk : l ≠ k), σ t = some l →
        (powerSeriesDivisorRestriction k (powerSeriesJacobian ψ).det).weightedOrder
          (Pi.single (⟨l, hlk⟩ : {i : Fin n // i ≠ k}) 1) =
            ((cartierCoefficient (birationalRelativeCanonicalDivisor n ρ hρ c₀ etaleCharts_cover
              cT₀ etaleCharts_cover) (ξ t) - ((n - 1 : ℕ) : ℤ) *
                cartierCoefficient E (ξ t)).toNat : ℕ∞)) ∧
      ∃ v : MvPowerSeries (Fin n) K,
        Taylor (β (τ (MvPolynomial.X k))) = MvPowerSeries.X k * v ∧
        ψ (MvPowerSeries.X k) = MvPowerSeries.X k * v ∧
        powerSeriesDivisorRestriction k v ≠ 0 ∧
        (∀ (t : Fin r) (l : Fin n) (hlk : l ≠ k), σ t = some l →
          (powerSeriesDivisorRestriction k v).weightedOrder
            (Pi.single (⟨l, hlk⟩ : {i : Fin n // i ≠ k}) 1) =
              ((cartierCoefficient E (ξ t)).toNat : ℕ∞)) ∧
        ∀ (hq : (pointClosureIdeal x).blowUpπ (g P) = x)
          (D : CartierDivisor X) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
          (s : Γ(D.sheaf, ⊤)) (m : ℕ), (m : ℕ∞) ≤ cartierSectionVanishingOrder D x s →
          ∃ z : (pointClosureIdeal x).blowUp.presheaf.stalk (g P),
            stalkMapAtEq (pointClosureIdeal x).blowUpπ (g P) x hq
                (cartierLocalCoefficient D x f hf s) = τ (MvPolynomial.X k) ^ m * z ∧
            powerSeriesDivisorRestriction k (Taylor (β z)) =
              powerSeriesDivisorMap ψ k
                (chartShiftedForm k (fun i => MvPowerSeries.constantCoeff
                  (Taylor (β (τ (MvPolynomial.X i.val)))))
                    (homogeneousTaylorForm m (cartierTaylorCoordinates D x f hf sourceCompletion s))) := by
  classical
  let I := pointClosureIdeal x
  let π := I.blowUpπ
  let : I.blowUp.Over (Spec (.of K)) := ⟨π ≫ (X ↘ Spec (.of K))⟩
  have : π.IsOver (Spec (.of K)) := ⟨rfl⟩
  have : g.IsOver (Spec (.of K)) := ⟨by
    change g ≫ (π ≫ (X ↘ Spec (.of K))) = T ↘ Spec (.of K)
    rw [← Category.assoc, hg]
    exact HomIsOver.comp_over (f := ρ) (S := Spec (.of K))⟩
  have hq : π (g P) = x := by
    have hm := specializes_iff_mem_closure.mp
      ((specializes_iff_mem_closure.mpr heP).map ρ.continuous)
    rw [hρe, hx.closure_eq] at hm
    change (g ≫ π) P = x
    rw [hg]
    exact hm
  obtain ⟨cX, hxcX, k, τ, β, c, σ, hPc, completion, hτ, hβ, hI, hcoord,
      hc, he, hmem, hTaylor, horder, hJ, v, hv, hψv, hv0, hvord, hsections⟩ :=
    exists_pointBlowup_snc_aligned_formal_map hn x hx ρ g hg ξ hinj hξ hsnc e hρe E hE hEI
      hE0 hEe P hP heP sourceCompletion
  have hIT : (effectiveCartierIdealSheaf E hE).stalkIdeal P = Ideal.span {β (τ (MvPolynomial.X k))} := by
    rw [hEI, ← hg, Scheme.IdealSheafData.comap_comp,
      Scheme.IdealSheafData.stalkIdeal_comap, hI, ← hβ, Ideal.map_span, Set.image_singleton]
    rfl
  have hn1 : 1 ≤ n := by have := k.isLt; omega
  have hDe' : cartierCoefficient (birationalRelativeCanonicalDivisor n ρ hρ c₀ etaleCharts_cover
      cT₀ etaleCharts_cover) (ξ e) = ((n - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub hn1, Nat.cast_one]
    exact hDe
  obtain ⟨hcoef, hJ0, hJord⟩ := pointBlowup_snc_completed_jacobian_orders π g ρ hg hρ c₀ cT₀ ξ hinj hξ
    E hE hD0 hE0 P c hPc σ hc x hq cX hxcX β hβ k τ hτ (hcoord hq) hIT
      (stalkTaylorExpansion P completion) hTaylor e he hDe' hEe
  exact ⟨cX, hxcX, k, τ, β, c, σ, hPc, completion, hτ, hβ, hI, hcoord,
    hc, he, hmem, hTaylor, horder, hJ, hcoef, hJ0, hJord, v, hv, hψv, hv0, hvord, hsections⟩

end MixedFujita
