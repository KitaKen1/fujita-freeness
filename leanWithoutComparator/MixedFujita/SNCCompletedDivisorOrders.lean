/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCEffectiveStalkProduct
public import MixedFujita.SNCMonomialDivisorOrders
public import MixedFujita.ToricExtractionDomination

/-! Actual SNC coefficients determine finite orders after completion and
restriction to a marked coordinate divisor. Centered charts and their
compatible completions are constructed at closed points. A coefficient
zero along the marked component gives a nonzero restriction and exact
tangent coefficient; coefficient one constructs the normal factor. -/

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

theorem exists_centered_snc_completion_at_closedPoint [IsAlgClosed K]
    {r : ℕ} (ξ : Fin r → X) (hsnc : IsSNCFamily K n ξ)
    (x : X) (hx : IsClosed ({x} : Set X)) :
    ∃ (c : EtaleChart K X n) (σ : Fin r → Option (Fin n)) (hxc : x ∈ c.U),
      IsSNCChart c ξ σ ∧
      (∀ i, x ∈ closure ({ξ i} : Set X) ↔ ∃ j, σ i = some j) ∧
      ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K,
        (∀ j, stalkTaylorExpansion x e (etaleChartStalkCoords c x hxc (MvPolynomial.X j)) =
          MvPowerSeries.X j) ∧
        ∀ a, (stalkTaylorExpansion x e a).order = localAdicOrder (X.presheaf.stalk x) a := by
  let : Smooth (X ↘ Spec (.of K)) := SmoothOfRelativeDimension.smooth n _
  obtain ⟨β⟩ := smoothScheme_closedPoint_has_localEvaluation (K := K) x hx
  obtain ⟨c, σ, hxc, hc, hnu, hsome, hmem⟩ := exists_centered_snc_chart ξ hsnc x β
  obtain ⟨e, he, hord⟩ := etaleChart_exists_taylorCoordinates c x hxc β
  refine ⟨c, σ, hxc, hc, fun i => ⟨hmem i, fun ⟨j, hj⟩ => hsome i j hj⟩, e, ?_, hord⟩
  intro j
  have hj := he j
  rw [etaleChartCenteredStalkCoords_variable] at hj
  have hβ0 : rationalAffineGermPoint x hxc β (c.coords (MvPolynomial.X j)) = 0 := by
    change β (X.presheaf.germ c.U x hxc (c.coords (MvPolynomial.X j))) = 0
    exact not_not.mp ((rationalLocalPoint_isUnit_iff β _).not.mp (hnu j))
  rwa [hβ0, map_zero, sub_zero] at hj

theorem snc_effective_completed_restriction_exact_coefficient
    (D : CartierDivisor X) (hD : D.IsEffective) (c : EtaleChart K X n) {r : ℕ}
    (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (σ : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σ)
    (hsupport : ∀ t : CodimensionOnePoint X, (t : X) ∉ Set.range ξ → cartierCoefficient D (t : X) = 0)
    (x : X) (hx : x ∈ c.U) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
    (a : X.presheaf.stalk x) (ha : algebraMap (X.presheaf.stalk x) X.functionField a = (f : X.functionField))
    (T : X.presheaf.stalk x →ₐ[K] MvPowerSeries (Fin n) K)
    (hT : ∀ j, T (etaleChartStalkCoords c x hx (MvPolynomial.X j)) = MvPowerSeries.X j)
    (e t : Fin r) (k l : Fin n) (hlk : l ≠ k) (he : σ e = some k) (ht : σ t = some l)
    (hDe : cartierCoefficient D (ξ e) = 0) :
    powerSeriesDivisorRestriction k (T a) ≠ 0 ∧
      (powerSeriesDivisorRestriction k (T a)).weightedOrder
        (Pi.single (⟨l, hlk⟩ : {i : Fin n // i ≠ k}) 1) =
          ((cartierCoefficient D (ξ t)).toNat : ℕ∞) := by
  classical
  obtain ⟨u, hu⟩ := snc_effective_localEquation_taylor_unit_product D hD c ξ hinj hξ σ hc hsupport x hx f hf a ha T hT
  have hzero (i : Fin r) (hi : σ i = some k) : (cartierCoefficient D (ξ i)).toNat = 0 := by
    have hie := hc.1 i e k hi he
    rw [hie, hDe]
    rfl
  rw [hu]
  exact ⟨restrict_selected_coordinate_unit_product_ne_zero u σ _ k hzero,
    weightedOrder_restrict_selected_coordinate_single u σ _ hc.1 k l hlk hzero t ht⟩

theorem snc_effective_completed_normal_power_factor
    (D : CartierDivisor X) (hD : D.IsEffective) (c : EtaleChart K X n) {r : ℕ}
    (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (σ : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σ)
    (hsupport : ∀ t : CodimensionOnePoint X, (t : X) ∉ Set.range ξ → cartierCoefficient D (t : X) = 0)
    (x : X) (hx : x ∈ c.U) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
    (a : X.presheaf.stalk x) (ha : algebraMap (X.presheaf.stalk x) X.functionField a = (f : X.functionField))
    (T : X.presheaf.stalk x →ₐ[K] MvPowerSeries (Fin n) K)
    (hT : ∀ j, T (etaleChartStalkCoords c x hx (MvPolynomial.X j)) = MvPowerSeries.X j)
    (e : Fin r) (k : Fin n) (he : σ e = some k) :
    ∃ v : MvPowerSeries (Fin n) K, T a = MvPowerSeries.X k ^ (cartierCoefficient D (ξ e)).toNat * v ∧
      powerSeriesDivisorRestriction k v ≠ 0 ∧
      ∀ (t : Fin r) (l : Fin n) (hlk : l ≠ k), σ t = some l →
        (powerSeriesDivisorRestriction k v).weightedOrder
          (Pi.single (⟨l, hlk⟩ : {i : Fin n // i ≠ k}) 1) =
            ((cartierCoefficient D (ξ t)).toNat : ℕ∞) := by
  classical
  obtain ⟨u, hu⟩ := snc_effective_localEquation_taylor_unit_product D hD c ξ hinj hξ σ hc hsupport x hx f hf a ha T hT
  let m : Fin r → ℕ := fun i => if i = e then 0 else (cartierCoefficient D (ξ i)).toNat
  have hzero (i : Fin r) (hi : σ i = some k) : m i = 0 := by
    have hie := hc.1 i e k hi he
    simp only [m, hie, ite_eq_left rfl]
  refine ⟨(u : MvPowerSeries (Fin n) K) * ∏ i, ((σ i).elim 1 MvPowerSeries.X) ^ m i,
    ?_, restrict_selected_coordinate_unit_product_ne_zero u σ m k hzero, ?_⟩
  · rw [hu]
    exact selected_coordinate_unit_product_remove_normal_power u σ _ e k he
  · intro t l hlk ht
    have hte : t ≠ e := by
      intro h
      rw [h, he] at ht
      exact hlk (Option.some.inj ht).symm
    simpa only [m, ite_eq_right hte] using
      weightedOrder_restrict_selected_coordinate_single u σ m hc.1 k l hlk hzero t ht

theorem snc_effective_completed_normal_factor
    (D : CartierDivisor X) (hD : D.IsEffective) (c : EtaleChart K X n) {r : ℕ}
    (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (σ : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σ)
    (hsupport : ∀ t : CodimensionOnePoint X, (t : X) ∉ Set.range ξ → cartierCoefficient D (t : X) = 0)
    (x : X) (hx : x ∈ c.U) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
    (a : X.presheaf.stalk x) (ha : algebraMap (X.presheaf.stalk x) X.functionField a = (f : X.functionField))
    (T : X.presheaf.stalk x →ₐ[K] MvPowerSeries (Fin n) K)
    (hT : ∀ j, T (etaleChartStalkCoords c x hx (MvPolynomial.X j)) = MvPowerSeries.X j)
    (e : Fin r) (k : Fin n) (he : σ e = some k) (hDe : cartierCoefficient D (ξ e) = 1) :
    ∃ v : MvPowerSeries (Fin n) K, T a = MvPowerSeries.X k * v ∧
      powerSeriesDivisorRestriction k v ≠ 0 ∧
      ∀ (t : Fin r) (l : Fin n) (hlk : l ≠ k), σ t = some l →
        (powerSeriesDivisorRestriction k v).weightedOrder
          (Pi.single (⟨l, hlk⟩ : {i : Fin n // i ≠ k}) 1) =
            ((cartierCoefficient D (ξ t)).toNat : ℕ∞) := by
  classical
  obtain ⟨u, hu⟩ := snc_effective_localEquation_taylor_unit_product D hD c ξ hinj hξ σ hc hsupport x hx f hf a ha T hT
  let m : Fin r → ℕ := fun i => if i = e then 0 else (cartierCoefficient D (ξ i)).toNat
  have hzero (i : Fin r) (hi : σ i = some k) : m i = 0 := by
    have hie := hc.1 i e k hi he
    simp only [m, hie, ite_eq_left rfl]
  refine ⟨(u : MvPowerSeries (Fin n) K) * ∏ i, ((σ i).elim 1 MvPowerSeries.X) ^ m i,
    ?_, restrict_selected_coordinate_unit_product_ne_zero u σ m k hzero, ?_⟩
  · rw [hu]
    exact selected_coordinate_unit_product_remove_normal u σ _ e k he (by rw [hDe]; rfl)
  · intro t l hlk ht
    have hte : t ≠ e := by
      intro h
      rw [h, he] at ht
      exact hlk (Option.some.inj ht).symm
    simpa only [m, ite_eq_right hte] using
      weightedOrder_restrict_selected_coordinate_single u σ m hc.1 k l hlk hzero t ht

end MixedFujita
