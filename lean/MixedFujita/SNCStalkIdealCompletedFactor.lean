/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCCompletedDivisorOrders
public import Hironaka.Scheme.IdealSheaf.StalkIdeal

/-! Apply SNC completion factorization to a generator of the actual
effective Cartier stalk ideal. The generator need not be supplied with
a rational local equation: equality of principal ideals constructs the
unit relating it to a regular local equation. -/

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

theorem snc_effective_stalkIdeal_taylor_unit_product
    (D : CartierDivisor X) (hD : D.IsEffective) (c : EtaleChart K X n) {r : ℕ}
    (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (σ : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σ)
    (hsupport : ∀ t : CodimensionOnePoint X, (t : X) ∉ Set.range ξ → cartierCoefficient D (t : X) = 0)
    (x : X) (hx : x ∈ c.U) (a : X.presheaf.stalk x)
    (ha : (effectiveCartierIdealSheaf D hD).stalkIdeal x = Ideal.span {a})
    (T : X.presheaf.stalk x →ₐ[K] MvPowerSeries (Fin n) K)
    (hT : ∀ j, T (etaleChartStalkCoords c x hx (MvPolynomial.X j)) = MvPowerSeries.X j) :
    ∃ u : (MvPowerSeries (Fin n) K)ˣ, T a = (u : MvPowerSeries (Fin n) K) *
      ∏ i, ((σ i).elim 1 MvPowerSeries.X) ^ (cartierCoefficient D (ξ i)).toNat := by
  obtain ⟨U, hxU, hne, b, hb, hEq⟩ := exists_affineOpen_regularEquation_of_isEffective D hD x
  let v := X.presheaf.germ U.1 x hxU b
  have hspan : Ideal.span {v} = Ideal.span {a} := by
    have h := (effectiveCartierIdealSheaf D hD).stalkIdeal_eq_map_germ U hxU
    rw [effectiveCartierIdealSheaf_ideal_eq_span D hD U b hb hEq,
      Ideal.map_span, Set.image_singleton] at h
    exact h.symm.trans ha
  obtain ⟨w, hw⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  obtain ⟨u, hu⟩ := snc_effective_localEquation_taylor_unit_product D hD c ξ hinj hξ σ hc
    hsupport x hx (regularEquationRationalUnit X U.1 b hb)
      (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hEq hxU) v
        (by rw [regularEquationRationalUnit_val]; exact X.algebraMap_germ_eq_germToFunctionField hxU b)
      T hT
  refine ⟨u * Units.map T.toMonoidHom w, ?_⟩
  rw [← hw, map_mul, hu, Units.val_mul]
  change (_ * _) * T (w : X.presheaf.stalk x) =
    (_ * T (w : X.presheaf.stalk x)) * _
  ring

theorem snc_effective_stalkIdeal_completed_normal_power_factor
    (D : CartierDivisor X) (hD : D.IsEffective) (c : EtaleChart K X n) {r : ℕ}
    (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (σ : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σ)
    (hsupport : ∀ t : CodimensionOnePoint X, (t : X) ∉ Set.range ξ → cartierCoefficient D (t : X) = 0)
    (x : X) (hx : x ∈ c.U) (a : X.presheaf.stalk x)
    (ha : (effectiveCartierIdealSheaf D hD).stalkIdeal x = Ideal.span {a})
    (T : X.presheaf.stalk x →ₐ[K] MvPowerSeries (Fin n) K)
    (hT : ∀ j, T (etaleChartStalkCoords c x hx (MvPolynomial.X j)) = MvPowerSeries.X j)
    (e : Fin r) (k : Fin n) (he : σ e = some k) :
    ∃ v : MvPowerSeries (Fin n) K,
      T a = MvPowerSeries.X k ^ (cartierCoefficient D (ξ e)).toNat * v ∧
      powerSeriesDivisorRestriction k v ≠ 0 ∧
      ∀ (t : Fin r) (l : Fin n) (hlk : l ≠ k), σ t = some l →
        (powerSeriesDivisorRestriction k v).weightedOrder
          (Pi.single (⟨l, hlk⟩ : {i : Fin n // i ≠ k}) 1) =
            ((cartierCoefficient D (ξ t)).toNat : ℕ∞) := by
  classical
  obtain ⟨u, hu⟩ := snc_effective_stalkIdeal_taylor_unit_product D hD c ξ hinj hξ σ hc hsupport x hx a ha T hT
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

theorem snc_effective_stalkIdeal_completed_normal_factor
    (D : CartierDivisor X) (hD : D.IsEffective) (c : EtaleChart K X n) {r : ℕ}
    (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (σ : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σ)
    (hsupport : ∀ t : CodimensionOnePoint X, (t : X) ∉ Set.range ξ → cartierCoefficient D (t : X) = 0)
    (x : X) (hx : x ∈ c.U) (a : X.presheaf.stalk x)
    (ha : (effectiveCartierIdealSheaf D hD).stalkIdeal x = Ideal.span {a})
    (T : X.presheaf.stalk x →ₐ[K] MvPowerSeries (Fin n) K)
    (hT : ∀ j, T (etaleChartStalkCoords c x hx (MvPolynomial.X j)) = MvPowerSeries.X j)
    (e : Fin r) (k : Fin n) (he : σ e = some k) (hDe : cartierCoefficient D (ξ e) = 1) :
    ∃ v : MvPowerSeries (Fin n) K, T a = MvPowerSeries.X k * v ∧
      powerSeriesDivisorRestriction k v ≠ 0 ∧
      ∀ (t : Fin r) (l : Fin n) (hlk : l ≠ k), σ t = some l →
        (powerSeriesDivisorRestriction k v).weightedOrder
          (Pi.single (⟨l, hlk⟩ : {i : Fin n // i ≠ k}) 1) =
            ((cartierCoefficient D (ξ t)).toNat : ℕ∞) := by
  obtain ⟨v, hv, hrest⟩ := snc_effective_stalkIdeal_completed_normal_power_factor D hD c ξ hinj hξ
    σ hc hsupport x hx a ha T hT e k he
  exact ⟨v, by simpa only [hDe, Int.toNat_one, pow_one] using hv, hrest⟩

end MixedFujita
