/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SectionBaseStalkMembership
public import MixedFujita.SNCCompletedDivisorOrders

/-! The fixed-part coefficient is bounded by the restriction order of
every strict transform. Membership in the actual fixed-part stalk ideal
gives divisibility; cancellation of the marked normal power suffices.
No exact marked coefficient of each section zero divisor is needed. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPowerSeries
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem powerSeries_weightedOrder_pow_eq_mul {σ K : Type*} [Field K]
    (w : σ → ℕ) (f : MvPowerSeries σ K) (m : ℕ) :
    (f ^ m).weightedOrder w = (m : ℕ∞) * f.weightedOrder w := by
  induction m with
  | zero => simp [weightedOrder_one]
  | succ m hm =>
    rw [pow_succ, weightedOrder_mul, hm, Nat.cast_add, Nat.cast_one, add_mul, one_mul]

universe u
variable {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}}
  [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (.of K))]
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower cartierBaseOpenAlgebra

theorem snc_fixedPart_completed_section_order_bound
    (G : CartierDivisor X) (hG : G.IsEffective) (c : EtaleChart K X n) {r : ℕ}
    (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (σ : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σ)
    (hG0 : ∀ t : CodimensionOnePoint X, (t : X) ∉ Set.range ξ → cartierCoefficient G (t : X) = 0)
    (x : X) (hx : x ∈ c.U) (fG : X.functionFieldˣ) (hfG : G.IsLocalEquationAt x fG)
    (a : X.presheaf.stalk x)
    (ha : algebraMap (X.presheaf.stalk x) X.functionField a = (fG : X.functionField))
    (aSection : X.presheaf.stalk x)
    (hSection : aSection ∈ (effectiveCartierIdealSheaf G hG).stalkIdeal x)
    (Taylor : X.presheaf.stalk x →ₐ[K] MvPowerSeries (Fin n) K)
    (hTaylor : ∀ j, Taylor (etaleChartStalkCoords c x hx (MvPolynomial.X j)) = MvPowerSeries.X j)
    (e : Fin r) (k : Fin n) (he : σ e = some k) (m : ℕ)
    (hGe : cartierCoefficient G (ξ e) = (m : ℤ))
    (v f : MvPowerSeries (Fin n) K)
    (hfactor : Taylor aSection = (MvPowerSeries.X k * v) ^ m * f) :
    ∀ (t : Fin r) (l : Fin n) (hlk : l ≠ k), σ t = some l →
      ((cartierCoefficient G (ξ t)).toNat : ℕ∞) ≤
        (m : ℕ∞) * (powerSeriesDivisorRestriction k v).weightedOrder
          (Pi.single (⟨l, hlk⟩ : {i : Fin n // i ≠ k}) 1) +
        (powerSeriesDivisorRestriction k f).weightedOrder
          (Pi.single (⟨l, hlk⟩ : {i : Fin n // i ≠ k}) 1) := by
  classical
  have hI := effectiveCartier_stalkIdeal_eq_span_of_localEquation G hG x fG hfG a ha
  rw [hI, Ideal.mem_span_singleton] at hSection
  obtain ⟨q, hq⟩ := hSection
  obtain ⟨R, hR, _, hord⟩ := snc_effective_completed_normal_power_factor G hG c ξ hinj hξ σ hc
    hG0 x hx fG hfG a ha Taylor hTaylor e k he
  rw [hGe, Int.toNat_natCast] at hR
  have hX : (MvPowerSeries.X k : MvPowerSeries (Fin n) K) ≠ 0 := by
    intro hz
    have hc := congrArg (coeff (Finsupp.single k 1)) hz
    simpa using hc
  have hcancel : R * Taylor q = v ^ m * f := by
    apply mul_left_cancel₀ (pow_ne_zero m hX)
    calc
      MvPowerSeries.X k ^ m * (R * Taylor q) = Taylor aSection := by rw [hq, map_mul, hR]; ring
      _ = (MvPowerSeries.X k * v) ^ m * f := hfactor
      _ = MvPowerSeries.X k ^ m * (v ^ m * f) := by rw [mul_pow]; ring
  intro t l hlk ht
  let w : {i : Fin n // i ≠ k} → ℕ := Pi.single (⟨l, hlk⟩ : {i : Fin n // i ≠ k}) 1
  calc
    _ = (powerSeriesDivisorRestriction k R).weightedOrder w := (hord t l hlk ht).symm
    _ ≤ (powerSeriesDivisorRestriction k R).weightedOrder w +
        (powerSeriesDivisorRestriction k (Taylor q)).weightedOrder w := le_add_right le_rfl
    _ = (powerSeriesDivisorRestriction k (R * Taylor q)).weightedOrder w := by
      rw [map_mul, weightedOrder_mul]
    _ = (powerSeriesDivisorRestriction k (v ^ m * f)).weightedOrder w := by rw [hcancel]
    _ = _ := by rw [map_mul, map_pow, weightedOrder_mul, powerSeries_weightedOrder_pow_eq_mul]

end MixedFujita
