/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PowerSeriesAdicOrder
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Data.Fintype.BigOperators

/-!
A uniform finite order bound on a linear Taylor map gives an injective
finite coefficient map, hence finite dimensionality. Retain the coefficient
box 0 <= alpha_i <= d: every monomial of total degree <= d lies in it.
The resulting bound is (d+1)^n. No finite-dimensionality assumption is used.
-/

@[expose] public section

namespace MixedFujita

variable {K : Type*} [Field K]

noncomputable def powerSeriesBoxJet (n d : ℕ) :
    MvPowerSeries (Fin n) K →ₗ[K] ((Fin n → Fin (d + 1)) → K) :=
  LinearMap.pi fun a => MvPowerSeries.coeff
    (Finsupp.equivFunOnFinite.symm (fun i => (a i).val))

theorem powerSeriesBoxJet_zero_implies_order_ge (n d : ℕ)
    (φ : MvPowerSeries (Fin n) K) (h : powerSeriesBoxJet n d φ = 0) :
    (d + 1 : ℕ) ≤ φ.order := by
  apply MvPowerSeries.nat_le_order
  intro p hp
  let a : Fin n → Fin (d + 1) := fun i => ⟨p i, (Finsupp.le_degree i p).trans_lt hp⟩
  have he : Finsupp.equivFunOnFinite.symm (fun i => (a i).val) = p := by
    ext i
    rfl
  have hh := congrFun h a
  change MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm (fun i => (a i).val)) φ = 0 at hh
  rwa [he] at hh

theorem powerSeriesBoxJet_ne_zero_of_order_le (n d : ℕ)
    (φ : MvPowerSeries (Fin n) K) (h : φ.order ≤ d) : powerSeriesBoxJet n d φ ≠ 0 := by
  intro hz
  have H := (powerSeriesBoxJet_zero_implies_order_ge n d φ hz).trans h
  exact Nat.not_succ_le_self d (ENat.natCast_le_natCast.mp H)

variable {V : Type*} [AddCommGroup V] [Module K V] (n d : ℕ)
  (F : V →ₗ[K] MvPowerSeries (Fin n) K)
  (h : ∀ v, v ≠ 0 → (F v).order ≤ d)

include n d F h

theorem linearTaylorBoxJet_injective : Function.Injective ((powerSeriesBoxJet n d).comp F) := by
  intro u v huv
  apply sub_eq_zero.mp
  by_contra hw
  apply powerSeriesBoxJet_ne_zero_of_order_le n d (F (u - v)) (h (u - v) hw)
  change powerSeriesBoxJet n d (F u) = powerSeriesBoxJet n d (F v) at huv
  rw [map_sub, map_sub, huv, sub_self]

theorem finiteDimensional_of_linearTaylor_order_bound : FiniteDimensional K V :=
  FiniteDimensional.of_injective ((powerSeriesBoxJet n d).comp F)
    (linearTaylorBoxJet_injective n d F h)

theorem finrank_le_box_of_linearTaylor_order_bound : Module.finrank K V ≤ (d + 1) ^ n := by
  have H := LinearMap.finrank_le_finrank_of_injective
    (linearTaylorBoxJet_injective n d F h)
  simpa only [Module.finrank_pi, Fintype.card_fun, Fintype.card_fin] using H

end MixedFujita
