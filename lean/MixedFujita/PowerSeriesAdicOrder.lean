/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.HomogeneousTaylor
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
Identify actual powers of the variable ideal of finite-variable power
series with their order filtration, by the actual polynomial-completion
isomorphism. Over a field this ideal is the actual maximal ideal.
Consequently every ring isomorphism between these power-series rings
preserves order; no continuity or coordinate-filtration condition is an
extra hypothesis. This does not construct smooth local coordinates.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

variable {σ R : Type*} [Finite σ] [CommRing R]

noncomputable def powerSeriesVariableIdeal (σ R : Type*) [CommRing R] :
    Ideal (MvPowerSeries σ R) := Ideal.span (Set.range MvPowerSeries.X)

theorem powerSeriesCompletion_variableIdeal_map :
    (powerSeriesVariableIdeal σ R).map
      (MvPowerSeries.toAdicCompletionAlgEquiv σ R).toRingEquiv =
    (MvPolynomial.idealOfVars σ R).map
      (algebraMap (MvPolynomial σ R)
        (AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R))) := by
  simp_rw [powerSeriesVariableIdeal, MvPolynomial.idealOfVars, Ideal.map_span, ← Set.range_comp]
  congr 2
  ext i
  simp [AdicCompletion.algebraMap_apply, ← MvPolynomial.coe_X,
    MvPowerSeries.toAdicCompletion_coe]

omit [Finite σ] in
theorem powerSeries_nat_le_order_iff (φ : MvPowerSeries σ R) (d : ℕ) :
    (d : ℕ∞) ≤ φ.order ↔ ∀ p : σ →₀ ℕ, p.degree < d → MvPowerSeries.coeff p φ = 0 := by
  constructor
  · intro h p hp
    exact MvPowerSeries.coeff_of_lt_order ((ENat.natCast_lt_natCast.mpr hp).trans_le h)
  · exact MvPowerSeries.nat_le_order

theorem powerSeriesCompletion_eval_eq_zero_iff (φ : MvPowerSeries σ R) (d : ℕ) :
    AdicCompletion.eval (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R) d
      (MvPowerSeries.toAdicCompletionAlgEquiv σ R φ) = 0 ↔ (d : ℕ∞) ≤ φ.order := by
  change Ideal.Quotient.mk (MvPolynomial.idealOfVars σ R ^ d • ⊤)
    (MvPowerSeries.truncTotal d φ) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, smul_eq_mul, Ideal.mul_top,
    MvPolynomial.mem_pow_idealOfVars_iff', powerSeries_nat_le_order_iff]
  exact forall_congr' fun p => forall_congr' fun hp => by
    rw [MvPowerSeries.coeff_truncTotal φ hp]

theorem powerSeries_mem_variableIdeal_pow_iff (φ : MvPowerSeries σ R) (d : ℕ) :
    φ ∈ powerSeriesVariableIdeal σ R ^ d ↔ (d : ℕ∞) ≤ φ.order := by
  rw [← Ideal.apply_mem_of_equiv_iff
    (f := (MvPowerSeries.toAdicCompletionAlgEquiv σ R).toRingEquiv),
    Ideal.map_pow, powerSeriesCompletion_variableIdeal_map, ← Ideal.map_pow]
  change MvPowerSeries.toAdicCompletionAlgEquiv σ R φ ∈
    (((MvPolynomial.idealOfVars σ R) ^ d).map (algebraMap (MvPolynomial σ R)
      (AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R)))).restrictScalars
        (MvPolynomial σ R) ↔ _
  rw [← Ideal.smul_top_eq_map, AdicCompletion.pow_smul_top_eq_ker_eval
    (MvPolynomial.idealOfVars_fg σ R), LinearMap.mem_ker]
  exact powerSeriesCompletion_eval_eq_zero_iff φ d

theorem powerSeriesVariableIdeal_eq_ker_constantCoeff :
    powerSeriesVariableIdeal σ R = RingHom.ker (MvPowerSeries.constantCoeff (σ := σ) (R := R)) := by
  ext φ
  rw [← pow_one (powerSeriesVariableIdeal σ R), powerSeries_mem_variableIdeal_pow_iff]
  simpa only [Nat.cast_one, RingHom.mem_ker] using
    (MvPowerSeries.one_le_order_iff_constCoeff_eq_zero (f := φ))

theorem powerSeries_maximalIdeal_eq_variableIdeal {K : Type*} [Field K] :
    IsLocalRing.maximalIdeal (MvPowerSeries σ K) = powerSeriesVariableIdeal σ K := by
  rw [powerSeriesVariableIdeal_eq_ker_constantCoeff]
  symm
  exact IsLocalRing.ker_eq_maximalIdeal (MvPowerSeries.constantCoeff (σ := σ) (R := K))
    (fun k => ⟨MvPowerSeries.C k, by simp⟩)

theorem powerSeries_mem_maximalIdeal_pow_iff {K : Type*} [Field K]
    (φ : MvPowerSeries σ K) (d : ℕ) :
    φ ∈ IsLocalRing.maximalIdeal (MvPowerSeries σ K) ^ d ↔ (d : ℕ∞) ≤ φ.order := by
  rw [powerSeries_maximalIdeal_eq_variableIdeal, powerSeries_mem_variableIdeal_pow_iff]

theorem powerSeries_order_ringEquiv {τ K L : Type*} [Finite τ] [Field K] [Field L]
    (e : MvPowerSeries σ K ≃+* MvPowerSeries τ L) (φ : MvPowerSeries σ K) :
    (e φ).order = φ.order := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro d
  rw [← powerSeries_mem_maximalIdeal_pow_iff, ← powerSeries_mem_maximalIdeal_pow_iff,
    ← IsLocalRing.map_ringEquiv_maximalIdeal e, ← Ideal.map_pow,
    Ideal.apply_mem_of_equiv_iff]

end MixedFujita
