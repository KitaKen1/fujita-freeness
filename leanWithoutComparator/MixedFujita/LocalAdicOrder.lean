/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PowerSeriesAdicOrder
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.AdicCompletion.Noetherian

/-!
The actual ideal-adic vanishing order is the supremum of the powers
containing an element, with value infinity for zero in a Noetherian local
ring. A local ring's maximal-ideal powers are reflected by its completion.
A given ring-coordinate isomorphism from that completion to finite-variable
power series identifies this intrinsic local order with Taylor order.
The coordinate isomorphism's existence is not asserted.
This is adic vanishing order, not a Hilbert-Samuel multiplicity theorem.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

variable {R : Type*} [CommRing R]

noncomputable def idealAdicOrder (I : Ideal R) (r : R) : ℕ∞ :=
  ⨆ (d : ℕ) (_ : r ∈ I ^ d), (d : ℕ∞)

theorem idealAdicOrder_nat_le_iff (I : Ideal R) (r : R) (d : ℕ) :
    (d : ℕ∞) ≤ idealAdicOrder I r ↔ r ∈ I ^ d := by
  constructor
  · intro h
    by_contra hn
    cases d with
    | zero => exact hn (by simp)
    | succ d =>
      have hb : idealAdicOrder I r ≤ (d : ℕ∞) := by
        apply iSup_le
        intro m
        apply iSup_le
        intro hm
        apply ENat.natCast_le_natCast.mpr
        apply Nat.le_of_lt_succ
        apply lt_of_not_ge
        intro hdm
        exact hn (I.pow_le_pow_right hdm hm)
      exact Nat.not_succ_le_self d (ENat.natCast_le_natCast.mp (h.trans hb))
  · intro hr
    exact le_iSup_of_le d (le_iSup_of_le hr le_rfl)

theorem idealAdicOrder_eq_nat_iff (I : Ideal R) (r : R) (d : ℕ) :
    idealAdicOrder I r = (d : ℕ∞) ↔ r ∈ I ^ d ∧ r ∉ I ^ (d + 1) := by
  constructor
  · intro h
    constructor
    · exact (idealAdicOrder_nat_le_iff I r d).mp (h.symm.le)
    · intro hm
      have := (idealAdicOrder_nat_le_iff I r (d + 1)).mpr hm
      rw [h] at this
      exact Nat.not_succ_le_self d (ENat.natCast_le_natCast.mp this)
  · rintro ⟨hd, hnext⟩
    apply le_antisymm
    · apply ENat.forall_natCast_le_iff_le.mp
      intro m hm
      apply ENat.natCast_le_natCast.mpr
      apply Nat.le_of_lt_succ
      apply lt_of_not_ge
      intro hdm
      exact hnext (I.pow_le_pow_right hdm ((idealAdicOrder_nat_le_iff I r m).mp hm))
    · exact (idealAdicOrder_nat_le_iff I r d).mpr hd

theorem idealAdicOrder_eq_top_iff (I : Ideal R) (r : R) :
    idealAdicOrder I r = ⊤ ↔ ∀ d : ℕ, r ∈ I ^ d := by
  rw [ENat.eq_top_iff_forall_ge]
  exact forall_congr' fun d => idealAdicOrder_nat_le_iff I r d

theorem idealAdicOrder_zero (I : Ideal R) : idealAdicOrder I 0 = ⊤ :=
  (idealAdicOrder_eq_top_iff I 0).mpr fun d => (I ^ d).zero_mem

theorem ideal_mem_unit_mul_iff (I : Ideal R) (v : Rˣ) (r : R) :
    (v : R) * r ∈ I ↔ r ∈ I := by
  constructor
  · intro h
    have hv : ((v⁻¹ : Rˣ) : R) * (v : R) = 1 := Units.inv_mul v
    simpa only [← mul_assoc, hv, one_mul] using I.mul_mem_left ((v⁻¹ : Rˣ) : R) h
  · exact I.mul_mem_left (v : R)

theorem idealAdicOrder_unit_mul (I : Ideal R) (v : Rˣ) (r : R) :
    idealAdicOrder I ((v : R) * r) = idealAdicOrder I r := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro d
  rw [idealAdicOrder_nat_le_iff, idealAdicOrder_nat_le_iff, ideal_mem_unit_mul_iff]

noncomputable def localAdicOrder (R : Type*) [CommRing R] [IsLocalRing R] (r : R) : ℕ∞ :=
  idealAdicOrder (IsLocalRing.maximalIdeal R) r

theorem localAdicOrder_nat_le_iff [IsLocalRing R] (r : R) (d : ℕ) :
    (d : ℕ∞) ≤ localAdicOrder R r ↔ r ∈ IsLocalRing.maximalIdeal R ^ d :=
  idealAdicOrder_nat_le_iff _ r d

theorem localAdicOrder_eq_nat_iff [IsLocalRing R] (r : R) (d : ℕ) :
    localAdicOrder R r = (d : ℕ∞) ↔
      r ∈ IsLocalRing.maximalIdeal R ^ d ∧ r ∉ IsLocalRing.maximalIdeal R ^ (d + 1) :=
  idealAdicOrder_eq_nat_iff _ r d

theorem localAdicOrder_unit_mul [IsLocalRing R] (v : Rˣ) (r : R) :
    localAdicOrder R ((v : R) * r) = localAdicOrder R r :=
  idealAdicOrder_unit_mul _ v r

theorem localAdicOrder_eq_top_iff [IsLocalRing R] [IsNoetherianRing R] (r : R) :
    localAdicOrder R r = ⊤ ↔ r = 0 := by
  constructor
  · intro h
    have hm := (idealAdicOrder_eq_top_iff (IsLocalRing.maximalIdeal R) r).mp h
    apply IsHausdorff.haus (inferInstance : IsHausdorff (IsLocalRing.maximalIdeal R) R) r
    intro d
    apply SModEq.zero.mpr
    simpa only [smul_eq_mul, Ideal.mul_top] using hm d
  · rintro rfl
    exact idealAdicOrder_zero _

theorem completion_algebraMap_mem_maximalIdeal_pow_iff
    [IsLocalRing R] [IsNoetherianRing R] (r : R) (d : ℕ) :
    algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) r ∈
      IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal R) R) ^ d ↔
    r ∈ IsLocalRing.maximalIdeal R ^ d := by
  rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow]
  change algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) r ∈
    (((IsLocalRing.maximalIdeal R) ^ d).map
      (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).restrictScalars R ↔ _
  rw [← Ideal.smul_top_eq_map, AdicCompletion.pow_smul_top_eq_ker_eval
    (IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing, LinearMap.mem_ker]
  change Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ d • ⊤) r = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, smul_eq_mul, Ideal.mul_top]

theorem completionCoordinates_mem_maximalIdeal_pow_iff
    {σ K : Type*} [Finite σ] [Field K] [IsLocalRing R] [IsNoetherianRing R]
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃+* MvPowerSeries σ K)
    (r : R) (d : ℕ) :
    (d : ℕ∞) ≤ (coordinates (algebraMap R
      (AdicCompletion (IsLocalRing.maximalIdeal R) R) r)).order ↔
      r ∈ IsLocalRing.maximalIdeal R ^ d := by
  rw [← powerSeries_mem_maximalIdeal_pow_iff,
    ← IsLocalRing.map_ringEquiv_maximalIdeal coordinates, ← Ideal.map_pow,
    Ideal.apply_mem_of_equiv_iff, completion_algebraMap_mem_maximalIdeal_pow_iff]

theorem completionCoordinates_order_eq_localAdicOrder
    {σ K : Type*} [Finite σ] [Field K] [IsLocalRing R] [IsNoetherianRing R]
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃+* MvPowerSeries σ K)
    (r : R) :
    (coordinates (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) r)).order =
      localAdicOrder R r := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro d
  rw [completionCoordinates_mem_maximalIdeal_pow_iff, localAdicOrder_nat_le_iff]

end MixedFujita
