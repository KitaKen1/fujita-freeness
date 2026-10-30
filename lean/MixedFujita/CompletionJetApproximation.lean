/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LocalAdicOrder
public import MixedFujita.TaylorFiniteJets
public import MixedFujita.JetHilbertBound
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
Jet approximation through completion coordinates. For a Noetherian local ring S
and a ring isomorphism from its adic completion to power series, every power
series agrees with the coordinate image of an element of S up to any order m.
The kernel of the m-th evaluation is the m-th power times the completion, and
its coordinate image has order at least m. Coefficient boxes of side
(m-1)/n + 1 only see exponents of total degree < m, and every box function is
the box jet of an explicit power series.
-/

@[expose] public section

namespace MixedFujita

section Approximation

variable {S K σ : Type*} [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [Field K]
  [Finite σ]

theorem completionCoordinates_order_ge_of_mem_pow_smul
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal S) S ≃+* MvPowerSeries σ K)
    {m : ℕ} {z : AdicCompletion (IsLocalRing.maximalIdeal S) S}
    (hz : z ∈ (IsLocalRing.maximalIdeal S) ^ m •
      (⊤ : Submodule S (AdicCompletion (IsLocalRing.maximalIdeal S) S))) :
    (m : ℕ∞) ≤ (coordinates z).order := by
  refine Submodule.smul_induction_on hz ?_ ?_
  · intro r hr w _
    rw [Algebra.smul_def, map_mul]
    have hr' : (m : ℕ∞) ≤ (coordinates (algebraMap S _ r)).order := by
      rw [completionCoordinates_order_eq_localAdicOrder coordinates r]
      exact (localAdicOrder_nat_le_iff r m).mpr hr
    calc (m : ℕ∞) ≤ (coordinates (algebraMap S _ r)).order := hr'
      _ ≤ (coordinates (algebraMap S _ r)).order + (coordinates w).order := le_self_add
      _ ≤ _ := MvPowerSeries.le_order_mul
  · intro z₁ z₂ h₁ h₂
    rw [map_add]
    exact (le_min h₁ h₂).trans MvPowerSeries.min_order_le_add

/-- Every power series is approximated to order m by the coordinate image of an actual
element of the Noetherian local ring. -/
theorem completionCoordinates_exists_approx
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal S) S ≃+* MvPowerSeries σ K)
    (P : MvPowerSeries σ K) (m : ℕ) :
    ∃ y : S, (m : ℕ∞) ≤
      (P - coordinates (algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) y)).order := by
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _
    (AdicCompletion.eval (IsLocalRing.maximalIdeal S) S m (coordinates.symm P))
  refine ⟨y, ?_⟩
  have hker : coordinates.symm P -
      algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) y ∈
      (IsLocalRing.maximalIdeal S) ^ m •
      (⊤ : Submodule S (AdicCompletion (IsLocalRing.maximalIdeal S) S)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval
      (IsNoetherian.noetherian (IsLocalRing.maximalIdeal S)), LinearMap.mem_ker,
      map_sub, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      AdicCompletion.eval_of, ← hy]
    exact sub_self _
  have h := completionCoordinates_order_ge_of_mem_pow_smul coordinates hker
  rwa [map_sub, RingEquiv.apply_symm_apply] at h

/-- Membership in the m-th power transfers to order at least m in coordinates. -/
theorem completionCoordinates_order_ge_of_mem_pow
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal S) S ≃+* MvPowerSeries σ K)
    {m : ℕ} {r : S} (hr : r ∈ IsLocalRing.maximalIdeal S ^ m) :
    (m : ℕ∞) ≤ (coordinates (algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) r)).order := by
  rw [completionCoordinates_order_eq_localAdicOrder coordinates r]
  exact (localAdicOrder_nat_le_iff r m).mpr hr

end Approximation

section Boxes

variable {K : Type*} [Field K]

/-- A box jet of side (m-1)/n + 1 vanishes on power series of order at least m. -/
theorem powerSeriesBoxJet_eq_zero_of_le_order (n m : ℕ) (hm : 1 ≤ m)
    (φ : MvPowerSeries (Fin n) K) (h : (m : ℕ∞) ≤ φ.order) :
    powerSeriesBoxJet n ((m - 1) / n) φ = 0 := by
  funext a
  change MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm (fun i => (a i).val)) φ = 0
  apply MvPowerSeries.coeff_of_lt_order
  have hdeg := boxSide_degree_lt n m hm (Finsupp.equivFunOnFinite.symm (fun i => (a i).val))
    (fun i => Nat.lt_succ_iff.mp (a i).isLt)
  calc ((Finsupp.equivFunOnFinite.symm (fun i => (a i).val)).degree : ℕ∞) < m := by
        exact_mod_cast hdeg
    _ ≤ φ.order := h

/-- Two power series agreeing to order m have the same box jet of side (m-1)/n + 1. -/
theorem powerSeriesBoxJet_eq_of_le_order_sub (n m : ℕ) (hm : 1 ≤ m)
    (φ ψ : MvPowerSeries (Fin n) K) (h : (m : ℕ∞) ≤ (φ - ψ).order) :
    powerSeriesBoxJet n ((m - 1) / n) φ = powerSeriesBoxJet n ((m - 1) / n) ψ := by
  have h0 := powerSeriesBoxJet_eq_zero_of_le_order n m hm (φ - ψ) h
  rw [map_sub] at h0
  exact sub_eq_zero.mp h0

/-- The power series whose box coefficients are a given box function. -/
noncomputable def powerSeriesOfBox (n d : ℕ) (v : (Fin n → Fin (d + 1)) → K) :
    MvPowerSeries (Fin n) K :=
  fun β => if h : ∀ i, β i ≤ d then v (fun i => ⟨β i, Nat.lt_succ_of_le (h i)⟩) else 0

theorem powerSeriesBoxJet_ofBox (n d : ℕ) (v : (Fin n → Fin (d + 1)) → K) :
    powerSeriesBoxJet n d (powerSeriesOfBox n d v) = v := by
  funext a
  change MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm (fun i => (a i).val))
    (powerSeriesOfBox n d v) = v a
  rw [MvPowerSeries.coeff_apply]
  have hle : ∀ i, (Finsupp.equivFunOnFinite.symm (fun i => (a i).val)) i ≤ d :=
    fun i => Nat.lt_succ_iff.mp (a i).isLt
  simp only [powerSeriesOfBox, hle, implies_true, dite_true]
  congr 1

end Boxes

end MixedFujita
