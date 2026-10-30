/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.InitialExponents
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Data.Finsupp.MonomialOrder
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
Initial monomials of actual multivariate formal power series, for any
Mathlib monomial order. Finite-dimensional subspaces have exactly as many
possible initial monomials as their dimension. Initial monomials multiply.
The geometric Taylor expansion into this ring is a separate dependency.
-/

@[expose] public section

namespace MixedFujita

open scoped Pointwise

variable {σ K : Type*} [Field K]

noncomputable def monomialCoefficientMap (m : MonomialOrder σ) :
    MvPowerSeries σ K →ₗ[K] (m.syn → K) :=
  LinearMap.pi (fun p => MvPowerSeries.coeff (m.toSyn.symm p))

theorem monomialCoefficientMap_injective (m : MonomialOrder σ) :
    Function.Injective (monomialCoefficientMap m (K := K)) := by
  intro φ ψ h
  apply MvPowerSeries.ext
  intro p
  simpa only [monomialCoefficientMap, LinearMap.pi_apply,
    m.toSyn.symm_apply_apply] using congrFun h (m.toSyn p)

def IsInitialMonomial (m : MonomialOrder σ) (φ : MvPowerSeries σ K) (p : σ →₀ ℕ) : Prop :=
  MvPowerSeries.coeff p φ ≠ 0 ∧
    ∀ q, m.toSyn q < m.toSyn p → MvPowerSeries.coeff q φ = 0

theorem initialMonomial_iff_initialCoefficient (m : MonomialOrder σ)
    (φ : MvPowerSeries σ K) (p : σ →₀ ℕ) :
    IsInitialMonomial m φ p ↔
      IsInitialCoefficient (monomialCoefficientMap m) φ (m.toSyn p) := by
  constructor
  · intro h
    constructor
    · simpa only [monomialCoefficientMap, LinearMap.pi_apply, m.toSyn.symm_apply_apply]
        using h.1
    · intro q hq
      exact h.2 (m.toSyn.symm q) (by simpa only [m.toSyn.apply_symm_apply] using hq)
  · intro h
    constructor
    · simpa only [monomialCoefficientMap, LinearMap.pi_apply, m.toSyn.symm_apply_apply]
        using h.1
    · intro q hq
      simpa only [monomialCoefficientMap, LinearMap.pi_apply, m.toSyn.symm_apply_apply]
        using h.2 (m.toSyn q) hq

theorem exists_initialMonomial (m : MonomialOrder σ) {φ : MvPowerSeries σ K}
    (hφ : φ ≠ 0) : ∃ p, IsInitialMonomial m φ p := by
  have hf : monomialCoefficientMap m φ ≠ 0 := by
    intro h
    apply hφ
    exact monomialCoefficientMap_injective m (h.trans (map_zero _).symm)
  obtain ⟨p, hp⟩ := exists_initialCoefficient (monomialCoefficientMap m (K := K)) (v := φ) hf
  refine ⟨m.toSyn.symm p, ?_⟩
  apply (initialMonomial_iff_initialCoefficient m _ _).mpr
  simpa only [m.toSyn.apply_symm_apply] using hp

theorem initialMonomial_mul_coeff (m : MonomialOrder σ)
    {φ ψ : MvPowerSeries σ K} {p q : σ →₀ ℕ}
    (hp : IsInitialMonomial m φ p) (hq : IsInitialMonomial m ψ q) :
    MvPowerSeries.coeff (p + q) (φ * ψ) =
      MvPowerSeries.coeff p φ * MvPowerSeries.coeff q ψ := by
  classical
  rw [MvPowerSeries.coeff_mul, Finset.sum_eq_single_of_mem (p, q) (by simp)]
  rintro ⟨u, v⟩ huv hne
  have huv' : u + v = p + q := Finset.mem_antidiagonal.mp huv
  rcases lt_trichotomy (m.toSyn u) (m.toSyn p) with hu | hu | hu
  · rw [hp.2 u hu, zero_mul]
  · have hup : u = p := m.toSyn.injective hu
    have hvq : v = q := by rw [hup] at huv'; exact add_left_cancel huv'
    exact False.elim (hne (Prod.ext hup hvq))
  · have hv : m.toSyn v < m.toSyn q := by
      by_contra hv
      have hlt := add_lt_add_of_lt_of_le hu (le_of_not_gt hv)
      have heq := congrArg m.toSyn huv'
      simp only [map_add] at heq
      rw [heq] at hlt
      exact (lt_irrefl _) hlt
    rw [hq.2 v hv, mul_zero]

theorem initialMonomial_mul (m : MonomialOrder σ)
    {φ ψ : MvPowerSeries σ K} {p q : σ →₀ ℕ}
    (hp : IsInitialMonomial m φ p) (hq : IsInitialMonomial m ψ q) :
    IsInitialMonomial m (φ * ψ) (p + q) := by
  classical
  constructor
  · rw [initialMonomial_mul_coeff m hp hq]
    exact mul_ne_zero hp.1 hq.1
  · intro t ht
    rw [MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    rintro ⟨u, v⟩ huv
    have huv' : u + v = t := Finset.mem_antidiagonal.mp huv
    by_cases hu : m.toSyn u < m.toSyn p
    · rw [hp.2 u hu, zero_mul]
    · have hv : m.toSyn v < m.toSyn q := by
        by_contra hv
        have hle := add_le_add (le_of_not_gt hu) (le_of_not_gt hv)
        rw [← map_add, ← map_add, huv'] at hle
        exact not_le_of_gt ht hle
      rw [hq.2 v hv, mul_zero]

noncomputable def subspaceCoefficientMap (m : MonomialOrder σ) (S : Submodule K (MvPowerSeries σ K)) :
    S →ₗ[K] (m.syn → K) := (monomialCoefficientMap m).comp S.subtype

theorem subspaceCoefficientMap_injective (m : MonomialOrder σ)
    (S : Submodule K (MvPowerSeries σ K)) :
    Function.Injective (subspaceCoefficientMap m S) :=
  (monomialCoefficientMap_injective m).comp Subtype.val_injective

noncomputable def initialMonomialFinset (m : MonomialOrder σ)
    (S : Submodule K (MvPowerSeries σ K)) [FiniteDimensional K S] : Finset (σ →₀ ℕ) := by
  classical
  exact (initialIndexSet_finite (subspaceCoefficientMap m S)).toFinset.image m.toSyn.symm

theorem mem_initialMonomialFinset (m : MonomialOrder σ)
    (S : Submodule K (MvPowerSeries σ K)) [FiniteDimensional K S] (p : σ →₀ ℕ) :
    p ∈ initialMonomialFinset m S ↔
      ∃ φ ∈ S, IsInitialMonomial m φ p := by
  classical
  simp only [initialMonomialFinset, Finset.mem_image, Set.Finite.mem_toFinset,
    initialIndexSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨q, ⟨φ, hφ⟩, hq⟩
    have hqp : q = m.toSyn p := by
      have h := congrArg m.toSyn hq
      simpa only [m.toSyn.apply_symm_apply] using h
    subst q
    exact ⟨φ.val, φ.property, (initialMonomial_iff_initialCoefficient m φ.val p).mpr hφ⟩
  · rintro ⟨φ, hφ, hp⟩
    exact ⟨m.toSyn p, ⟨⟨φ, hφ⟩,
      (initialMonomial_iff_initialCoefficient m φ p).mp hp⟩, m.toSyn.symm_apply_apply p⟩

theorem initialMonomialFinset_card (m : MonomialOrder σ)
    (S : Submodule K (MvPowerSeries σ K)) [FiniteDimensional K S] :
    (initialMonomialFinset m S).card = Module.finrank K S := by
  classical
  rw [initialMonomialFinset, Finset.card_image_of_injective _ m.toSyn.symm.injective]
  have h := initialIndexSet_card _ (subspaceCoefficientMap_injective m S)
  rw [Set.ncard_eq_toFinset_card _ (initialIndexSet_finite _)] at h
  exact h

/-- The multiplication law for the *entire* set of possible initial monomials. -/
theorem initialMonomialFinset_add_subset [DecidableEq σ] (m : MonomialOrder σ)
    (S T U : Submodule K (MvPowerSeries σ K))
    [FiniteDimensional K S] [FiniteDimensional K T] [FiniteDimensional K U]
    (hmul : ∀ φ ∈ S, ∀ ψ ∈ T, φ * ψ ∈ U) :
    initialMonomialFinset m S + initialMonomialFinset m T ⊆ initialMonomialFinset m U := by
  intro t ht
  obtain ⟨p, hp, q, hq, rfl⟩ := Finset.mem_add.mp ht
  obtain ⟨φ, hφ, hp⟩ := (mem_initialMonomialFinset m S p).mp hp
  obtain ⟨ψ, hψ, hq⟩ := (mem_initialMonomialFinset m T q).mp hq
  exact (mem_initialMonomialFinset m U _).mpr
    ⟨φ * ψ, hmul φ hφ ψ hψ, initialMonomial_mul m hp hq⟩

end MixedFujita
