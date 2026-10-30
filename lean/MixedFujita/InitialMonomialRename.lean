/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PowerSeriesExponents
public import Mathlib.RingTheory.MvPowerSeries.Rename

/-!
Initial exponents under a renaming of the variables (used to split the Taylor variables at a
general closed point of the centre into normal and tangent variables, section 5.2 of the
manuscript).

Let e be a bijection from the variables σ to the variables τ. A monomial order on σ gives a
monomial order on τ; the coefficients, the initial monomials and the sets of initial exponents of
finite-dimensional spaces of power series correspond under the renaming of the variables along e,
and sums over the initial exponents are transported.
-/

@[expose] public section

namespace MixedFujita

variable {σ τ K : Type*} [Field K]

/-- The monomial order on the variables τ given by a monomial order on σ and a bijection. -/
noncomputable def monomialOrderMapEquiv (m : MonomialOrder σ) (e : σ ≃ τ) : MonomialOrder τ where
  syn := m.syn
  toSyn := (Finsupp.domCongr e.symm).trans m.toSyn
  toSyn_monotone := by
    intro a b hab
    refine m.toSyn_monotone fun i => ?_
    change Finsupp.equivMapDomain e.symm a i ≤ Finsupp.equivMapDomain e.symm b i
    rw [Finsupp.equivMapDomain_apply, Finsupp.equivMapDomain_apply]
    exact hab _

theorem equivMapDomain_symm_equivMapDomain (e : σ ≃ τ) (a : σ →₀ ℕ) :
    Finsupp.equivMapDomain e.symm (Finsupp.equivMapDomain e a) = a := by
  rw [← Finsupp.equivMapDomain_trans, Equiv.self_trans_symm, Finsupp.equivMapDomain_refl]

theorem equivMapDomain_equivMapDomain_symm (e : σ ≃ τ) (a : τ →₀ ℕ) :
    Finsupp.equivMapDomain e (Finsupp.equivMapDomain e.symm a) = a := by
  rw [← Finsupp.equivMapDomain_trans, Equiv.symm_trans_self, Finsupp.equivMapDomain_refl]

/-- The transported order compares the transported exponents as the original order compares the
exponents. -/
theorem monomialOrderMapEquiv_lt_iff (m : MonomialOrder σ) (e : σ ≃ τ) (a b : σ →₀ ℕ) :
    (monomialOrderMapEquiv m e).toSyn (Finsupp.equivMapDomain e a) <
        (monomialOrderMapEquiv m e).toSyn (Finsupp.equivMapDomain e b) ↔
      m.toSyn a < m.toSyn b := by
  change m.toSyn (Finsupp.equivMapDomain e.symm (Finsupp.equivMapDomain e a)) <
    m.toSyn (Finsupp.equivMapDomain e.symm (Finsupp.equivMapDomain e b)) ↔ _
  rw [equivMapDomain_symm_equivMapDomain, equivMapDomain_symm_equivMapDomain]

/-- The coefficients of a renamed power series. -/
theorem coeff_equivMapDomain_renameEquiv (e : σ ≃ τ) (φ : MvPowerSeries σ K) (p : σ →₀ ℕ) :
    MvPowerSeries.coeff (Finsupp.equivMapDomain e p) (MvPowerSeries.renameEquiv K e φ) =
      MvPowerSeries.coeff p φ := by
  have h := MvPowerSeries.coeff_embDomain_rename e.toEmbedding φ p
  rw [Finsupp.embDomain_eq_mapDomain] at h
  rw [Finsupp.equivMapDomain_eq_mapDomain]
  exact h

/-- Initial monomials correspond under the renaming of the variables. -/
theorem isInitialMonomial_renameEquiv_iff (m : MonomialOrder σ) (e : σ ≃ τ)
    (φ : MvPowerSeries σ K) (p : σ →₀ ℕ) :
    IsInitialMonomial (monomialOrderMapEquiv m e) (MvPowerSeries.renameEquiv K e φ)
        (Finsupp.equivMapDomain e p) ↔ IsInitialMonomial m φ p := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by rwa [coeff_equivMapDomain_renameEquiv] at h1, fun q hq => ?_⟩
    have h3 := h2 (Finsupp.equivMapDomain e q) ((monomialOrderMapEquiv_lt_iff m e q p).mpr hq)
    rwa [coeff_equivMapDomain_renameEquiv] at h3
  · rintro ⟨h1, h2⟩
    refine ⟨by rwa [coeff_equivMapDomain_renameEquiv], fun q' hq' => ?_⟩
    rw [← equivMapDomain_equivMapDomain_symm e q'] at hq' ⊢
    rw [coeff_equivMapDomain_renameEquiv]
    exact h2 _ ((monomialOrderMapEquiv_lt_iff m e _ p).mp hq')

/-- The initial exponents of a renamed space are the transported initial exponents. -/
theorem mem_initialMonomialFinset_map_renameEquiv (m : MonomialOrder σ) (e : σ ≃ τ)
    (S : Submodule K (MvPowerSeries σ K)) [FiniteDimensional K S] (p : σ →₀ ℕ) :
    Finsupp.equivMapDomain e p ∈ initialMonomialFinset (monomialOrderMapEquiv m e)
        (S.map (MvPowerSeries.renameEquiv K e).toLinearMap) ↔
      p ∈ initialMonomialFinset m S := by
  rw [mem_initialMonomialFinset, mem_initialMonomialFinset]
  constructor
  · rintro ⟨ψ, hψ, hinit⟩
    obtain ⟨φ, hφ, rfl⟩ := Submodule.mem_map.mp hψ
    exact ⟨φ, hφ, (isInitialMonomial_renameEquiv_iff m e φ p).mp hinit⟩
  · rintro ⟨φ, hφ, hinit⟩
    exact ⟨_, Submodule.mem_map_of_mem hφ, (isInitialMonomial_renameEquiv_iff m e φ p).mpr hinit⟩

/-- Sums over the initial exponents of a renamed space. -/
theorem sum_initialMonomialFinset_map_renameEquiv (m : MonomialOrder σ) (e : σ ≃ τ)
    (S : Submodule K (MvPowerSeries σ K)) [FiniteDimensional K S] {M : Type*} [AddCommMonoid M]
    (g : (τ →₀ ℕ) → M) :
    ∑ q ∈ initialMonomialFinset (monomialOrderMapEquiv m e)
        (S.map (MvPowerSeries.renameEquiv K e).toLinearMap), g q =
      ∑ p ∈ initialMonomialFinset m S, g (Finsupp.equivMapDomain e p) := by
  refine Finset.sum_nbij' (Finsupp.equivMapDomain e.symm) (Finsupp.equivMapDomain e)
    (fun q hq => ?_) (fun p hp => (mem_initialMonomialFinset_map_renameEquiv m e S p).mpr hp)
    (fun q _ => equivMapDomain_equivMapDomain_symm e q)
    (fun p _ => equivMapDomain_symm_equivMapDomain e p)
    (fun q _ => by rw [equivMapDomain_equivMapDomain_symm])
  rw [← equivMapDomain_equivMapDomain_symm e q] at hq
  exact (mem_initialMonomialFinset_map_renameEquiv m e S _).mp hq

end MixedFujita
