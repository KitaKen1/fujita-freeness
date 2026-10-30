/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.WellFounded

/-!
Initial coefficients in an arbitrary well-ordered coefficient system.
The cardinality proof uses independence and a separating coefficient map;
it does not require a formalized Gaussian elimination algorithm.
-/

@[expose] public section

namespace MixedFujita

variable {K V α : Type*} [Field K] [AddCommGroup V] [Module K V]
  [LinearOrder α]

def IsInitialCoefficient (f : V →ₗ[K] (α → K)) (v : V) (p : α) : Prop :=
  f v p ≠ 0 ∧ ∀ q < p, f v q = 0

def initialIndexSet (f : V →ₗ[K] (α → K)) : Set α :=
  {p | ∃ v, IsInitialCoefficient f v p}

theorem exists_initialCoefficient [WellFoundedLT α]
    (f : V →ₗ[K] (α → K)) {v : V} (hv : f v ≠ 0) :
    ∃ p, IsInitialCoefficient f v p := by
  let S := Function.support (f v)
  have hS : S.Nonempty := Function.support_nonempty_iff.mpr hv
  let p := wellFounded_lt.min S hS
  refine ⟨p, wellFounded_lt.min_mem S hS, ?_⟩
  intro q hqp
  by_contra hq
  exact wellFounded_lt.not_lt_min S hq hqp

/-- Supplying the least active index is enough to verify the leading term
of any finite linear combination. -/
theorem initial_min_coefficient_sum {ι : Type*}
    (f : V →ₗ[K] (α → K)) (v : ι → V) (p : ι → α)
    (hp : Function.Injective p) (hinit : ∀ i, IsInitialCoefficient f (v i) (p i))
    (s : Finset ι) (g : ι → K) (j : ι) (hj : j ∈ s)
    (hmin : ∀ k ∈ s, g k ≠ 0 → p j ≤ p k) :
    f (∑ k ∈ s, g k • v k) (p j) = g j * f (v j) (p j) := by
  classical
  have hother : ∀ k ∈ s, k ≠ j → g k * f (v k) (p j) = 0 := by
    intro k hk hkj
    by_cases hgk : g k = 0
    · simp [hgk]
    · have hlt : p j < p k := lt_of_le_of_ne
        (hmin k hk hgk)
        (fun heq => hkj (hp heq.symm))
      rw [(hinit k).2 (p j) hlt, mul_zero]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_eq_single_of_mem j hj hother

theorem sum_has_initialCoefficient {ι : Type*}
    (f : V →ₗ[K] (α → K)) (v : ι → V) (p : ι → α)
    (hp : Function.Injective p) (hinit : ∀ i, IsInitialCoefficient f (v i) (p i))
    (s : Finset ι) (g : ι → K) (j : ι) (hj : j ∈ s) (hgj : g j ≠ 0)
    (hmin : ∀ k ∈ s, g k ≠ 0 → p j ≤ p k) :
    IsInitialCoefficient f (∑ k ∈ s, g k • v k) (p j) := by
  constructor
  · rw [initial_min_coefficient_sum f v p hp hinit s g j hj hmin]
    exact mul_ne_zero hgj (hinit j).1
  · intro q hq
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hgk : g k = 0
    · simp [hgk]
    · rw [(hinit k).2 q (hq.trans_le (hmin k hk hgk)), mul_zero]

/-- A triangular coefficient argument, valid for any indexed family. -/
theorem independent_initialCoefficients {ι : Type*}
    (f : V →ₗ[K] (α → K)) (v : ι → V) (p : ι → α)
    (hp : Function.Injective p) (hinit : ∀ i, IsInitialCoefficient f (v i) (p i)) :
    LinearIndependent K v := by
  classical
  apply linearIndependent_iff'.mpr
  intro s g hsum i hi
  by_contra hgi
  let T := s.filter (fun k => g k ≠ 0)
  have hT : (T.image p).Nonempty :=
    ⟨p i, Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hgi⟩, rfl⟩⟩
  obtain ⟨j, hj, hpj⟩ := Finset.mem_image.mp (Finset.min'_mem (T.image p) hT)
  have hj' := Finset.mem_filter.mp hj
  have hmin : ∀ k ∈ s, g k ≠ 0 → p j ≤ p k := by
    intro k hk hgk
    rw [hpj]
    exact Finset.min'_le _ _ (Finset.mem_image.mpr
      ⟨k, Finset.mem_filter.mpr ⟨hk, hgk⟩, rfl⟩)
  have h := sum_has_initialCoefficient f v p hp hinit s g j hj'.1 hj'.2 hmin
  apply h.1
  rw [hsum, map_zero]
  rfl

noncomputable def initialVector (f : V →ₗ[K] (α → K)) (p : initialIndexSet f) : V :=
  Classical.choose p.property

theorem initialVector_spec (f : V →ₗ[K] (α → K)) (p : initialIndexSet f) :
    IsInitialCoefficient f (initialVector f p) p.val := Classical.choose_spec p.property

theorem initialVector_independent (f : V →ₗ[K] (α → K)) :
    LinearIndependent K (initialVector f) :=
  independent_initialCoefficients f _ Subtype.val Subtype.val_injective (initialVector_spec f)

theorem initialIndexSet_finite [FiniteDimensional K V] (f : V →ₗ[K] (α → K)) :
    (initialIndexSet f).Finite :=
  Set.finite_coe_iff.mp (initialVector_independent f).finite

def initialCoefficientMap (f : V →ₗ[K] (α → K)) :
    V →ₗ[K] (initialIndexSet f → K) :=
  LinearMap.pi (fun p => (LinearMap.proj p.val).comp f)

theorem initialCoefficientMap_injective [WellFoundedLT α]
    (f : V →ₗ[K] (α → K)) (hf : Function.Injective f) :
    Function.Injective (initialCoefficientMap f) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  by_contra hv'
  have hfv : f v ≠ 0 := by
    intro h
    exact hv' (hf (h.trans (map_zero f).symm))
  obtain ⟨p, hp⟩ := exists_initialCoefficient f hfv
  have h := congrFun hv (⟨p, v, hp⟩ : initialIndexSet f)
  exact hp.1 h

/-- All possible initial indices, not just the indices of a chosen basis. -/
theorem initialIndexSet_card [FiniteDimensional K V] [WellFoundedLT α]
    (f : V →ₗ[K] (α → K)) (hf : Function.Injective f) :
    (initialIndexSet f).ncard = Module.finrank K V := by
  classical
  let := (initialIndexSet_finite f).fintype
  have hu := (initialVector_independent f).fintype_card_le_finrank
  have hl := LinearMap.finrank_le_finrank_of_injective (initialCoefficientMap_injective f hf)
  have hl' : Module.finrank K V ≤ Fintype.card (initialIndexSet f) := by
    simpa only [Module.finrank_fintype_fun_eq_card] using hl
  rw [← Set.fintypeCard_eq_ncard]
  exact le_antisymm hu hl'

/-- Choosing one witness per initial index already gives an adapted basis. -/
noncomputable def initialCoefficientBasis [FiniteDimensional K V] [WellFoundedLT α]
    (f : V →ₗ[K] (α → K)) (hf : Function.Injective f) :
    Module.Basis (initialIndexSet f) K V := by
  classical
  letI := (initialIndexSet_finite f).fintype
  apply basisOfLinearIndependentOfCardEqFinrank' (initialVector f) (initialVector_independent f)
  simpa only [Set.fintypeCard_eq_ncard] using initialIndexSet_card f hf

theorem initialCoefficientBasis_spec [FiniteDimensional K V] [WellFoundedLT α]
    (f : V →ₗ[K] (α → K)) (hf : Function.Injective f) (p : initialIndexSet f) :
    IsInitialCoefficient f (initialCoefficientBasis f hf p) p := by
  simpa only [initialCoefficientBasis, coe_basisOfLinearIndependentOfCardEqFinrank']
    using initialVector_spec f p

end MixedFujita
