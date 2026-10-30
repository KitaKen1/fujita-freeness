/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCChartComponentPrime
public import MixedFujita.SNCStrataGenericPoints
public import MixedFujita.FibreSNCFamily

/-!
The members of a family of points in simple normal crossing position on a chart cover (step 10,
R4-7).

Let points `ξ_k` of an integral scheme of finite type over a field be in simple normal crossing
position on each chart of a cover by étale charts, with no other assumption on the points. A member
through a chart has a coordinate `a` there (`exists_eq_some_of_mem_isSNCChart`), and its prime ideal
is `(y_a)` (`span_coordinate_eq_primeIdealOf_of_isSNCChart`): a principal prime, nonzero, so of
height one by Krull's principal ideal theorem, and the member has codimension one
(`coheight_eq_one_of_isSNCChart`). Two members through a chart with coordinates `a ≠ b` are
different points, since `y_b` lies in no minimal prime of `(y_a)`
(`etaleChart_coordinate_notMem_stratum_minimalPrime`), so two different members are different
points (`ne_of_isSNCChart`). On a cover this gives the injectivity, the codimension and the simple
normal crossing family (`snc_points_of_cover`). These are the hypotheses on the boundary of the
closed fibre of the model, whose points are given by their closures (check 526).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] {n : ℕ}

attribute [local instance] cartierBaseOpenAlgebra

omit [IsIntegral X] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] in
/-- A member of a simple normal crossing family through a chart has a coordinate there. -/
theorem exists_eq_some_of_mem_isSNCChart (c : EtaleChart K X n) {r : ℕ} (ξ : Fin r → X)
    (σ : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σ) (k : Fin r) (hk : ξ k ∈ c.U) :
    ∃ a, σ k = some a := by
  cases hσ : σ k with
  | none =>
    have h := hc.2 k
    rw [hσ, Option.elim_none] at h
    have hmem : ξ k ∈ closure ({ξ k} : Set X) ∩ c.U := ⟨subset_closure rfl, hk⟩
    rw [h] at hmem
    exact absurd hmem (Set.notMem_empty _)
  | some a => exact ⟨a, rfl⟩

/-- **Two different members of a simple normal crossing family are different points.** -/
theorem ne_of_isSNCChart (c : EtaleChart K X n) {r : ℕ} (ξ : Fin r → X)
    (σ : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σ) {k l : Fin r} (hkl : k ≠ l)
    (hk : ξ k ∈ c.U) : ξ k ≠ ξ l := by
  intro heq
  have hl : ξ l ∈ c.U := heq ▸ hk
  obtain ⟨a, ha⟩ := exists_eq_some_of_mem_isSNCChart c ξ σ hc k hk
  obtain ⟨b, hb⟩ := exists_eq_some_of_mem_isSNCChart c ξ σ hc l hl
  have hab : a ≠ b := fun h => hkl (hc.1 k l a ha (h ▸ hb))
  have h1 := span_coordinate_eq_primeIdealOf_of_isSNCChart c ξ σ hc k a ha hk
  have h2 := span_coordinate_eq_primeIdealOf_of_isSNCChart c ξ σ hc l b hb hl
  have hpt : (⟨ξ k, hk⟩ : c.U) = ⟨ξ l, hl⟩ := Subtype.ext heq
  rw [← hpt] at h2
  have hprime : (Ideal.span {c.coords (MvPolynomial.X a)} : Ideal Γ(X, c.U)).IsPrime := by
    rw [h1]
    exact (c.isAffine.primeIdealOf ⟨ξ k, hk⟩).isPrime
  have hmin : (Ideal.span {c.coords (MvPolynomial.X a)} : Ideal Γ(X, c.U)) ∈
      (etaleChartStratumIdeal c ({a} : Set (Fin n))).minimalPrimes := by
    rw [etaleChartStratumIdeal_eq_span, Set.image_singleton, Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _
  apply etaleChart_coordinate_notMem_stratum_minimalPrime c {a} hmin (b := b)
    (by simpa using hab.symm)
  rw [h1, ← h2]
  exact Ideal.mem_span_singleton_self _

/-- **A member of a simple normal crossing family through a chart has codimension one.** -/
theorem coheight_eq_one_of_isSNCChart [IsLocallyNoetherian X] (c : EtaleChart K X n) {r : ℕ}
    (ξ : Fin r → X) (σ : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σ) (k : Fin r)
    (hk : ξ k ∈ c.U) : Order.coheight (ξ k) = 1 := by
  obtain ⟨a, ha⟩ := exists_eq_some_of_mem_isSNCChart c ξ σ hc k hk
  have h1 := span_coordinate_eq_primeIdealOf_of_isSNCChart c ξ σ hc k a ha hk
  have : IsNoetherianRing Γ(X, c.U) :=
    IsLocallyNoetherian.component_noetherian ⟨c.U, c.isAffine⟩
  have hle : (c.isAffine.primeIdealOf ⟨ξ k, hk⟩).asIdeal.height ≤ 1 := by
    have hmem : (c.isAffine.primeIdealOf ⟨ξ k, hk⟩).asIdeal ∈
        (Ideal.span {c.coords (MvPolynomial.X a)} : Ideal Γ(X, c.U)).minimalPrimes := by
      rw [h1, Ideal.minimalPrimes_eq_subsingleton_self]
      exact Set.mem_singleton _
    exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmem
  have hne : (c.isAffine.primeIdealOf ⟨ξ k, hk⟩).asIdeal.height ≠ 0 := by
    rw [Ne, Ideal.height_eq_zero_iff_eq_bot, ← h1, Ideal.span_singleton_eq_bot]
    exact etaleChart_coordinate_ne_zero c a
  have hheight : (c.isAffine.primeIdealOf ⟨ξ k, hk⟩).asIdeal.height = 1 :=
    le_antisymm hle (Order.one_le_iff_ne_zero.mpr hne)
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨ξ k, hk⟩
  have := c.isAffine.isLocalization_stalk ⟨ξ k, hk⟩
  have hdim := IsLocalization.AtPrime.ringKrullDim_eq_height
    (c.isAffine.primeIdealOf ⟨ξ k, hk⟩).asIdeal (X.presheaf.stalk (ξ k))
  rw [ringKrullDim_stalk_eq_coheight, hheight] at hdim
  exact_mod_cast hdim

/-- **Points in simple normal crossing position on a chart cover**: they are distinct, of
codimension one, and a simple normal crossing family. -/
theorem snc_points_of_cover [IsLocallyNoetherian X] {r : ℕ} (ξ : Fin r → X) {ι : Type*}
    (c : ι → EtaleChart K X n) (σ : ι → Fin r → Option (Fin n))
    (hc : ∀ i, IsSNCChart (c i) ξ (σ i)) (hcov : ∀ x : X, ∃ i, x ∈ (c i).U) :
    Function.Injective ξ ∧ (∀ k, Order.coheight (ξ k) = 1) ∧ IsSNCFamily K n ξ := by
  refine ⟨fun k l hkl => ?_, fun k => ?_, isSNCFamily_of_cover ξ c σ hc hcov⟩
  · by_contra hne
    obtain ⟨i, hi⟩ := hcov (ξ k)
    exact ne_of_isSNCChart (c i) ξ (σ i) (hc i) hne hi hkl
  · obtain ⟨i, hi⟩ := hcov (ξ k)
    exact coheight_eq_one_of_isSNCChart (c i) ξ (σ i) (hc i) k hi

end MixedFujita
