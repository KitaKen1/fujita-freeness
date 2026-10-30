/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
The critical-incidence construction adapts the existing pinned OpenAI Bertini
argument to point-ideal generators; the new algebraic-independence contradiction
handles the base point. No vendored source is modified.
-/
module
public import MixedFujita.PointedBertiniCriticalParameters

@[expose] public section
namespace MixedFujita
open KaehlerDifferential
open OAI.MaximalSeshadri.FrameBertini (DifferentialFrame critical_of_coordinates formallySmooth_quotient_of_gradient)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
/-- A pointed linear system has a nonzero parameter polynomial on its entire critical incidence. -/
theorem pointed_critical_incidence_polynomial
    {K R A ι κ : Type*} [Field K] [CharZero K] [CommRing R] [CommRing A]
    [Algebra K R] [Algebra K A] [Algebra R A] [IsScalarTower K R A]
    [Algebra.FiniteType K A] [Fintype ι] [Fintype κ]
    (b : DifferentialFrame K R κ) (β : R →ₐ[K] K) (v : ι → R)
    (hspan : Ideal.span (Set.range v) = RingHom.ker β.toRingHom)
    (hfirst : ∃ i j, β (b.coord (D K R (v i)) j) ≠ 0) (a : ι → A)
    (hzero : ∑ i, a i * algebraMap R A (v i) = 0)
    (hgrad : ∀ j, ∑ i, a i * algebraMap R A (b.coord (D K R (v i)) j) = 0) :
    ∃ p : MvPolynomial ι K, p ≠ 0 ∧ IsNilpotent (MvPolynomial.aeval a p) := by
  classical
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  let Q := minimalPrimes A
  letI : Fintype Q := (minimalPrimes.finite_of_isNoetherianRing A).fintype
  have hf : ∀ q : Q, ∃ p : MvPolynomial ι K,
      p ≠ 0 ∧ MvPolynomial.aeval a p ∈ q.val := by
    intro q
    let : q.val.IsPrime := q.property.isPrime
    let B := A ⧸ q.val
    let F := FractionRing B
    let : Algebra.EssFiniteType B F :=
      Algebra.EssFiniteType.of_isLocalization F (nonZeroDivisors B)
    let : Algebra.EssFiniteType K F := Algebra.EssFiniteType.comp K B F
    have hzero' : ∑ i, algebraMap A F (a i) * algebraMap R F (v i) = 0 := by
      simpa only [map_sum, map_mul, map_zero,
        ← IsScalarTower.algebraMap_apply R A F] using congrArg (algebraMap A F) hzero
    have hgrad' : ∀ j, ∑ i, algebraMap A F (a i) *
        algebraMap R F (b.coord (D K R (v i)) j) = 0 := by
      intro j
      simpa only [map_sum, map_mul, map_zero,
        ← IsScalarTower.algebraMap_apply R A F] using congrArg (algebraMap A F) (hgrad j)
    obtain ⟨p, hp, he⟩ := pointed_critical_parameters_polynomial (L := F)
      b β v hspan hfirst (fun i => algebraMap A F (a i)) hzero' hgrad'
    refine ⟨p, hp, ?_⟩
    have he' : algebraMap A F (MvPolynomial.aeval a p) = 0 := by
      change (IsScalarTower.toAlgHom K A F) (MvPolynomial.aeval a p) = 0
      rw [MvPolynomial.comp_aeval_apply a (IsScalarTower.toAlgHom K A F)]
      exact he
    have hinj : Function.Injective (algebraMap B F) := IsFractionRing.injective B F
    rw [IsScalarTower.algebraMap_apply A B F] at he'
    have hq : algebraMap A B (MvPolynomial.aeval a p) = 0 :=
      hinj (he'.trans (map_zero _).symm)
    exact Ideal.Quotient.eq_zero_iff_mem.mp hq
  choose p hp hm using hf
  refine ⟨∏ q : Q, p q, Finset.prod_ne_zero_iff.mpr (fun q _ => hp q), ?_⟩
  rw [nilpotent_iff_mem_prime]
  intro J hJ
  let : J.IsPrime := hJ
  obtain ⟨q, hq, hqJ⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A)) (J := J) bot_le
  simp only [map_prod]
  apply (Ideal.IsPrime.prod_mem_iff).mpr
  exact ⟨⟨q, hq⟩, Finset.mem_univ _, hqJ (hm ⟨q, hq⟩)⟩

open OAI.MaximalSeshadri.LinearBertini in
/-- The original universal critical ideal admits a nonzero coefficient condition for a pointed system. -/
theorem pointed_universal_critical_polynomial
    {K R ι κ : Type*} [Field K] [CharZero K] [CommRing R] [Algebra K R]
    [Algebra.FiniteType K R] [Fintype ι] [Fintype κ]
    (b : DifferentialFrame K R κ) (β : R →ₐ[K] K) (v : ι → R)
    (hspan : Ideal.span (Set.range v) = RingHom.ker β.toRingHom)
    (hfirst : ∃ i j, β (b.coord (D K R (v i)) j) ≠ 0) :
    ∃ p : MvPolynomial ι K, p ≠ 0 ∧
      IsNilpotent (MvPolynomial.aeval (fun i =>
        algebraMap (MvPolynomial ι R)
          (MvPolynomial ι R ⧸ criticalIdeal b v) (MvPolynomial.X i)) p) := by
  let T := MvPolynomial ι R
  let A := T ⧸ criticalIdeal b v
  let a : ι → A := fun i => algebraMap T A (MvPolynomial.X i)
  have hC (r : R) : algebraMap T A (MvPolynomial.C r) = algebraMap R A r := rfl
  have hzero : ∑ i, a i * algebraMap R A (v i) = 0 := by
    have he : algebraMap T A (universalSection v) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert _ _))
    simpa only [universalSection, map_sum, map_mul, hC, a] using he
  have hgrad : ∀ j, ∑ i, a i * algebraMap R A (b.coord (D K R (v i)) j) = 0 := by
    intro j
    have he : algebraMap T A (universalGradient b v j) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_range_self j)))
    simpa only [universalGradient, map_sum, map_mul, hC, a] using he
  exact pointed_critical_incidence_polynomial b β v hspan hfirst a hzero hgrad


end MixedFujita
