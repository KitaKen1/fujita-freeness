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
public import MixedFujita.PointedBertiniCriticalLocus

@[expose] public section
namespace MixedFujita
open KaehlerDifferential
open OAI.MaximalSeshadri.FrameBertini (DifferentialFrame critical_of_coordinates formallySmooth_quotient_of_gradient)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open OAI.MaximalSeshadri.LinearBertini in
/-- A nonempty open of coefficients gives smooth affine hypersurfaces through the prescribed point. -/
theorem affine_pointed_bertini_smooth
    {K R ι κ : Type*} [Field K] [CharZero K] [CommRing R] [Algebra K R]
    [Algebra.Smooth K R] [Fintype ι] [Fintype κ]
    (b : DifferentialFrame K R κ) (β : R →ₐ[K] K) (v : ι → R)
    (hspan : Ideal.span (Set.range v) = RingHom.ker β.toRingHom)
    (hfirst : ∃ i j, β (b.coord (D K R (v i)) j) ≠ 0) :
    ∃ p : MvPolynomial ι K, p ≠ 0 ∧ ∀ t : ι → K, MvPolynomial.aeval t p ≠ 0 →
      Algebra.Smooth K (R ⧸ Ideal.span ({specializedSection v t} : Set R)) := by
  obtain ⟨p, hp, hcrit⟩ := pointed_universal_critical_polynomial b β v hspan hfirst
  refine ⟨p, hp, fun t ht => ?_⟩
  have hgrad := critical_specialization_eq_top b v p hcrit t ht
  rw [show specializedGradient b v t = (fun j =>
    b.coord (D K R (specializedSection v t)) j) from
      funext (fun j => (specializedGradient_eq b v t j).symm)] at hgrad
  let : Algebra.FormallySmooth K (R ⧸ Ideal.span ({specializedSection v t} : Set R)) :=
    formallySmooth_quotient_of_gradient b (specializedSection v t) hgrad
  let : Algebra.FinitePresentation K (R ⧸ Ideal.span ({specializedSection v t} : Set R)) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact ⟨inferInstance, inferInstance⟩

open OAI.MaximalSeshadri.LinearBertini in
/-- The whole pointed system vanishes at its designated rational point. -/
theorem pointed_specializedSection_vanishes
    {K R ι : Type*} [Field K] [CommRing R] [Algebra K R] [Fintype ι]
    (β : R →ₐ[K] K) (v : ι → R)
    (hspan : Ideal.span (Set.range v) = RingHom.ker β.toRingHom) (t : ι → K) :
    β (specializedSection v t) = 0 := by
  have hβv (i : ι) : β (v i) = 0 := by
    have hm : v i ∈ Ideal.span (Set.range v) := Ideal.subset_span (Set.mem_range_self i)
    rw [hspan] at hm
    exact hm
  simp only [specializedSection, map_sum, map_mul, hβv, mul_zero, Finset.sum_const_zero]

open OAI.MaximalSeshadri.LinearBertini in
/-- The actual gradient criterion excludes the zero equation. -/
theorem specializedSection_ne_zero_of_gradient_span_eq_top
    {K R ι κ : Type*} [Field K] [CommRing R] [Algebra K R] [Fintype ι] [Fintype κ]
    (b : DifferentialFrame K R κ) (β : R →ₐ[K] K) (v : ι → R) (t : ι → K)
    (hgrad : Ideal.span (insert (specializedSection v t)
      (Set.range (specializedGradient b v t))) = ⊤) : specializedSection v t ≠ 0 := by
  intro hg
  have hzero : specializedGradient b v t = fun _ => 0 := by
    funext j
    rw [← specializedGradient_eq, hg, map_zero, map_zero]
    rfl
  rw [hg, hzero] at hgrad
  have hbot : Ideal.span (insert (0 : R) (Set.range (fun _ : κ => (0 : R)))) = ⊥ := by
    apply Ideal.span_eq_bot.mpr
    rintro r (rfl | ⟨j, rfl⟩) <;> rfl
  rw [hbot] at hgrad
  have hone : (1 : R) ∈ (⊥ : Ideal R) := by rw [hgrad]; exact Submodule.mem_top
  have hK : (1 : K) = 0 := by simpa only [map_one, map_zero] using congrArg β (Ideal.mem_bot.mp hone)
  exact one_ne_zero hK

open OAI.MaximalSeshadri.LinearBertini in
/-- One nonzero polynomial simultaneously ensures a nonzero pointed equation and global affine smoothness. -/
theorem affine_pointed_bertini_regular_equations
    {K R ι κ : Type*} [Field K] [CharZero K] [CommRing R] [Algebra K R]
    [Algebra.Smooth K R] [Fintype ι] [Fintype κ]
    (b : DifferentialFrame K R κ) (β : R →ₐ[K] K) (v : ι → R)
    (hspan : Ideal.span (Set.range v) = RingHom.ker β.toRingHom)
    (hfirst : ∃ i j, β (b.coord (D K R (v i)) j) ≠ 0) :
    ∃ p : MvPolynomial ι K, p ≠ 0 ∧ ∀ t : ι → K, MvPolynomial.aeval t p ≠ 0 →
      specializedSection v t ≠ 0 ∧ β (specializedSection v t) = 0 ∧
        Algebra.Smooth K (R ⧸ Ideal.span ({specializedSection v t} : Set R)) := by
  obtain ⟨p, hp, hcrit⟩ := pointed_universal_critical_polynomial b β v hspan hfirst
  refine ⟨p, hp, fun t ht => ?_⟩
  have hgrad := critical_specialization_eq_top b v p hcrit t ht
  refine ⟨specializedSection_ne_zero_of_gradient_span_eq_top b β v t hgrad,
    pointed_specializedSection_vanishes β v hspan t, ?_⟩
  rw [show specializedGradient b v t = (fun j =>
    b.coord (D K R (specializedSection v t)) j) from
      funext (fun j => (specializedGradient_eq b v t j).symm)] at hgrad
  let : Algebra.FormallySmooth K (R ⧸ Ideal.span ({specializedSection v t} : Set R)) :=
    formallySmooth_quotient_of_gradient b (specializedSection v t) hgrad
  let : Algebra.FinitePresentation K (R ⧸ Ideal.span ({specializedSection v t} : Set R)) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact ⟨inferInstance, inferInstance⟩

open OAI.MaximalSeshadri.LinearBertini in
/-- Pointed affine Bertini can satisfy any extra nonzero polynomial condition on the parameters. -/
theorem affine_pointed_bertini_choose_parameters
    {K R ι κ : Type*} [Field K] [CharZero K] [CommRing R] [Algebra K R]
    [Algebra.Smooth K R] [Fintype ι] [Fintype κ]
    (b : DifferentialFrame K R κ) (β : R →ₐ[K] K) (v : ι → R)
    (hspan : Ideal.span (Set.range v) = RingHom.ker β.toRingHom)
    (hfirst : ∃ i j, β (b.coord (D K R (v i)) j) ≠ 0)
    (q : MvPolynomial ι K) (hq : q ≠ 0) :
    ∃ t : ι → K, MvPolynomial.aeval t q ≠ 0 ∧ specializedSection v t ≠ 0 ∧
      β (specializedSection v t) = 0 ∧
      Algebra.Smooth K (R ⧸ Ideal.span ({specializedSection v t} : Set R)) := by
  obtain ⟨p, hp, hs⟩ := affine_pointed_bertini_regular_equations b β v hspan hfirst
  have hprod : p * q ≠ 0 := mul_ne_zero hp hq
  have hex : ∃ t : ι → K, MvPolynomial.aeval t (p * q) ≠ 0 := by
    by_contra! hn
    apply hprod
    apply MvPolynomial.funext
    intro t
    simpa only [MvPolynomial.aeval_eq_eval, map_zero] using hn t
  obtain ⟨t, ht⟩ := hex
  simp only [map_mul, mul_ne_zero_iff] at ht
  exact ⟨t, ht.2, hs t ht.1⟩

end MixedFujita
