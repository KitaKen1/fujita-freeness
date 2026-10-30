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
public import OAI.AlgebraicGeometry.Seshadri.Bertini.LinearFamilies

@[expose] public section
namespace MixedFujita
open KaehlerDifferential
open OAI.MaximalSeshadri.FrameBertini (DifferentialFrame critical_of_coordinates formallySmooth_quotient_of_gradient)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
/-- Killing generators of a rational point ideal forces an algebra map to factor through that point. -/
theorem algebraMap_eq_point_evaluation_of_generators_vanish
    {K R A ι : Type*} [Field K] [CommRing R] [CommRing A]
    [Algebra K R] [Algebra K A] [Algebra R A] [IsScalarTower K R A]
    (β : R →ₐ[K] K) (v : ι → R)
    (hspan : Ideal.span (Set.range v) = RingHom.ker β.toRingHom)
    (hz : ∀ i, algebraMap R A (v i) = 0) (r : R) :
    algebraMap R A r = algebraMap K A (β r) := by
  have hle : Ideal.span (Set.range v) ≤ RingHom.ker (algebraMap R A) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hz i
  have hr : r - algebraMap K R (β r) ∈ Ideal.span (Set.range v) := by
    rw [hspan]
    change β (r - algebraMap K R (β r)) = 0
    simp
  have he := hle hr
  change algebraMap R A (r - algebraMap K R (β r)) = 0 at he
  rw [map_sub, ← IsScalarTower.algebraMap_apply K R A] at he
  exact sub_eq_zero.mp he

theorem pointed_critical_parameters_dependent
    {K R L ι κ : Type*} [Field K] [CharZero K] [CommRing R] [Field L]
    [Algebra K R] [Algebra K L] [Algebra R L] [IsScalarTower K R L]
    [Algebra.EssFiniteType K L] [Fintype ι] [Fintype κ]
    (b : DifferentialFrame K R κ) (β : R →ₐ[K] K) (v : ι → R)
    (hspan : Ideal.span (Set.range v) = RingHom.ker β.toRingHom)
    (hfirst : ∃ i j, β (b.coord (D K R (v i)) j) ≠ 0) (a : ι → L)
    (hzero : ∑ i, a i * algebraMap R L (v i) = 0)
    (hgrad : ∀ j, ∑ i, a i * algebraMap R L (b.coord (D K R (v i)) j) = 0) :
    ¬ AlgebraicIndependent K a := by
  intro ha
  have hcritical := critical_of_coordinates b v a hgrad
  have hd := congrArg (D K L) hzero
  simp only [map_sum, Derivation.leibniz, map_zero, Finset.sum_add_distrib,
    hcritical, zero_add] at hd
  have hi := OAI.MaximalSeshadri.Bertini.algebraicIndependent_differentials a ha
  have hz := (Fintype.linearIndependent_iff.mp hi) (fun i => algebraMap R L (v i)) hd
  have hfactor := algebraMap_eq_point_evaluation_of_generators_vanish β v hspan hz
  obtain ⟨i, j, hfirst⟩ := hfirst
  have hlin : ∑ i, β (b.coord (D K R (v i)) j) • a i = 0 := by
    have h := hgrad j
    simp_rw [hfactor] at h
    simpa only [Algebra.smul_def, mul_comm] using h
  exact hfirst ((Fintype.linearIndependent_iff.mp ha.linearIndependent) _ hlin i)

theorem pointed_critical_parameters_polynomial
    {K R L ι κ : Type*} [Field K] [CharZero K] [CommRing R] [Field L]
    [Algebra K R] [Algebra K L] [Algebra R L] [IsScalarTower K R L]
    [Algebra.EssFiniteType K L] [Fintype ι] [Fintype κ]
    (b : DifferentialFrame K R κ) (β : R →ₐ[K] K) (v : ι → R)
    (hspan : Ideal.span (Set.range v) = RingHom.ker β.toRingHom)
    (hfirst : ∃ i j, β (b.coord (D K R (v i)) j) ≠ 0) (a : ι → L)
    (hzero : ∑ i, a i * algebraMap R L (v i) = 0)
    (hgrad : ∀ j, ∑ i, a i * algebraMap R L (b.coord (D K R (v i)) j) = 0) :
    ∃ p : MvPolynomial ι K, p ≠ 0 ∧ MvPolynomial.aeval a p = 0 := by
  have h := pointed_critical_parameters_dependent b β v hspan hfirst a hzero hgrad
  classical
  rw [algebraicIndependent_iff] at h
  push Not at h
  obtain ⟨p, hp, hne⟩ := h
  exact ⟨p, hne, hp⟩

end MixedFujita
