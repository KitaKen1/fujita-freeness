/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveDehomogenizationCoefficients
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
Homogenization in a fixed degree. Padding each exponent with the k-th
coordinate turns a polynomial on the other coordinates of total degree at
most D into a homogeneous polynomial of degree D whose dehomogenization is
the original polynomial. The padded exponent is given explicitly and only
verified, so no inverse of the chart isomorphism is needed.
-/

@[expose] public section

namespace MixedFujita

variable {n : ℕ} {R : Type*} [CommRing R]

/-- Pad an exponent on the coordinates other than k to total degree D. -/
noncomputable def projectiveHomogenizeExponent (k : Fin n) (D : ℕ)
    (q : {j : Fin n // j ≠ k} →₀ ℕ) : Fin n →₀ ℕ :=
  q.extendDomain + Finsupp.single k (D - q.degree)

theorem projectiveHomogenizeExponent_subtypeDomain (k : Fin n) (D : ℕ)
    (q : {j : Fin n // j ≠ k} →₀ ℕ) :
    (projectiveHomogenizeExponent k D q).subtypeDomain (fun i => i ≠ k) = q := by
  ext ⟨i, hi⟩
  simp [projectiveHomogenizeExponent, hi]

theorem extendDomain_degree_ne (k : Fin n) (q : {j : Fin n // j ≠ k} →₀ ℕ) :
    (q.extendDomain).degree = q.degree := by
  rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum,
    ← Fintype.sum_subtype_add_sum_subtype (fun i : Fin n => i ≠ k)]
  have h2 : ∑ i : {i : Fin n // ¬ i ≠ k}, (q.extendDomain) i.val = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp [Finsupp.extendDomain_apply, i.property]
  rw [h2, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  simp [Finsupp.extendDomain_apply, i.property]

theorem projectiveHomogenizeExponent_degree (k : Fin n) {D : ℕ}
    (q : {j : Fin n // j ≠ k} →₀ ℕ) (hq : q.degree ≤ D) :
    (projectiveHomogenizeExponent k D q).degree = D := by
  rw [projectiveHomogenizeExponent, map_add, extendDomain_degree_ne, Finsupp.degree_single]
  omega

/-- The degree-D homogenization of a polynomial on the coordinates other than k. -/
noncomputable def projectiveHomogenize (k : Fin n) (D : ℕ)
    (P : MvPolynomial {j : Fin n // j ≠ k} R) : MvPolynomial (Fin n) R :=
  ∑ q ∈ P.support, MvPolynomial.monomial (projectiveHomogenizeExponent k D q) (P.coeff q)

theorem projectiveDehomogenize_homogenize (k : Fin n) (D : ℕ)
    (P : MvPolynomial {j : Fin n // j ≠ k} R) :
    projectiveDehomogenize R k (projectiveHomogenize k D P) = P := by
  rw [projectiveHomogenize, map_sum]
  simp_rw [projectiveDehomogenize_monomial_restrict, projectiveHomogenizeExponent_subtypeDomain]
  exact P.as_sum.symm

theorem projectiveHomogenize_isHomogeneous (k : Fin n) {D : ℕ}
    (P : MvPolynomial {j : Fin n // j ≠ k} R) (hP : P.totalDegree ≤ D) :
    (projectiveHomogenize k D P).IsHomogeneous D := by
  apply MvPolynomial.IsHomogeneous.sum
  intro q hq
  apply MvPolynomial.isHomogeneous_monomial
  apply projectiveHomogenizeExponent_degree
  have h := MvPolynomial.le_totalDegree hq
  rw [Finsupp.degree_apply]
  exact h.trans hP

end MixedFujita
