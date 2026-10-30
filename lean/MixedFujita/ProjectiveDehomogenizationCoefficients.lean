/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveChartAlgebra

/-!
Deleting one exponent coordinate is injective in a fixed total degree.
Thus dehomogenization of a homogeneous polynomial preserves each coefficient,
including an arbitrary chosen unit coefficient, in every projective chart.
-/

@[expose] public section

namespace MixedFujita

variable {n : ℕ} {R : Type*} [CommRing R]

theorem projectiveDehomogenize_monomial_restrict (k : Fin n)
    (p : Fin n →₀ ℕ) (r : R) :
    projectiveDehomogenize R k (MvPolynomial.monomial p r) =
      MvPolynomial.monomial (p.subtypeDomain (fun i => i ≠ k)) r := by
  classical
  rw [projectiveDehomogenize_monomial, MvPolynomial.monomial_eq,
    p.prod_fintype _ (fun _ => pow_zero _),
    (p.subtypeDomain (fun i => i ≠ k)).prod_fintype _ (fun _ => pow_zero _)]
  congr 1
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i : Fin n => i ≠ k)]
  have h₁ (i : {i : Fin n // i ≠ k}) :
      projectiveChartVariable R k i.val ^ p i.val = MvPolynomial.X i ^ p i.val := by
    simp [projectiveChartVariable, i.property]
  have h₂ (i : {i : Fin n // ¬i ≠ k}) :
      projectiveChartVariable R k i.val ^ p i.val = 1 := by
    have hi : i.val = k := not_not.mp i.property
    simp [projectiveChartVariable, hi]
  simp only [h₁, h₂, Finset.prod_const_one, mul_one, Finsupp.subtypeDomain_apply]

theorem projectiveExponent_restrict_injective_of_degree (k : Fin n)
    (p q : Fin n →₀ ℕ) (hd : p.degree = q.degree)
    (h : p.subtypeDomain (fun i => i ≠ k) = q.subtypeDomain (fun i => i ≠ k)) : p = q := by
  have ho (i : Fin n) (hi : i ≠ k) : p i = q i :=
    DFunLike.congr_fun h ⟨i, hi⟩
  have hs : ∑ i ∈ Finset.univ.erase k, p i = ∑ i ∈ Finset.univ.erase k, q i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact ho i (Finset.ne_of_mem_erase hi)
  have hp : p k + ∑ i ∈ Finset.univ.erase k, p i = p.degree := by
    simpa only [Finsupp.degree_eq_sum] using
      (Finset.add_sum_erase Finset.univ (fun i => p i) (Finset.mem_univ k))
  have hq : q k + ∑ i ∈ Finset.univ.erase k, q i = q.degree := by
    simpa only [Finsupp.degree_eq_sum] using
      (Finset.add_sum_erase Finset.univ (fun i => q i) (Finset.mem_univ k))
  apply Finsupp.ext
  intro i
  by_cases hi : i = k
  · subst i
    omega
  · exact ho i hi

theorem projectiveDehomogenize_coeff_homogeneous (k : Fin n)
    (f : MvPolynomial (Fin n) R) (d : ℕ) (hf : f.IsHomogeneous d)
    (q : Fin n →₀ ℕ) (hq : q.degree = d) :
    (projectiveDehomogenize R k f).coeff (q.subtypeDomain (fun i => i ≠ k)) = f.coeff q := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum f]
  simp only [map_sum, projectiveDehomogenize_monomial_restrict, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial]
  have he : ∀ p ∈ f.support,
      (if p.subtypeDomain (fun i => i ≠ k) = q.subtypeDomain (fun i => i ≠ k)
        then f.coeff p else 0) = (if p = q then f.coeff p else 0) := by
    intro p hp
    have hpdeg : p.degree = d := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using
        hf (MvPolynomial.mem_support_iff.mp hp)
    have hi : p.subtypeDomain (fun i => i ≠ k) = q.subtypeDomain (fun i => i ≠ k) ↔ p = q :=
      ⟨projectiveExponent_restrict_injective_of_degree k p q (hpdeg.trans hq.symm),
        fun h => congrArg (Finsupp.subtypeDomain (fun i => i ≠ k)) h⟩
    simp only [hi]
  rw [Finset.sum_congr rfl he]
  simp only [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (MvPolynomial.notMem_support_iff.mp h).symm

theorem projectiveDehomogenize_has_unit_coefficient (k : Fin n)
    (f : MvPolynomial (Fin n) R) (d : ℕ) (hf : f.IsHomogeneous d)
    (q : Fin n →₀ ℕ) (hq : IsUnit (f.coeff q)) :
    ∃ p : {j : Fin n // j ≠ k} →₀ ℕ, IsUnit ((projectiveDehomogenize R k f).coeff p) := by
  by_cases hd : q.degree = d
  · exact ⟨q.subtypeDomain (fun i => i ≠ k),
      projectiveDehomogenize_coeff_homogeneous k f d hf q hd ▸ hq⟩
  · have h0 : IsUnit (0 : R) := (hf.coeff_eq_zero hd) ▸ hq
    let _ : Subsingleton R := subsingleton_iff_zero_eq_one.mp (isUnit_zero_iff.mp h0)
    refine ⟨0, ?_⟩
    rw [Subsingleton.elim ((projectiveDehomogenize R k f).coeff 0) (0 : R)]
    exact h0

end MixedFujita
