/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PointBlowupStrictTransform
public import MixedFujita.HomogeneousTaylor
public import MixedFujita.ProjectiveDehomogenizationCoefficients
public import Mathlib.RingTheory.MvPowerSeries.Rename

/-!
Exact restriction of the formal point-blow-up strict transform to the exceptional coordinate.
The resulting series is the polynomial leading form dehomogenized on the projective chart.
This is an equality of the actual series, including all higher-order terms of the input.
-/

@[expose] public section
namespace MixedFujita
open MvPowerSeries
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ} {K : Type*} [Field K]

/-- Set the exceptional coordinate to zero and retain the other coordinates. -/
noncomputable def pointBlowupExceptionalRestriction (k : Fin n) :
    MvPowerSeries (Fin n) K →ₐ[K] MvPowerSeries {i : Fin n // i ≠ k} K :=
  MvPowerSeries.killCompl ⟨Subtype.val, Subtype.val_injective⟩

theorem pointBlowupEmbeddedExponent_degree (k : Fin n)
    (q : {i : Fin n // i ≠ k} →₀ ℕ) :
    (Finsupp.embDomain ⟨Subtype.val, Subtype.val_injective⟩ q : Fin n →₀ ℕ).degree = q.degree := by
  simp only [Finsupp.degree_apply, Finsupp.support_embDomain, Finset.sum_map,
    Finsupp.embDomain_apply_self]

theorem pointBlowupEmbeddedExponent_self (k : Fin n)
    (q : {i : Fin n // i ≠ k} →₀ ℕ) :
    (Finsupp.embDomain ⟨Subtype.val, Subtype.val_injective⟩ q : Fin n →₀ ℕ) k = 0 := by
  apply Finsupp.embDomain_of_notMem_range
  rintro ⟨i, hi⟩
  exact i.property hi

theorem pointBlowupEmbeddedExponent_sum_erase (k : Fin n)
    (q : {i : Fin n // i ≠ k} →₀ ℕ) :
    ∑ i ∈ Finset.univ.erase k,
      (Finsupp.embDomain ⟨Subtype.val, Subtype.val_injective⟩ q : Fin n →₀ ℕ) i = q.degree := by
  have h := Finset.add_sum_erase Finset.univ
    (fun i => (Finsupp.embDomain ⟨Subtype.val, Subtype.val_injective⟩ q : Fin n →₀ ℕ) i)
    (Finset.mem_univ k)
  rw [pointBlowupEmbeddedExponent_self, zero_add, ← Finsupp.degree_eq_sum,
    pointBlowupEmbeddedExponent_degree] at h
  exact h

theorem pointBlowupLiftedExponent_restrict (k : Fin n) (m : ℕ)
    (q : {i : Fin n // i ≠ k} →₀ ℕ) :
    ((Finsupp.embDomain ⟨Subtype.val, Subtype.val_injective⟩ q : Fin n →₀ ℕ) +
      Finsupp.single k (m - q.degree)).subtypeDomain (fun i => i ≠ k) = q := by
  ext i
  rw [Finsupp.subtypeDomain_apply, Finsupp.add_apply]
  have hx := Finsupp.embDomain_apply_self
    (⟨Subtype.val, Subtype.val_injective⟩ : {i : Fin n // i ≠ k} ↪ Fin n) q i
  rw [show (Finsupp.embDomain ⟨Subtype.val, Subtype.val_injective⟩ q : Fin n →₀ ℕ) i.val =
    q i from hx, Finsupp.single_eq_of_ne i.property, add_zero]

theorem pointBlowupLiftedExponent_degree (k : Fin n) (m : ℕ)
    (q : {i : Fin n // i ≠ k} →₀ ℕ) (hq : q.degree ≤ m) :
    ((Finsupp.embDomain ⟨Subtype.val, Subtype.val_injective⟩ q : Fin n →₀ ℕ) +
      Finsupp.single k (m - q.degree)).degree = m := by
  rw [map_add, pointBlowupEmbeddedExponent_degree, Finsupp.degree_single]
  omega

theorem projectiveExponent_restricted_degree_le (k : Fin n) (p : Fin n →₀ ℕ) :
    (p.subtypeDomain (fun i => i ≠ k)).degree ≤ p.degree := by
  have he : (Finsupp.embDomain ⟨Subtype.val, Subtype.val_injective⟩
      (p.subtypeDomain (fun i => i ≠ k)) : Fin n →₀ ℕ) + Finsupp.single k (p k) = p := by
    ext i
    by_cases hi : i = k
    · subst i
      simp only [Finsupp.add_apply, pointBlowupEmbeddedExponent_self, Finsupp.single_eq_same,
        zero_add]
    · have hx := Finsupp.embDomain_apply_self
        (⟨Subtype.val, Subtype.val_injective⟩ : {i : Fin n // i ≠ k} ↪ Fin n)
        (p.subtypeDomain (fun i => i ≠ k)) ⟨i, hi⟩
      rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hi, add_zero]
      exact hx
  have hd := congrArg Finsupp.degree he
  rw [map_add, pointBlowupEmbeddedExponent_degree, Finsupp.degree_single] at hd
  omega

theorem projectiveDehomogenize_coeff_zero_of_degree_gt (k : Fin n)
    (g : MvPolynomial (Fin n) K) (m : ℕ) (hg : g.IsHomogeneous m)
    (q : {i : Fin n // i ≠ k} →₀ ℕ) (hq : m < q.degree) :
    (projectiveDehomogenize K k g).coeff q = 0 := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum g]
  simp only [map_sum, projectiveDehomogenize_monomial_restrict, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial]
  apply Finset.sum_eq_zero
  intro p hp
  apply ite_eq_right
  intro he
  have hpdeg : p.degree = m := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using
      hg (MvPolynomial.mem_support_iff.mp hp)
  have hle := projectiveExponent_restricted_degree_le k p
  rw [he, hpdeg] at hle
  omega

theorem pointBlowupExceptionalRestriction_strictTransform (k : Fin n) (m : ℕ)
    (φ : MvPowerSeries (Fin n) K) :
    pointBlowupExceptionalRestriction k (pointBlowupStrictTransform k m φ) =
      (projectiveDehomogenize K k (homogeneousTaylorForm m φ) :
        MvPowerSeries {i : Fin n // i ≠ k} K) := by
  ext q
  rw [pointBlowupExceptionalRestriction, MvPowerSeries.coeff_killCompl,
    coeff_pointBlowupStrictTransform_of_eq_zero k m φ _
      (pointBlowupEmbeddedExponent_self k q), pointBlowupEmbeddedExponent_sum_erase,
    MvPolynomial.coeff_coe]
  by_cases hq : q.degree ≤ m
  · rw [ite_eq_left hq]
    have he := projectiveDehomogenize_coeff_homogeneous k (homogeneousTaylorForm m φ) m
      (homogeneousTaylorForm_isHomogeneous m φ) _ (pointBlowupLiftedExponent_degree k m q hq)
    rw [pointBlowupLiftedExponent_restrict, homogeneousTaylorForm_coeff,
      ite_eq_left (pointBlowupLiftedExponent_degree k m q hq)] at he
    exact he.symm
  · rw [ite_eq_right hq, projectiveDehomogenize_coeff_zero_of_degree_gt k _ m
      (homogeneousTaylorForm_isHomogeneous m φ) q (Nat.lt_of_not_ge hq)]

end MixedFujita
