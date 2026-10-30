/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PolynomialProjectiveScheme
public import MixedFujita.PolynomialNonzeroLocus
public import Mathlib.Algebra.Polynomial.Roots

/-!
Actual K-valued points of Spec K[T]. Over an infinite field, any Zariski
open containing such a point has another K-valued point outside any specified
finite set. Properness therefore transfers avoidance of a closed bad locus
at zero to some nonzero K-valued parameter. Closedness of a threshold bad
locus is not proved or assumed implicitly by this module.
-/

@[expose] public section

namespace MixedFujita

open AlgebraicGeometry TopologicalSpace

universe u

variable {K : Type u} [Field K]

noncomputable def fieldSpectrumPoint (K : Type u) [Field K] : PrimeSpectrum K :=
  ⟨⊥, Ideal.isPrime_bot⟩

noncomputable def polynomialParameterPoint (t : K) : Spec (CommRingCat.of (Polynomial K)) :=
  PrimeSpectrum.comap (Polynomial.evalRingHom t) (fieldSpectrumPoint K)

theorem polynomialParameterPoint_mem_basicOpen (t : K) (q : Polynomial K) :
    polynomialParameterPoint t ∈ PrimeSpectrum.basicOpen q ↔ q.eval t ≠ 0 :=
  Iff.rfl

theorem polynomialParameterPoint_mem_nonzeroLocus {σ : Type*}
    (t : K) (f : MvPolynomial σ (Polynomial K)) :
    polynomialParameterPoint t ∈ polynomialNonzeroLocus f ↔
      MvPolynomial.map (Polynomial.evalRingHom t) f ≠ 0 := by
  change ¬ polynomialCoefficientIdeal f ≤ RingHom.ker (Polynomial.evalRingHom t) ↔ _
  rw [← polynomial_map_eq_zero_iff]

theorem polynomialParameterPoint_mem_open_outside_finset [Infinite K]
    (U : (Spec (CommRingCat.of (Polynomial K))).Opens) (r : K)
    (hr : polynomialParameterPoint r ∈ U) (s : Finset K) :
    ∃ t : K, t ∉ s ∧ polynomialParameterPoint t ∈ U := by
  classical
  obtain ⟨_, ⟨q, rfl⟩, hqr, hqU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp
      U.isOpen (polynomialParameterPoint r) hr
  have hq : q ≠ 0 := by
    intro h
    have hqr' := (polynomialParameterPoint_mem_basicOpen r q).mp hqr
    exact hqr' (by rw [h, Polynomial.eval_zero])
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset (s ∪ q.roots.toFinset)
  have hs : t ∉ s := fun h => ht (Finset.mem_union_left _ h)
  have hroot : q.eval t ≠ 0 := by
    intro h
    exact ht (Finset.mem_union_right _ (Multiset.mem_toFinset.mpr
      ((Polynomial.mem_roots hq).mpr h)))
  exact ⟨t, hs, hqU ((polynomialParameterPoint_mem_basicOpen t q).mpr hroot)⟩

theorem polynomialParameterPoint_mem_open_nonzero [Infinite K]
    (U : (Spec (CommRingCat.of (Polynomial K))).Opens) (r : K)
    (hr : polynomialParameterPoint r ∈ U) :
    ∃ t : K, t ≠ 0 ∧ polynomialParameterPoint t ∈ U := by
  obtain ⟨t, ht, hU⟩ := polynomialParameterPoint_mem_open_outside_finset U r hr {0}
  exact ⟨t, by simpa only [Finset.mem_singleton] using ht, hU⟩

theorem polynomialParameterPoint_nonzero_form_in_open [Infinite K] {σ : Type*}
    (U : (Spec (CommRingCat.of (Polynomial K))).Opens) (r : K)
    (hr : polynomialParameterPoint r ∈ U) (f : MvPolynomial σ (Polynomial K))
    (hf : MvPolynomial.map (Polynomial.evalRingHom r) f ≠ 0) :
    ∃ t : K, t ≠ 0 ∧ polynomialParameterPoint t ∈ U ∧
      MvPolynomial.map (Polynomial.evalRingHom t) f ≠ 0 := by
  obtain ⟨t, ht, hU, hf'⟩ := polynomialParameterPoint_mem_open_nonzero
    (U ⊓ polynomialNonzeroLocus f) r
    ⟨hr, (polynomialParameterPoint_mem_nonzeroLocus r f).mpr hf⟩
  exact ⟨t, ht, hU, (polynomialParameterPoint_mem_nonzeroLocus t f).mp hf'⟩

theorem polynomialProjective_nonzero_parameter_avoids_closed_bad_locus
    {n : ℕ} [Infinite K] {Z : Set (polynomialProjectiveScheme n (Polynomial K))}
    (hZ : IsClosed Z)
    (hzero : ∀ x, polynomialProjectiveToBase n (Polynomial K) x =
      polynomialParameterPoint (0 : K) → x ∉ Z) :
    ∃ t : K, t ≠ 0 ∧ ∀ x, polynomialProjectiveToBase n (Polynomial K) x =
      polynomialParameterPoint t → x ∉ Z := by
  obtain ⟨U, hU, hgood⟩ := polynomialProjectiveToBase_good_neighborhood
    n (Polynomial K) hZ (polynomialParameterPoint (0 : K)) hzero
  obtain ⟨t, ht, hUt⟩ := polynomialParameterPoint_mem_open_nonzero U 0 hU
  exact ⟨t, ht, fun x hx => hgood x (hx ▸ hUt)⟩

end MixedFujita
