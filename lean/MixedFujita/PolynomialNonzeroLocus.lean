/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
The actual Zariski open parameter locus where a polynomial remains nonzero
in the residue-field polynomial ring. Its complement is defined by the
finitely generated ideal of coefficients. This is the fiberwise regular
equation input, not a relative Cartier or lct semicontinuity theorem.
-/

@[expose] public section

namespace MixedFujita

variable {R S σ : Type*} [CommRing R] [CommRing S]

noncomputable def polynomialCoefficientIdeal (f : MvPolynomial σ R) : Ideal R :=
  Ideal.span (Set.range f.coeff)

theorem polynomialCoefficientIdeal_le_iff (f : MvPolynomial σ R) (J : Ideal R) :
    polynomialCoefficientIdeal f ≤ J ↔ ∀ q, f.coeff q ∈ J := by
  rw [polynomialCoefficientIdeal, Ideal.span_le]
  exact ⟨fun h q => h (Set.mem_range_self q), fun h _ ⟨q, hq⟩ => hq ▸ h q⟩

theorem polynomial_map_eq_zero_iff (c : R →+* S) (f : MvPolynomial σ R) :
    MvPolynomial.map c f = 0 ↔ polynomialCoefficientIdeal f ≤ RingHom.ker c := by
  rw [polynomialCoefficientIdeal_le_iff, MvPolynomial.ext_iff]
  simp only [MvPolynomial.coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply,
    RingHom.mem_ker]

theorem polynomialCoefficientIdeal_map (c : R →+* S) (f : MvPolynomial σ R) :
    polynomialCoefficientIdeal (MvPolynomial.map c f) =
      Ideal.map c (polynomialCoefficientIdeal f) := by
  rw [polynomialCoefficientIdeal, polynomialCoefficientIdeal, Ideal.map_span,
    ← Set.range_comp']
  congr 2

theorem polynomialCoefficientIdeal_support (f : MvPolynomial σ R) :
    polynomialCoefficientIdeal f = Ideal.span (f.coeff '' (f.support : Set (σ →₀ ℕ))) := by
  apply le_antisymm
  · rw [polynomialCoefficientIdeal_le_iff]
    intro q
    by_cases hq : q ∈ f.support
    · exact Ideal.subset_span ⟨q, hq, rfl⟩
    · rw [MvPolynomial.notMem_support_iff.mp hq]
      exact Ideal.zero_mem _
  · apply Ideal.span_le.mpr
    rintro _ ⟨q, _, rfl⟩
    exact Ideal.subset_span (Set.mem_range_self q)

theorem polynomialCoefficientIdeal_finite_generators (f : MvPolynomial σ R) :
    ∃ s : Finset R, polynomialCoefficientIdeal f = Ideal.span (s : Set R) := by
  classical
  refine ⟨f.support.image f.coeff, ?_⟩
  rw [polynomialCoefficientIdeal_support, Finset.coe_image]

noncomputable def polynomialNonzeroLocus (f : MvPolynomial σ R) :
    TopologicalSpace.Opens (PrimeSpectrum R) :=
  ⟨(PrimeSpectrum.zeroLocus (polynomialCoefficientIdeal f : Set R))ᶜ,
    (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩

theorem polynomialNonzeroLocus_mem (f : MvPolynomial σ R) (p : PrimeSpectrum R) :
    p ∈ polynomialNonzeroLocus f ↔
      MvPolynomial.map (algebraMap R p.asIdeal.ResidueField) f ≠ 0 := by
  change ¬ p ∈ PrimeSpectrum.zeroLocus (polynomialCoefficientIdeal f : Set R) ↔ _
  rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
  simp only [ne_eq, polynomial_map_eq_zero_iff, Ideal.ker_algebraMap_residueField]

theorem polynomialNonzeroLocus_finite_basicOpen_cover (f : MvPolynomial σ R) :
    (polynomialNonzeroLocus f : Set (PrimeSpectrum R)) =
      ⋃ q ∈ f.support, (PrimeSpectrum.basicOpen (f.coeff q) : Set (PrimeSpectrum R)) := by
  ext p
  change (¬ polynomialCoefficientIdeal f ≤ p.asIdeal) ↔ _
  simp only [Set.mem_iUnion]
  rw [polynomialCoefficientIdeal_le_iff]
  push Not
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q, MvPolynomial.mem_support_iff.mpr (fun hz => hq (hz ▸ p.asIdeal.zero_mem)), hq⟩
  · rintro ⟨q, _, hq⟩
    exact ⟨q, hq⟩

theorem polynomialNonzeroLocus_baseChange (c : R →+* S) (f : MvPolynomial σ R) :
    (PrimeSpectrum.comap c) ⁻¹' (polynomialNonzeroLocus f : Set (PrimeSpectrum R)) =
      (polynomialNonzeroLocus (MvPolynomial.map c f) : Set (PrimeSpectrum S)) := by
  ext p
  change ¬ polynomialCoefficientIdeal f ≤ p.asIdeal.comap c ↔
    ¬ polynomialCoefficientIdeal (MvPolynomial.map c f) ≤ p.asIdeal
  rw [polynomialCoefficientIdeal_map, Ideal.map_le_iff_le_comap]

theorem polynomialNonzeroLocus_fiber_regular (f : MvPolynomial σ R) (p : PrimeSpectrum R) :
    p ∈ polynomialNonzeroLocus f ↔
      MvPolynomial.map (algebraMap R p.asIdeal.ResidueField) f ∈
        nonZeroDivisors (MvPolynomial σ p.asIdeal.ResidueField) := by
  rw [polynomialNonzeroLocus_mem, mem_nonZeroDivisors_iff_ne_zero]

end MixedFujita
