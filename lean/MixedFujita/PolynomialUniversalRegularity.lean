/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PolynomialNonzeroLocus
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
Iterated McCoy regularity for a finite set of variables. A unit coefficient
gives a regular equation after every coefficient-ring homomorphism, including
maps to rings with zero divisors. Each coefficient basic open of the nonzero
locus therefore has a universally regular equation. Quotient flatness and
the relative effective Cartier construction are separate obligations.
-/

@[expose] public section

namespace MixedFujita

variable {R S T σ : Type*} [CommRing R] [CommRing S] [CommRing T]

theorem finPolynomial_regular_of_coefficient {n : ℕ}
    (f : MvPolynomial (Fin n) R) (q : Fin n →₀ ℕ)
    (hq : f.coeff q ∈ nonZeroDivisors R) :
    f ∈ nonZeroDivisors (MvPolynomial (Fin n) R) := by
  induction n with
  | zero =>
    have hq0 : q = 0 := Subsingleton.elim _ _
    apply mem_nonZeroDivisors_of_injective (MvPolynomial.isEmptyRingEquiv R (Fin 0)).injective
    simpa only [MvPolynomial.isEmptyRingEquiv_eq_coeff_zero, hq0] using hq
  | succ n ih =>
    apply mem_nonZeroDivisors_of_injective (MvPolynomial.finSuccEquiv R n).injective
    apply Polynomial.mem_nonZeroDivisors_of_coeff_mem (q 0)
    apply ih _ (Finsupp.tail q)
    simpa only [MvPolynomial.finSuccEquiv_coeff_coeff, Finsupp.cons_tail] using hq

theorem finitePolynomial_regular_of_coefficient [Finite σ]
    (f : MvPolynomial σ R) (q : σ →₀ ℕ)
    (hq : f.coeff q ∈ nonZeroDivisors R) :
    f ∈ nonZeroDivisors (MvPolynomial σ R) := by
  classical
  let _ := Fintype.ofFinite σ
  let e := Fintype.equivFin σ
  apply mem_nonZeroDivisors_of_injective (MvPolynomial.renameEquiv R e).injective
  apply finPolynomial_regular_of_coefficient _ (q.mapDomain e)
  simpa only [MvPolynomial.renameEquiv_apply,
    MvPolynomial.coeff_rename_mapDomain e e.injective] using hq

theorem finitePolynomial_regular_of_unit_coefficient [Finite σ]
    (f : MvPolynomial σ R) (q : σ →₀ ℕ) (hq : IsUnit (f.coeff q)) :
    f ∈ nonZeroDivisors (MvPolynomial σ R) :=
  finitePolynomial_regular_of_coefficient f q hq.mem_nonZeroDivisors

theorem finitePolynomial_unit_coefficient_baseChange [Finite σ]
    (c : R →+* S) (f : MvPolynomial σ R) (q : σ →₀ ℕ)
    (hq : IsUnit (f.coeff q)) :
    MvPolynomial.map c f ∈ nonZeroDivisors (MvPolynomial σ S) := by
  apply finitePolynomial_regular_of_unit_coefficient _ q
  rw [MvPolynomial.coeff_map]
  exact hq.map c

theorem finitePolynomial_localized_coefficient_regular [Finite σ]
    (f : MvPolynomial σ R) (q : σ →₀ ℕ) [Algebra R S]
    [IsLocalization.Away (f.coeff q) S] :
    MvPolynomial.map (algebraMap R S) f ∈ nonZeroDivisors (MvPolynomial σ S) := by
  apply finitePolynomial_regular_of_unit_coefficient _ q
  rw [MvPolynomial.coeff_map]
  exact IsLocalization.Away.algebraMap_isUnit (f.coeff q)

theorem finitePolynomial_localized_coefficient_universal_regular [Finite σ]
    (f : MvPolynomial σ R) (q : σ →₀ ℕ) [Algebra R S]
    [IsLocalization.Away (f.coeff q) S] (c : S →+* T) :
    MvPolynomial.map (c.comp (algebraMap R S)) f ∈
      nonZeroDivisors (MvPolynomial σ T) := by
  apply finitePolynomial_regular_of_unit_coefficient _ q
  rw [MvPolynomial.coeff_map, RingHom.comp_apply]
  exact (IsLocalization.Away.algebraMap_isUnit (S := S) (f.coeff q)).map c

theorem polynomialNonzeroLocus_local_coefficient (f : MvPolynomial σ R)
    (p : PrimeSpectrum R) (hp : p ∈ polynomialNonzeroLocus f) :
    ∃ q ∈ f.support, f.coeff q ∉ p.asIdeal := by
  have hcover := polynomialNonzeroLocus_finite_basicOpen_cover f
  have : p ∈ ⋃ q ∈ f.support,
      (PrimeSpectrum.basicOpen (f.coeff q) : Set (PrimeSpectrum R)) := by
    rw [← hcover]
    exact hp
  obtain ⟨q, hpq⟩ := Set.mem_iUnion.mp this
  obtain ⟨hq, hpq⟩ := Set.mem_iUnion.mp hpq
  exact ⟨q, hq, hpq⟩

end MixedFujita
