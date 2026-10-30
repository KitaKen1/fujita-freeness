/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ClosedRationalPoints
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Roots

/-!
Very general points over an uncountable field (§5.1, step 9). Countably many nonzero polynomials
over an uncountable field have a common non-root: in the last variable each polynomial has a
nonzero leading coefficient in the remaining variables, which by induction is nonzero at some
point y; the specialized polynomials in the last variable have finitely many roots each, so
countably many in total, and a value t outside them gives the point (t, y). For a finitely
generated K-domain A over an uncountable algebraically closed field, countably many nonzero
elements a_k have a common non-zero K-point: by Noether normalization A is integral over a
polynomial ring P; each a_k divides some nonzero c_k in P (remove the powers of X from a monic
relation and take the constant term); choosing y with c_k(y) ≠ 0 for all k and a maximal ideal Q
of A over the maximal ideal of y, no a_k lies in Q, and evaluation at Q is a K-point where every
a_k is nonzero. On an affine variety, a point outside countably many proper closed subsets.
-/

@[expose] public section

namespace MixedFujita

open Polynomial

/-- Countably many nonzero polynomials over an uncountable field have a common non-root. -/
theorem exists_eval_ne_zero_of_countable {K : Type*} [Field K] [Uncountable K] {ι : Type*}
    [Countable ι] : ∀ {n : ℕ} (f : ι → MvPolynomial (Fin n) K), (∀ k, f k ≠ 0) →
      ∃ x : Fin n → K, ∀ k, MvPolynomial.eval x (f k) ≠ 0
  | 0, f, hf => by
    refine ⟨Fin.elim0, fun k => ?_⟩
    have hk := MvPolynomial.eq_C_of_isEmpty (f k)
    rw [hk, MvPolynomial.eval_C]
    intro h0
    apply hf k
    rw [hk, h0, map_zero]
  | n + 1, f, hf => by
    set p : ι → Polynomial (MvPolynomial (Fin n) K) := fun k => MvPolynomial.finSuccEquiv K n (f k)
      with hp
    have hp0 : ∀ k, p k ≠ 0 := fun k h =>
      hf k ((MvPolynomial.finSuccEquiv K n).injective (by rw [map_zero]; exact h))
    obtain ⟨y, hy⟩ := exists_eval_ne_zero_of_countable (fun k => (p k).leadingCoeff)
      (fun k => leadingCoeff_ne_zero.mpr (hp0 k))
    set q : ι → Polynomial K := fun k => (p k).map (MvPolynomial.eval y) with hq
    have hq0 : ∀ k, q k ≠ 0 := by
      intro k h
      have hc := congrArg (fun r : Polynomial K => r.coeff (p k).natDegree) h
      simp only [hq, coeff_map, coeff_zero] at hc
      exact hy k hc
    have hbad : (⋃ k, {t : K | (q k).IsRoot t}).Countable :=
      Set.countable_iUnion fun k => (finite_setOfPred_isRoot (hq0 k)).countable
    obtain ⟨t, ht⟩ : ∃ t, t ∉ ⋃ k, {t : K | (q k).IsRoot t} := by
      by_contra h
      push Not at h
      apply Set.not_countable_univ (α := K)
      exact hbad.mono fun t _ => h t
    refine ⟨Fin.cons t y, fun k hk => ?_⟩
    rw [MvPolynomial.eval_eq_eval_mv_eval'] at hk
    exact ht (Set.mem_iUnion.mpr ⟨k, hk⟩)

/-- A nonzero integral element of a domain divides the image of a nonzero element of the base. -/
theorem exists_dvd_algebraMap_of_isIntegral {R S : Type*} [CommRing R] [CommRing S] [IsDomain S]
    [Nontrivial R] [Algebra R S] {a : S} (ha : a ≠ 0) (hint : IsIntegral R a) :
    ∃ c : R, c ≠ 0 ∧ ∃ b : S, algebraMap R S c = a * b := by
  obtain ⟨p, hmonic, heval⟩ := hint
  have hp0 : p ≠ 0 := hmonic.ne_zero
  have hX : (X - C (0 : R) : R[X]) = X := by simp
  have hpq := pow_mul_divByMonic_rootMultiplicity_eq p 0
  have hq0 := eval_divByMonic_pow_rootMultiplicity_ne_zero 0 hp0
  rw [hX] at hpq hq0
  set q := p /ₘ X ^ p.rootMultiplicity 0
  have haq : aeval a q = 0 := by
    have h : aeval a p = 0 := by rwa [aeval_def]
    rw [← hpq, map_mul, map_pow, aeval_X] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ ha)
  refine ⟨q.coeff 0, by rwa [coeff_zero_eq_eval_zero], -(aeval a (divX q)), ?_⟩
  have hsplit := X_mul_divX_add q
  have h := congrArg (aeval a) hsplit
  rw [haq, map_add, map_mul, aeval_X, aeval_C] at h
  linear_combination h

/-- Very general points on an affine variety: countably many nonzero elements of a finitely
generated domain over an uncountable algebraically closed field are all nonzero at some K-point. -/
theorem exists_algHom_ne_zero_of_countable {K A : Type*} [Field K] [IsAlgClosed K] [Uncountable K]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] {ι : Type*} [Countable ι]
    (a : ι → A) (ha : ∀ k, a k ≠ 0) : ∃ φ : A →ₐ[K] K, ∀ k, φ (a k) ≠ 0 := by
  obtain ⟨s, g, hginj, hgint⟩ := exists_integral_inj_algHom_of_fg K A
  let _ : Algebra (MvPolynomial (Fin s) K) A := g.toRingHom.toAlgebra
  have hint : Algebra.IsIntegral (MvPolynomial (Fin s) K) A := ⟨hgint⟩
  choose c hc0 b hb using fun k =>
    exists_dvd_algebraMap_of_isIntegral (R := MvPolynomial (Fin s) K) (ha k)
      (Algebra.IsIntegral.isIntegral (a k))
  obtain ⟨y, hy⟩ := exists_eval_ne_zero_of_countable c hc0
  set m := RingHom.ker (MvPolynomial.eval y : MvPolynomial (Fin s) K →+* K) with hm
  have hmmax : m.IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ fun x => ⟨MvPolynomial.C x, by simp⟩
  have hker : (⊥ : Ideal A).under (MvPolynomial (Fin s) K) ≤ m := by
    intro x hx
    rw [Ideal.under_def, Ideal.mem_comap, Ideal.mem_bot] at hx
    have hx0 : x = 0 := hginj (by rw [map_zero]; exact hx)
    rw [hx0]
    exact m.zero_mem
  obtain ⟨Q, -, hQprime, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral m ⊥ hker
  have hQmax : Q.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := MvPolynomial (Fin s) K) Q
      (by rw [hQ]; exact hmmax)
  have := hQmax
  refine ⟨closedPointEvaluation (K := K) Q, fun k => ?_⟩
  rw [Ne, closedPointEvaluation_eq_zero_iff]
  intro hak
  have h1 : algebraMap (MvPolynomial (Fin s) K) A (c k) ∈ Q := by
    rw [hb k]
    exact Q.mul_mem_right _ hak
  have h2 : c k ∈ Q.under (MvPolynomial (Fin s) K) := h1
  rw [hQ, hm, RingHom.mem_ker] at h2
  exact hy k h2

/-- Very general closed points: countably many nonzero ideals of a finitely generated domain over an
uncountable algebraically closed field, that is countably many proper closed subsets of an affine
variety, all avoid some maximal ideal. -/
theorem exists_isMaximal_not_le_of_countable {K A : Type*} [Field K] [IsAlgClosed K]
    [Uncountable K] [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] {ι : Type*}
    [Countable ι] (I : ι → Ideal A) (hI : ∀ k, I k ≠ ⊥) :
    ∃ Q : Ideal A, Q.IsMaximal ∧ ∀ k, ¬ I k ≤ Q := by
  choose a ha ha0 using fun k => Submodule.exists_mem_ne_zero_of_ne_bot (hI k)
  obtain ⟨φ, hφ⟩ := exists_algHom_ne_zero_of_countable (K := K) a ha0
  refine ⟨RingHom.ker φ.toRingHom,
    RingHom.ker_isMaximal_of_surjective _ fun c => ⟨algebraMap K A c, by simp⟩, fun k hk => ?_⟩
  exact hφ k (RingHom.mem_ker.mp (hk (ha k)))

end MixedFujita
