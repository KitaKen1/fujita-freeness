/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.Data.Int.CharZero

/-!
Closed points of finitely generated `ℤ`-algebras (step 10, R4).

The integers form a Jacobson ring (`isJacobsonRing_int`): a nonzero prime ideal is maximal, and
the intersection of the maximal ideals `(p)` is zero. By Zariski's lemma the residue field of a
finitely generated `ℤ`-algebra at a maximal ideal is a finitely generated abelian group; it has
positive characteristic, since a field integral over `ℤ` would make `ℤ` a field, so it is finite
(`finite_quotient_of_isMaximal`, `finite_residueField_of_isMaximal`). If `n!` is a unit, the
residue characteristic is larger than `n` (`lt_ringChar_quotient_of_isUnit_factorial`). These are
the closed points at which the characteristic-`p` vanishing of check 491 is applied.
-/

@[expose] public section

namespace MixedFujita

/-- **The integers form a Jacobson ring.** -/
instance isJacobsonRing_int : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  apply le_antisymm _ Ideal.le_jacobson
  by_cases hbot : P = ⊥
  · subst hbot
    intro x hx
    rw [Ideal.jacobson, Ideal.mem_sInf] at hx
    obtain ⟨p, hp_ge, hp⟩ := Nat.exists_infinite_primes (x.natAbs + 1)
    have hirr : Irreducible (p : ℤ) := (Nat.prime_iff_prime_int.mp hp).irreducible
    have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hirr
    have hmem := hx ⟨bot_le, hmax⟩
    rw [Ideal.mem_span_singleton] at hmem
    have hdvd : p ∣ x.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr hmem
      simpa using this
    have h0 : x.natAbs = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    rw [Ideal.mem_bot]
    exact Int.natAbs_eq_zero.mp h0
  · have := IsPrime.to_maximal_ideal hbot
    exact (Ideal.jacobson_eq_self_of_isMaximal (H := this)).le

section FiniteType

variable {R : Type*} [CommRing R] (𝔪 : Ideal R) [𝔪.IsMaximal]

/-- The residue characteristic at a maximal ideal of a finitely generated `ℤ`-algebra is positive. -/
theorem ringChar_quotient_ne_zero [Algebra.FiniteType ℤ R] : ringChar (R ⧸ 𝔪) ≠ 0 := by
  let _ := Ideal.Quotient.field 𝔪
  have : Module.Finite ℤ (R ⧸ 𝔪) := finite_of_finite_type_of_isJacobsonRing ℤ (R ⧸ 𝔪)
  intro h0
  have : CharP (R ⧸ 𝔪) 0 := ringChar.of_eq h0
  have : CharZero (R ⧸ 𝔪) := CharP.charP_to_charZero (R ⧸ 𝔪)
  have hinj : Function.Injective (algebraMap ℤ (R ⧸ 𝔪)) := (algebraMap ℤ (R ⧸ 𝔪)).injective_int
  exact Int.not_isField (isField_of_isIntegral_of_isField hinj (Field.toIsField _))

/-- **The residue field of a finitely generated `ℤ`-algebra at a maximal ideal is finite.** -/
theorem finite_quotient_of_isMaximal [Algebra.FiniteType ℤ R] : Finite (R ⧸ 𝔪) := by
  let _ := Ideal.Quotient.field 𝔪
  have : Module.Finite ℤ (R ⧸ 𝔪) := finite_of_finite_type_of_isJacobsonRing ℤ (R ⧸ 𝔪)
  have hchar := ringChar_quotient_ne_zero 𝔪
  apply Module.finite_of_fg_torsion
  intro x
  refine ⟨⟨(ringChar (R ⧸ 𝔪) : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hchar)⟩, ?_⟩
  change ((ringChar (R ⧸ 𝔪) : ℕ) : ℤ) • x = 0
  rw [natCast_zsmul, nsmul_eq_mul, ringChar.Nat.cast_ringChar, zero_mul]

/-- **The residue field at a maximal ideal of a finitely generated `ℤ`-algebra is finite.** -/
theorem finite_residueField_of_isMaximal [Algebra.FiniteType ℤ R] : Finite 𝔪.ResidueField := by
  have := finite_quotient_of_isMaximal 𝔪
  exact Finite.of_surjective _ (Ideal.bijective_algebraMap_quotient_residueField 𝔪).2

/-- **If `n!` is a unit, the residue characteristic exceeds `n`.** -/
theorem lt_ringChar_quotient_of_isUnit_factorial [Algebra.FiniteType ℤ R] (n : ℕ)
    (hn : IsUnit (n.factorial : R)) : n < ringChar (R ⧸ 𝔪) := by
  let _ := Ideal.Quotient.field 𝔪
  have hchar := ringChar_quotient_ne_zero 𝔪
  have hprime : (ringChar (R ⧸ 𝔪)).Prime := by
    have : CharP (R ⧸ 𝔪) (ringChar (R ⧸ 𝔪)) := ringChar.charP _
    exact (CharP.char_is_prime_or_zero (R ⧸ 𝔪) _).resolve_right hchar
  by_contra hle
  push Not at hle
  have hdvd : ringChar (R ⧸ 𝔪) ∣ n.factorial := (Nat.Prime.dvd_factorial hprime).mpr hle
  have hzero : ((n.factorial : ℕ) : R ⧸ 𝔪) = 0 := (ringChar.spec (R ⧸ 𝔪) _).mpr hdvd
  have hunit : IsUnit ((n.factorial : ℕ) : R ⧸ 𝔪) := by
    have := hn.map (Ideal.Quotient.mk 𝔪)
    simpa using this
  rw [hzero] at hunit
  exact not_isUnit_zero hunit

end FiniteType

end MixedFujita
