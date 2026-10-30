/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierGlobalGenerationOperations
public import MixedFujita.CartierNefDefinition
public import MixedFujita.ArbitrarilySmallKltPerturbations

/-!
Projective ampleness supplies actual generating sections of arbitrarily large
divisible multiples. Coordinate sections generate the actual hyperplane
divisor; principal shifts and section powers transfer this to an ample divisor.
Common denominators synchronize an original pair denominator and a cleared
rational ample class. No Serre-vanishing input or supplied generation of large
multiples is needed for this divisible sequence. All sufficiently large
integers, including other residue classes, are not asserted here.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- An arbitrarily large common multiple can also have arbitrarily small reciprocal weight. -/
theorem exists_large_divisible_scaled_denominator (a d N : ℕ) (ha : 1 ≤ a) (hd : 1 ≤ d)
    (ε : ℚ) (hε : 0 < ε) :
    ∃ m : ℕ, 2 ≤ m ∧ a ∣ m ∧ N ≤ m * d ∧ 1 < m * d ∧
      0 < 1 / ((m * d : ℕ) : ℚ) ∧ 1 / ((m * d : ℕ) : ℚ) < ε := by
  obtain ⟨j, hj⟩ := exists_nat_gt (1 / ε)
  let t := j + N + 2
  let m := a * t
  have ht : 2 ≤ t := by omega
  have htm : t ≤ m := by simpa [m] using Nat.mul_le_mul_right t ha
  have hmd : m ≤ m * d := by simpa using Nat.mul_le_mul_left m hd
  have hm : 2 ≤ m := ht.trans htm
  have hN : N ≤ m * d := (by omega : N ≤ t).trans (htm.trans hmd)
  have hmd1 : 1 < m * d := by omega
  have hmdpos : (0 : ℚ) < (m * d : ℕ) := by exact_mod_cast (by omega : 0 < m * d)
  have hlt : 1 / ε < ((m * d : ℕ) : ℚ) := by
    have hjt : (j : ℚ) < t := by
      have hN0 : (0 : ℚ) ≤ N := Nat.cast_nonneg N
      dsimp [t]
      push_cast
      linarith
    exact (hj.trans hjt).trans_le (by exact_mod_cast htm.trans hmd)
  refine ⟨m, hm, ⟨t, rfl⟩, hN, hmd1, div_pos zero_lt_one hmdpos, ?_⟩
  apply (div_lt_iff₀ hmdpos).mpr
  simpa only [mul_comm] using (div_lt_iff₀ hε).mp hlt

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]

/-- The actual projective coordinate sections generate the actual hyperplane divisor. -/
theorem projectiveHyperplaneCartier_globallyGenerated {v : ℕ}
    (e : X ⟶ polynomialProjectiveScheme v K) (g : MvPolynomial (Fin v) K)
    (hg : g.IsHomogeneous 1) (hggen : g ∉ (e (genericPoint X)).asHomogeneousIdeal) :
    CartierIsGloballyGenerated (projectiveHyperplaneCartier e g hg hggen) := by
  obtain ⟨k₀, hk₀⟩ := polynomialProjective_exists_coordinate_chart v K (e (genericPoint X))
  let j₀ : {k : Fin v // Nonempty (projectivePullbackCoordinateOpen e k)} :=
    ⟨k₀, ⟨⟨genericPoint X, hk₀⟩⟩⟩
  have h : CartierIsGloballyGenerated (1 • projectiveHyperplaneCartier e g hg hggen) := by
    intro x
    obtain ⟨k, hk⟩ := polynomialProjective_exists_coordinate_chart v K (e x)
    refine ⟨projectiveFormSection e g hg hggen j₀ 1 (MvPolynomial.X k) (isHomogeneous_X K k), ?_⟩
    exact (mem_cartierSectionNonvanishingOpen_iff_localCoefficient _ _ x _
      (Classical.choose_spec ((1 • projectiveHyperplaneCartier e g hg hggen).exists_isLocalEquationAt x))).mp
        (projectiveFormSection_X_mem_nonvanishingOpen e g hg hggen j₀ x hk)
  simpa only [one_nsmul] using h

/-- A positive globally generated multiple is constructed from projective ampleness. -/
theorem cartierIsAmpleProj_exists_globallyGenerated_multiple (A : CartierDivisor X)
    (hA : CartierIsAmpleProj K A) :
    ∃ p : ℕ, 1 ≤ p ∧ CartierIsGloballyGenerated (p • A) := by
  obtain ⟨p, hp, v, e, _, _, g, hg, hggen, f, h⟩ := hA
  refine ⟨p, hp, ?_⟩
  rw [h]
  exact cartierIsGloballyGenerated_principal_shift _ f
    (projectiveHyperplaneCartier_globallyGenerated e g hg hggen)

/-- All multiples in one actual divisible sequence are globally generated. -/
theorem cartierIsAmpleProj_exists_globallyGenerated_divisible_sequence (A : CartierDivisor X)
    (hA : CartierIsAmpleProj K A) :
    ∃ p : ℕ, 1 ≤ p ∧ ∀ t : ℕ, CartierIsGloballyGenerated ((t * p) • A) := by
  obtain ⟨p, hp, h⟩ := cartierIsAmpleProj_exists_globallyGenerated_multiple A hA
  exact ⟨p, hp, fun t => by simpa only [smul_smul] using cartierIsGloballyGenerated_nsmul _ h t⟩

/-- Actual global generation synchronizes both rational denominators, any size
threshold, and any positive reciprocal margin. -/
theorem cartierIsAmpleProj_exists_common_denominator_global_generation
    (A : CartierDivisor X) (hA : CartierIsAmpleProj K A) (d q N : ℕ)
    (hd : 1 ≤ d) (hq : 1 ≤ q) (ε : ℚ) (hε : 0 < ε) :
    ∃ m r : ℕ, 2 ≤ m ∧ 1 ≤ r ∧ m * d = r * q ∧ N ≤ m * d ∧ 1 < m * d ∧
      0 < 1 / ((m * d : ℕ) : ℚ) ∧ 1 / ((m * d : ℕ) : ℚ) < ε ∧
      CartierIsGloballyGenerated (r • A) := by
  obtain ⟨p, hp, hgen⟩ := cartierIsAmpleProj_exists_globallyGenerated_divisible_sequence A hA
  obtain ⟨m, hm, hdiv, hN, hmd, hpos, hsmall⟩ :=
    exists_large_divisible_scaled_denominator (p * q) d N (by nlinarith) hd ε hε
  obtain ⟨t, ht⟩ := hdiv
  let r := p * t * d
  have htpos : 1 ≤ t := by
    by_contra h
    have htzero : t = 0 := by omega
    have hmzero : m = 0 := by simpa only [htzero, Nat.mul_zero] using ht
    omega
  have hr : 1 ≤ r := by
    simpa only [r, Nat.one_mul] using Nat.mul_le_mul (Nat.mul_le_mul hp htpos) hd
  have heq : m * d = r * q := by rw [ht]; dsimp [r]; ac_rfl
  refine ⟨m, r, hm, hr, heq, hN, hmd, hpos, hsmall, ?_⟩
  simpa only [r, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hgen (t * d)

end MixedFujita
