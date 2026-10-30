/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.IntegerCoefficientDescent
public import MixedFujita.AmpleCartierAddition
public import MixedFujita.NefAmpleLowerDimensionNonvanishing
public import MixedFujita.NefAmpleMorseCoefficientStep
public import MixedFujita.SteinAmpleLinearComparison

/-! 有限整数係数降下による下の次元からの元nef＋ample。 See reports/check-240-weak-morse-integer-descent-nef-add-ample.json for the verified scope. Original NefAddAmpleStatement, weak algebraic Morse nonvanishing, klt and Kodaira perturbation are proved. Big plus nef is proved here with an original ample divisor on a normal positive-dimensional source; unrestricted proper BigAddNefStatement is not asserted. General KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] MvPolynomial.gradedAlgebra


/-- Explicit integer coefficient descent proves original nef-plus-ample
ampleness from the same theorem only in strictly smaller dimensions. -/
theorem nef_add_ample_isAmpleProj_of_lower_dimension_by_integer_descent
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = (n + 1 : ℕ))
    (hIH : ∀ (Z : Scheme.{u}) [IsIntegral Z] [Z.Over (Spec (CommRingCat.of K))]
      [IsProper (Z ↘ Spec (CommRingCat.of K))], topologicalKrullDim Z ≤ n →
        ∀ (P B : CartierDivisor Z), CartierIsNef K P → CartierIsAmpleProj K B →
          CartierIsAmpleProj K (P + B))
    (N A : CartierDivisor X) (hN : CartierIsNef K N) (hA : CartierIsAmpleProj K A) :
    CartierIsAmpleProj K (N + A) := by
  obtain ⟨k₀, hk₀⟩ := cartierIsAmpleProj_eventually_twist_veryAmple hA N
  let k := max k₀ 1
  have hk : 0 < k := by omega
  have hseq : ∀ s : ℕ, CartierIsAmpleProj K
      ((n + 2) ^ s • N + (k * (n + 1) ^ s) • A) := by
    intro s
    induction s with
    | zero =>
      simpa only [pow_zero, one_smul, mul_one] using
        cartierIsAmpleProj_of_veryAmple (hk₀ k (by omega))
    | succ s ih =>
      let P := (n + 2) ^ s • N
      let B := (k * (n + 1) ^ s) • A
      have hP : CartierIsNef K P := cartierIsNef_nsmul hN _
      have hB : CartierIsAmpleProj K B := cartierIsAmpleProj_nsmul hA
        (show 0 < k * (n + 1) ^ s from Nat.mul_pos hk (pow_pos (by omega) s))
      obtain ⟨m, hm, t, ht⟩ := proper_nef_ample_sum_step_exists_nonzero K n hdim P B hP hB ih
      have happ : CartierIsAmpleProj K ((n + 2) • P + (n + 1) • B) :=
        nef_add_ample_isAmpleProj_of_lower_dimension_and_nonzero_section K n hdim.le hIH
          ((n + 2) • P) ((n + 1) • B) (cartierIsNef_nsmul hP _)
          (cartierIsAmpleProj_nsmul hB (by omega)) m hm t ht
      have he : (n + 2) • P + (n + 1) • B =
          (n + 2) ^ (s + 1) • N + (k * (n + 1) ^ (s + 1)) • A := by
        dsimp [P, B]
        simp only [smul_smul, pow_succ]
        congr 2 <;> ring
      exact he ▸ happ
  let s := (n + 1) * k
  let p := (n + 2) ^ s
  let q := k * (n + 1) ^ s
  have hqp : q ≤ p := integer_descent_coefficients_eventually_ordered (n + 1) k (by omega)
  have hp : 0 < p := by dsimp [p]; positivity
  have htotal : CartierIsAmpleProj K (p • (N + A)) := by
    by_cases heq : q = p
    · have he : p • N + q • A = p • (N + A) := by rw [heq, smul_add]
      exact he ▸ hseq s
    · have hdiff : 0 < p - q := by omega
      have h := cartierIsAmpleProj_add_of_isAmpleProj K _ _ (hseq s)
        (cartierIsAmpleProj_nsmul hA hdiff)
      have he : (p • N + q • A) + (p - q) • A = p • (N + A) := by
        rw [smul_add, add_assoc, ← add_nsmul, Nat.add_sub_of_le hqp]
      exact he ▸ h
  exact cartierIsAmpleProj_of_positive_nsmul hp htotal

end MixedFujita
