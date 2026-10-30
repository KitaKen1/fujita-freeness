/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.NefSemiampleMixedEulerNonnegative
public import MixedFujita.AmpleCartierEulerDegree
public import MixedFujita.SemiampleMorseNonvanishing

/-! 元nef1本の混合非負性によるMorse係数更新非消滅。 See reports/check-240-weak-morse-integer-descent-nef-add-ample.json for the verified scope. Original NefAddAmpleStatement, weak algebraic Morse nonvanishing, klt and Kodaira perturbation are proved. Big plus nef is proved here with an original ample divisor on a normal positive-dimensional source; unrestricted proper BigAddNefStatement is not asserted. General KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

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


/-- The weak Morse inequality needed for one coefficient-descent step
follows from ONE nef mixed nonnegativity and the positive ample diagonal. -/
theorem proper_nef_ample_sum_morse_step_inequality
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = (n + 1 : ℕ))
    (N A : CartierDivisor X) (hN : CartierIsNef K N)
    (hB : CartierIsAmpleProj K (N + A)) :
    (n + 1 : ℤ) * cartierMixedEulerDifference K
      (A :: List.replicate n ((n + 2) • (N + A))) 0 <
        cartierMixedEulerDifference K (List.replicate (n + 1) ((n + 2) • (N + A))) 0 := by
  let B := N + A
  have hnn := proper_nef_semiample_cartierMixedEuler_nonneg K n X hdim.le ⟨B, hB⟩ N hN
    (List.replicate n B) (List.length_replicate ..) (by
      intro D hD
      have he : D = B := List.eq_of_mem_replicate hD
      subst D
      exact cartierIsAmpleProj_exists_globallyGenerated_multiple B hB) 0
  have hadd := proper_cartierMixedEulerDifference_top_add_first K (n + 1) hdim.le
    (List.replicate n B) (by simp) N A 0
  change cartierMixedEulerDifference K (B :: List.replicate n B) 0 = _ at hadd
  rw [← List.replicate_succ] at hadd
  have hcmp : cartierMixedEulerDifference K (A :: List.replicate n B) 0 ≤
      cartierMixedEulerDifference K (List.replicate (n + 1) B) 0 := by omega
  have hpos := proper_ample_cartierMixedEuler_diagonal_positive K (n + 1) hdim (by omega) B hB 0
  have htail : cartierMixedEulerDifference K (A :: List.replicate n ((n + 2) • B)) 0 =
      (n + 2 : ℤ) ^ n * cartierMixedEulerDifference K (A :: List.replicate n B) 0 := by
    have h := proper_cartierMixedEulerDifference_top_nsmul_prefix K (n + 1) hdim.le
      (List.replicate n B) [A] (by simp) 0 (n + 2)
    rw [cartierMixedEulerDifference_perm K
      (List.perm_append_comm :
        ((List.replicate n B).map (fun F => (n + 2) • F) ++ [A]).Perm
          ([A] ++ (List.replicate n B).map (fun F => (n + 2) • F))) 0] at h
    rw [cartierMixedEulerDifference_perm K
      (List.perm_append_comm : (List.replicate n B ++ [A]).Perm ([A] ++ List.replicate n B)) 0] at h
    simpa only [List.map_replicate, List.singleton_append, List.length_replicate,
      Nat.cast_add, Nat.cast_ofNat] using h
  change (n + 1 : ℤ) * cartierMixedEulerDifference K
    (A :: List.replicate n ((n + 2) • B)) 0 < _
  rw [htail, proper_cartierMixedEulerDifference_diagonal_nsmul K (n + 1) hdim.le B 0 (n + 2)]
  have hs : (n + 1 : ℤ) * cartierMixedEulerDifference K (A :: List.replicate n B) 0 <
      (n + 2 : ℤ) * cartierMixedEulerDifference K (List.replicate (n + 1) B) 0 := by
    have h := mul_le_mul_of_nonneg_left hcmp (show (0 : ℤ) ≤ n + 1 by positivity)
    nlinarith only [h, hpos]
  have h := mul_lt_mul_of_pos_left hs (show (0 : ℤ) < (n + 2 : ℤ) ^ n by positivity)
  push_cast
  rw [pow_succ]
  convert h using 1 <;> ring


/-- One coefficient update has an actual nonzero positive-multiple section.
It uses neither lower-dimensional ampleness nor a nef-plus-ample theorem. -/
theorem proper_nef_ample_sum_step_exists_nonzero
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = (n + 1 : ℕ))
    (N A : CartierDivisor X) (hN : CartierIsNef K N) (hA : CartierIsAmpleProj K A)
    (hB : CartierIsAmpleProj K (N + A)) :
    ∃ m : ℕ, 0 < m ∧
      ∃ s : Γ((m • ((n + 2) • N + (n + 1) • A)).sheaf, ⊤), s ≠ 0 := by
  have h := proper_ample_sub_semiample_exists_nonzero_of_mixed_inequality K n hdim.le
    ((n + 2) • (N + A)) A (cartierIsAmpleProj_nsmul hB (by omega))
    (cartierIsAmpleProj_exists_globallyGenerated_multiple A hA)
    (proper_nef_ample_sum_morse_step_inequality K n hdim N A hN hB)
  have he : (n + 2) • (N + A) - A = (n + 2) • N + (n + 1) • A := by module
  rw [he] at h
  exact h

end MixedFujita
