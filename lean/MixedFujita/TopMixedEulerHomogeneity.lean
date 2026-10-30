/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.TopDimensionalMixedEuler
public import Mathlib.Tactic.Ring

/-! 最高次混合Euler係数の全因子自然数斉次性と対角のn乗則。 See reports/check-222-euler-newton-hilbert-normalization.json for the verified scope. General multivariate intersection identification and mixed ample-pullback positivity remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open Polynomial Finset

/-- Ordinary integer homogeneity of any specified top mixed Euler factor. -/
theorem proper_cartierMixedEulerDifference_top_nsmul_factor
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X ≤ n)
    (A B : List (CartierDivisor X)) (hlen : A.length + B.length + 1 = n)
    (H E : CartierDivisor X) (q : ℕ) :
    cartierMixedEulerDifference K (A ++ (q • H) :: B) E =
      (q : ℤ) * cartierMixedEulerDifference K (A ++ H :: B) E := by
  induction q with
  | zero =>
    simp only [zero_nsmul, Nat.cast_zero, zero_mul]
    have h := proper_cartierMixedEulerDifference_top_add_factor K n hdim A B hlen 0 0 E
    simp only [zero_add] at h
    omega
  | succ q ih =>
    rw [succ_nsmul, proper_cartierMixedEulerDifference_top_add_factor K n hdim A B hlen, ih]
    push_cast
    ring


/-- Simultaneous scaling of a prefix of the top mixed factors, proved
from actual factor additivity and permutation invariance. -/
theorem proper_cartierMixedEulerDifference_top_nsmul_prefix
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X ≤ n)
    (A B : List (CartierDivisor X)) (hlen : A.length + B.length = n)
    (E : CartierDivisor X) (q : ℕ) :
    cartierMixedEulerDifference K ((A.map fun F => q • F) ++ B) E =
      (q : ℤ) ^ A.length * cartierMixedEulerDifference K (A ++ B) E := by
  induction A generalizing B with
  | nil => simp only [List.map_nil, List.nil_append, List.length_nil, pow_zero, one_mul]
  | cons H A ih =>
    have perm (C : List (CartierDivisor X)) : (C ++ H :: B).Perm (H :: (C ++ B)) :=
      List.perm_append_comm.trans (List.perm_append_comm.cons H)
    have hscale := proper_cartierMixedEulerDifference_top_nsmul_factor K n hdim []
      ((A.map fun F => q • F) ++ B)
      (by simp only [List.length_nil, List.length_append, List.length_map, List.length_cons] at *; omega)
      H E q
    simp only [List.map_cons, List.cons_append, List.nil_append] at hscale ⊢
    rw [hscale, ← cartierMixedEulerDifference_perm K (perm (A.map fun F => q • F)) E]
    rw [ih (H :: B) (by simp only [List.length_cons] at *; omega)]
    rw [cartierMixedEulerDifference_perm K (perm A) E]
    simp only [List.length_cons, pow_succ]
    ring


/-- The diagonal top coefficient scales by the ordinary n-th power. -/
theorem proper_cartierMixedEulerDifference_diagonal_nsmul
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X ≤ n) (H E : CartierDivisor X) (q : ℕ) :
    cartierMixedEulerDifference K (List.replicate n (q • H)) E =
      (q : ℤ) ^ n * cartierMixedEulerDifference K (List.replicate n H) E := by
  simpa only [List.map_replicate, List.append_nil, List.length_replicate] using
    proper_cartierMixedEulerDifference_top_nsmul_prefix K n hdim (List.replicate n H) []
      (by simp) E q

end MixedFujita
