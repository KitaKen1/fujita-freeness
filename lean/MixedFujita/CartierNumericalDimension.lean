/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierMixedIntersection
public import MixedFujita.AmpleCartierEulerDegree
public import Mathlib.Data.Finset.Lattice.Fold

/-! 元の通常混合交点数による数値次元の最大値定義と最大元証明。 See reports/check-229-original-numerical-dimension-partial-dictionary.json for the verified scope. Intermediate Iitaka dimension equality, general KV and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Original mixed powers are the usual INTEGER top intersection
D^k times J^(n-k), with the actual dimension/arity equality proved. -/
noncomputable def cartierMixedPowerIntersection
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n)
    (D J : CartierDivisor X) (k : Fin (n + 1)) : ℤ :=
  cartierMixedIntersection K (List.replicate k.val D ++ List.replicate (n - k.val) J)
    (by simpa only [List.length_append, List.length_replicate,
      Nat.add_sub_of_le (Nat.le_of_lt_succ k.isLt)] using hdim)


/-- The manuscript numerical dimension is the MAXIMUM of the exponents
with positive ORIGINAL ordinary mixed power intersection. The next theorem
proves its exact greatest-element meaning when J is ample; no Iitaka or
growth dimension is used in this definition. -/
noncomputable def cartierNumericalDimension
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (D J : CartierDivisor X) : ℕ :=
  ((Finset.univ : Finset (Fin (n + 1))).filter fun k =>
    0 < cartierMixedPowerIntersection K n hdim D J k).sup Fin.val


/-- The zeroth mixed power is literally the usual ample self-intersection. -/
theorem cartierMixedPowerIntersection_zero
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (D J : CartierDivisor X) :
    cartierMixedPowerIntersection K n hdim D J ⟨0, Nat.zero_lt_succ n⟩ =
      cartierMixedIntersection K (List.replicate n J) (by simpa using hdim) := by
  simp only [cartierMixedPowerIntersection, List.replicate_zero, List.nil_append, Nat.sub_zero]


/-- The top mixed power is literally the original self-intersection D^n. -/
theorem cartierMixedPowerIntersection_top
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (D J : CartierDivisor X) :
    cartierMixedPowerIntersection K n hdim D J ⟨n, Nat.lt_succ_self n⟩ =
      cartierMixedIntersection K (List.replicate n D) (by simpa using hdim) := by
  simp only [cartierMixedPowerIntersection, Nat.sub_self, List.replicate_zero, List.append_nil]


/-- The original maximum of positive mixed powers never exceeds the
ordinary dimension of the source. -/
theorem cartierNumericalDimension_le_dim
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (D J : CartierDivisor X) :
    cartierNumericalDimension K n hdim D J ≤ n := by
  apply Finset.sup_le
  intro k hk
  exact Nat.le_of_lt_succ k.isLt


/-- This is exactly the manuscript MAXIMUM, rather than a growth-based
replacement: it belongs to and bounds the set of positive ordinary mixed powers. -/
theorem cartierNumericalDimension_isGreatest
    (K : Type u) [Field K] [Infinite K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (D J : CartierDivisor X) (hJ : CartierIsAmpleProj K J) :
    IsGreatest {k : ℕ | ∃ hk : k < n + 1,
      0 < cartierMixedPowerIntersection K n hdim D J ⟨k, hk⟩}
      (cartierNumericalDimension K n hdim D J) := by
  let S : Finset (Fin (n + 1)) := Finset.univ.filter fun k =>
    0 < cartierMixedPowerIntersection K n hdim D J k
  have hzero : (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [cartierMixedPowerIntersection_zero]
    exact proper_ample_cartierMixedEuler_diagonal_positive K n hdim hn J hJ 0
  obtain ⟨k, hk, heq⟩ := Finset.exists_mem_eq_sup S ⟨_, hzero⟩ Fin.val
  constructor
  · change ∃ hk : S.sup Fin.val < n + 1,
      0 < cartierMixedPowerIntersection K n hdim D J ⟨S.sup Fin.val, hk⟩
    rw [heq]
    exact ⟨k.isLt, (Finset.mem_filter.mp hk).2⟩
  · intro k hk
    obtain ⟨hk, hpos⟩ := hk
    exact Finset.le_sup (f := Fin.val) (show (⟨k, hk⟩ : Fin (n + 1)) ∈ S from
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos⟩)


/-- A positive ORIGINAL top self-intersection forces the original
maximum of positive mixed powers to be the ordinary source dimension. -/
theorem cartierNumericalDimension_eq_dim_of_top_positive
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (D J : CartierDivisor X)
    (hpos : 0 < cartierMixedIntersection K (List.replicate n D) (by simpa using hdim)) :
    cartierNumericalDimension K n hdim D J = n := by
  apply le_antisymm (cartierNumericalDimension_le_dim K n hdim D J)
  have hmem : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) ∈
      ((Finset.univ : Finset (Fin (n + 1))).filter fun k =>
        0 < cartierMixedPowerIntersection K n hdim D J k) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      cartierMixedPowerIntersection_top]
    exact hpos
  exact Finset.le_sup (f := Fin.val) hmem

end MixedFujita
