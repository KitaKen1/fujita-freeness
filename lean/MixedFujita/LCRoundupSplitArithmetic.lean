/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCBoundaryRoundup

/-! lc係数のroundup正部分の有効性と非負係数での零判定。 See reports/check-244-lc-critical-cut-roundup-kernel.json for the verified scope. Actual lc critical Cartier cuts and effective exceptional roundup parts are constructed. An original projective effective lc non-klt pair yields an internal smooth projective model, nonempty cut, coherent embedded kernel and usual-KV-based H1 vanishing and quotient section lifting. Usual KV and cut-generator existence remain unproved; the kernel is not identified with a reduced lc-center ideal; klt BPF and full F1/F2 remain incomplete. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

/-- The correction at a coefficient-one component cancels the unique possible negative
integer in the negative-boundary roundup of an lc coefficient. -/
theorem lc_roundup_positive_part_nonneg (b : ℤ) (d : ℕ) (hd : 1 ≤ d)
    (hb : b ≤ (d : ℤ)) :
    0 ≤ ⌈-((b : ℝ) / (d : ℝ))⌉ + (if b = (d : ℤ) then 1 else 0) := by
  by_cases he : b = (d : ℤ)
  · have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    norm_num [he, hd0]
  · rw [ite_eq_right he, add_zero, Int.ceil_neg]
    exact negative_floor_normalized_coefficient_nonneg b d hd (lt_of_le_of_ne hb he)


/-- At a nonnegative lc coefficient the positive roundup part is zero,
including the coefficient-one endpoint. -/
theorem lc_roundup_positive_part_eq_zero (b : ℤ) (d : ℕ) (hd : 1 ≤ d)
    (h0 : 0 ≤ b) (hb : b ≤ (d : ℤ)) :
    ⌈-((b : ℝ) / (d : ℝ))⌉ + (if b = (d : ℤ) then 1 else 0) = 0 := by
  by_cases he : b = (d : ℤ)
  · have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    norm_num [he, hd0]
  · rw [ite_eq_right he, add_zero, Int.ceil_neg]
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
    have hlt : (b : ℝ) / (d : ℝ) < 1 :=
      (div_lt_one hdpos).mpr (by exact_mod_cast lt_of_le_of_ne hb he)
    rw [Int.floor_eq_zero_iff.mpr ⟨div_nonneg (by exact_mod_cast h0) hdpos.le, hlt⟩, neg_zero]

end MixedFujita
