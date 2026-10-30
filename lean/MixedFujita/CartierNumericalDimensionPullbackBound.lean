/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierNumericalDimensionInvariance
public import MixedFujita.MixedPullbackIntersectionVanishing

/-! 引き戻しと正整数倍の元数値次元の実基底次元による上界。 See reports/check-229-original-numerical-dimension-partial-dictionary.json for the verified scope. Intermediate Iitaka dimension equality, general KV and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- The manuscript numerical dimension of a pulled line bundle is bounded
by the BASE dimension, using actual original mixed-intersection vanishing. -/
theorem cartierNumericalDimension_le_base_dimension_of_pullback
    (K : Type u) [Field K] {B Y : Scheme.{u}} [IsIntegral B] [IsIntegral Y]
    [B.Over (Spec (CommRingCat.of K))] [IsProper (B ↘ Spec (CommRingCat.of K))]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdimY : topologicalKrullDim Y = n) (d : ℕ) (hdimB : topologicalKrullDim B ≤ d)
    (p : Y ⟶ B) (H : CartierDivisor B) (D J : CartierDivisor Y)
    (a : (Scheme.Modules.pullback p).obj H.sheaf ≅ D.sheaf) :
    cartierNumericalDimension K n hdimY D J ≤ d := by
  apply Finset.sup_le
  intro k hk
  have hpos := (Finset.mem_filter.mp hk).2
  by_contra hkd
  have hz : cartierMixedPowerIntersection K n hdimY D J k = 0 := by
    exact proper_cartierMixedIntersection_pullback_power_vanish K d hdimB p H D a k.val
      (by omega) (List.replicate (n - k.val) J)
      (by simpa only [List.length_append, List.length_replicate,
        Nat.add_sub_of_le (Nat.le_of_lt_succ k.isLt)] using hdimY)
  rw [hz] at hpos
  exact lt_irrefl 0 hpos


/-- The same ordinary numerical bound applies when a POSITIVE MULTIPLE
of D is the actual pulled line bundle, as in a semiample contraction. -/
theorem cartierNumericalDimension_le_base_dimension_of_multiple_pullback
    (K : Type u) [Field K] {B Y : Scheme.{u}} [IsIntegral B] [IsIntegral Y]
    [B.Over (Spec (CommRingCat.of K))] [IsProper (B ↘ Spec (CommRingCat.of K))]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdimY : topologicalKrullDim Y = n) (d : ℕ) (hdimB : topologicalKrullDim B ≤ d)
    (p : Y ⟶ B) (H : CartierDivisor B) (D J : CartierDivisor Y)
    (q : ℕ) (hq : 0 < q) (a : (Scheme.Modules.pullback p).obj H.sheaf ≅ (q • D).sheaf) :
    cartierNumericalDimension K n hdimY D J ≤ d := by
  have h := cartierNumericalDimension_le_base_dimension_of_pullback
    K n hdimY d hdimB p H (q • D) J a
  rwa [cartierNumericalDimension_nsmul K n hdimY D J q hq] at h

end MixedFujita
