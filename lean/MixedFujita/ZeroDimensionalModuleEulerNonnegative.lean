/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ActualModuleEulerCharacteristic

/-! 実零次元Euler標数の非負性と切断帰納の基点。 See reports/check-228-semiample-mixed-intersection-nonnegative.json for the verified scope. Strict ample-pullback positivity and the original numerical-dimension dictionary remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- In dimension zero the ACTUAL full Euler characteristic of every module
is the nonnegative rank of its actual degree-zero cohomology. -/
theorem zeroDimensional_moduleEulerChar_nonneg
    (K : Type u) [Field K] {Y : Scheme.{u}}
    [Y.Over (Spec (CommRingCat.of K))] [NoetherianSpace Y]
    (hdim : topologicalKrullDim Y ≤ 0) (M : Y.Modules) :
    0 ≤ Scheme.Modules.eulerChar (Y ↘ Spec (CommRingCat.of K)) M := by
  rw [moduleEulerChar_eq_eulerCharBelow_of_dim_lt K M 1
    (hdim.trans_lt (by norm_num : (0 : WithBot ℕ∞) < (1 : ℕ)))]
  simp only [Scheme.Modules.eulerCharBelow_succ, Scheme.Modules.eulerCharBelow_zero,
    pow_zero, one_mul, zero_add]
  positivity

end MixedFujita
