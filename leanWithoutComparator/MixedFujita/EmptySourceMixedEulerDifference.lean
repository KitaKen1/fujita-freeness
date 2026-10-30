/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CoherentMixedEulerDifference
public import MixedFujita.CartierPulledCoherentTwist

/-! 空の実proper源での連接混合Euler差分消滅。 See reports/check-231-semiample-numerical-iitaka-dictionary.json for the verified scope. The full original semiample numerical/Iitaka dictionary is proved in the declared scope; general nef positivity, KV, BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true


/-- Mixed coefficients on an actually empty source vanish, with no
geometric or numerical vanishing premise supplied. -/
theorem cartierPulledModuleMixedEulerDifference_empty_source
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsEmpty Y]
    [Y.Over (Spec (CommRingCat.of K))] (p : Y ⟶ X) (M : Y.Modules) [M.IsCoherent]
    (D : List (CartierDivisor X)) (E : CartierDivisor X) :
    cartierPulledModuleMixedEulerDifference K p M D E = 0 := by
  induction D generalizing E with
  | nil =>
    let : ((cartierPullbackTwistFunctor E p).obj M).IsCoherent := cartierPulledTensor_isCoherent E p M
    let : ((cartierPullbackTwistFunctor E p).obj M).IsQuasicoherent :=
      Scheme.Modules.IsCoherent.isQuasicoherent
    exact Scheme.Modules.eulerChar_eq_zero_of_isEmpty _ _
  | cons H D ih =>
    change cartierPulledModuleMixedEulerDifference K p M D (E + H) -
      cartierPulledModuleMixedEulerDifference K p M D E = 0
    rw [ih, ih, sub_self]

end MixedFujita
