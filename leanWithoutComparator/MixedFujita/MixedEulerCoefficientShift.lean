/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CoherentMixedEulerDifference
public import MixedFujita.MixedForwardDifferenceLinearity

/-! 実Cartier差分と係数捻りの同定・平行移動。 See reports/check-221-general-mixed-euler-nilpotence.json for the verified scope. Ordinary mixed-intersection identification and ample-pullback positivity remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Mixed forward differences commute with translation of the original function. -/
theorem mixedForwardDifference_comp_add {A : Type*} [AddCommMonoid A]
    (D : List A) (f : A → ℤ) (H E : A) :
    mixedForwardDifference D (fun F => f (F + H)) E =
      mixedForwardDifference D f (E + H) := by
  induction D generalizing E with
  | nil => rfl
  | cons J D ih =>
    rw [mixedForwardDifference_cons, mixedForwardDifference_cons, ih, ih]
    rw [add_right_comm E J H]


/-- A shift of the original divisor is exactly tensoring the coefficient
with its actual pulled Cartier sheaf; all tensor comparisons are actual isos. -/
theorem cartierPulledModuleMixedEulerDifference_shift_eq_twist
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))]
    (p : Y ⟶ X) (M : Y.Modules) (D : List (CartierDivisor X)) (H E : CartierDivisor X) :
    cartierPulledModuleMixedEulerDifference K p M D (E + H) =
      cartierPulledModuleMixedEulerDifference K p ((cartierPullbackTwistFunctor H p).obj M) D E := by
  have heq : (fun F : CartierDivisor X => Scheme.Modules.eulerChar
      (Y ↘ Spec (CommRingCat.of K))
      ((cartierPullbackTwistFunctor F p).obj ((cartierPullbackTwistFunctor H p).obj M))) =
      fun F : CartierDivisor X => Scheme.Modules.eulerChar (Y ↘ Spec (CommRingCat.of K))
        ((cartierPullbackTwistFunctor (F + H) p).obj M) := by
    funext F
    exact moduleEulerChar_congr K
      ((associator ((Scheme.Modules.pullback p).obj F.sheaf)
        ((Scheme.Modules.pullback p).obj H.sheaf) M).symm ≪≫
          tensorIso ((cartierPullbackTensorIso F p H.sheaf).symm ≪≫
            (Scheme.Modules.pullback p).mapIso (cartierTensorSheafIso F H)) (Iso.refl M))
  unfold cartierPulledModuleMixedEulerDifference
  rw [heq]
  exact (mixedForwardDifference_comp_add D (fun F : CartierDivisor X =>
    Scheme.Modules.eulerChar (Y ↘ Spec (CommRingCat.of K))
      ((cartierPullbackTwistFunctor F p).obj M)) H E).symm


/-- One additional Cartier difference is the difference of actual coherent
coefficient twists, independently of finiteness or a cohomology cutoff. -/
theorem cartierPulledModuleMixedEulerDifference_cons_eq_coefficient_difference
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))]
    (p : Y ⟶ X) (M : Y.Modules) (D : List (CartierDivisor X)) (H E : CartierDivisor X) :
    cartierPulledModuleMixedEulerDifference K p M (H :: D) E =
      cartierPulledModuleMixedEulerDifference K p ((cartierPullbackTwistFunctor H p).obj M) D E -
        cartierPulledModuleMixedEulerDifference K p M D E := by
  change cartierPulledModuleMixedEulerDifference K p M D (E + H) -
      cartierPulledModuleMixedEulerDifference K p M D E = _
  rw [cartierPulledModuleMixedEulerDifference_shift_eq_twist]

end MixedFujita
