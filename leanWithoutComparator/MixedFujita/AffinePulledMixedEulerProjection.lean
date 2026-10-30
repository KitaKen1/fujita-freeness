/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierPulledMixedEulerProjection

/-! 実affine写像に沿う連接混合Euler差分の射影公式。 See reports/check-232-nef-semiample-mixed-nonnegative.json for the verified scope. One original nef factor with a semiample tail and numerical-trivial-factor vanishing are proved in the declared scope. General nef-plus-ample ampleness, KV, BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra


/-- The actual mixed Euler projection identity for affine maps, including
finite maps; this does not assume a proper Euler--Leray formula. -/
theorem cartierPulledModuleMixedEulerDifference_affine_pushforward
    (K : Type u) [Field K] {X Y Z : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] [Z.Over (Spec (CommRingCat.of K))]
    [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) (i : Z ⟶ Y) [IsAffineHom i] [i.IsOver (Spec (CommRingCat.of K))]
    (M : Z.Modules) [M.IsCoherent] (D : List (CartierDivisor X)) (E : CartierDivisor X) :
    cartierPulledModuleMixedEulerDifference K p ((Scheme.Modules.pushforward i).obj M) D E =
      cartierPulledModuleMixedEulerDifference K (i ≫ p) M D E := by
  have heq : (fun F : CartierDivisor X => Scheme.Modules.eulerChar
      (Y ↘ Spec (CommRingCat.of K))
        ((cartierPullbackTwistFunctor F p).obj ((Scheme.Modules.pushforward i).obj M))) =
      fun F : CartierDivisor X => Scheme.Modules.eulerChar
        (Z ↘ Spec (CommRingCat.of K)) ((cartierPullbackTwistFunctor F (i ≫ p)).obj M) := by
    funext F
    rw [moduleEulerChar_congr K (cartierPulledProjectionFormulaIso F p i M)]
    let : ((cartierPullbackTwistFunctor F (i ≫ p)).obj M).IsCoherent :=
      cartierPulledTensor_isCoherent F (i ≫ p) M
    let : ((cartierPullbackTwistFunctor F (i ≫ p)).obj M).IsQuasicoherent :=
      Scheme.Modules.IsCoherent.isQuasicoherent
    have h := Scheme.Modules.eulerChar_pushforward (Y ↘ Spec (CommRingCat.of K)) i
      ((cartierPullbackTwistFunctor F (i ≫ p)).obj M)
    simpa only [HomIsOver.comp_over] using h
  unfold cartierPulledModuleMixedEulerDifference
  rw [heq]

end MixedFujita
