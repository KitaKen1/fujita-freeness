/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CoherentMixedEulerDifference

/-! 非整な閉支持を経由する実混合Euler差分の射影公式。 See reports/check-220-coherent-mixed-euler-devissage.json for the verified scope. Positive-dimensional general mixed Euler nilpotence remains unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- The actual projection formula for an ambient Cartier bundle pulled to
an arbitrary intermediate source. Both intermediate and final sources may
be nonintegral. -/
noncomputable def cartierPulledProjectionFormulaIso
    {X Y Z : Scheme.{u}} [IsIntegral X] (D : CartierDivisor X)
    (p : Y ⟶ X) (i : Z ⟶ Y) (M : Z.Modules) :
    (cartierPullbackTwistFunctor D p).obj ((Scheme.Modules.pushforward i).obj M) ≅
      (Scheme.Modules.pushforward i).obj ((cartierPullbackTwistFunctor D (i ≫ p)).obj M) := by
  let L := (cartierSGALineBundle D).pullback p
  let b : (L.pullback i).toModules 1 ≅ (Scheme.Modules.pullback (i ≫ p)).obj D.sheaf :=
    (sgaLineBundlePullbackPowerIso L i 1).symm ≪≫
      (Scheme.Modules.pullback i).mapIso (cartierPulledSheafSGAPowerOneIso D p) ≪≫
      (Scheme.Modules.pullbackComp i p).app D.sheaf
  exact (cartierPulledTensorSGATwistIso D p ((Scheme.Modules.pushforward i).obj M)).symm ≪≫
    (L.twistPushforwardIso i M 1).symm ≪≫
      (Scheme.Modules.pushforward i).mapIso
        ((sgaTwistTensorIso (L.pullback i) M 1).symm ≪≫ tensorIso b (Iso.refl M))


/-- Along actual closed supports the mixed Euler function is exactly the
one on the original coherent module, with the pulled Cartier directions.
No integrality of the closed support is needed. -/
theorem cartierPulledModuleMixedEulerDifference_closed_pushforward
    (K : Type u) [Field K] {X Y Z : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] [Z.Over (Spec (CommRingCat.of K))]
    [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) (i : Z ⟶ Y) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of K))]
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
