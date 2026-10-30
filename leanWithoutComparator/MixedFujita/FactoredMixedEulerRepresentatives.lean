/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierMixedIntersectionRepresentatives

/-! 任意係数を保持する実Cartier代表元による基底変更比較。 See reports/check-227-base-dimension-pullback-vanishing.json for the verified scope. Positivity through the base dimension and the original numerical-dimension dictionary remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Changing the integral ambient base using actual representatives preserves
the mixed Euler difference of EVERY coefficient module on an arbitrary source. -/
theorem cartierPulledModuleMixedEulerDifference_eq_of_factor_representations
    (K : Type u) [Field K] {X Z Y : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
    [Y.Over (Spec (CommRingCat.of K))] (i : Z ⟶ X) (q : Y ⟶ Z) (M : Y.Modules)
    {D : List (CartierDivisor X)} {F : List (CartierDivisor Z)}
    (h : List.Forall₂ (fun H J => Nonempty ((Scheme.Modules.pullback i).obj H.sheaf ≅ J.sheaf)) D F)
    (E : CartierDivisor X) (G : CartierDivisor Z)
    (a : (Scheme.Modules.pullback i).obj E.sheaf ≅ G.sheaf) :
    cartierPulledModuleMixedEulerDifference K (q ≫ i) M D E =
      cartierPulledModuleMixedEulerDifference K q M F G := by
  induction h generalizing E G with
  | nil =>
    exact moduleEulerChar_congr K (tensorIso
      (Scheme.Modules.pullbackCompIso' q i (q ≫ i) rfl E.sheaf ≪≫
        (Scheme.Modules.pullback q).mapIso a) (Iso.refl M))
  | @cons H J D F hHJ hDF ih =>
    obtain ⟨b⟩ := hHJ
    change cartierPulledModuleMixedEulerDifference K (q ≫ i) M D (E + H) -
      cartierPulledModuleMixedEulerDifference K (q ≫ i) M D E =
        cartierPulledModuleMixedEulerDifference K q M F (G + J) -
          cartierPulledModuleMixedEulerDifference K q M F G
    exact congrArg₂ (· - ·)
      (ih (E + H) (G + J)
        ((Scheme.Modules.pullback i).mapIso (cartierTensorSheafIso E H).symm ≪≫
          cartierPullbackTensorIso E i H.sheaf ≪≫ tensorIso a b ≪≫ cartierTensorSheafIso G J))
      (ih E G a)

end MixedFujita
