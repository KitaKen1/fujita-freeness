/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierMixedIntersection
public import MixedFujita.CartierGlobalPullback

/-! 非優勢射の実引き戻し直線束と元Cartier交点数の代表元比較。 See reports/check-224-effective-cut-generic-intersection.json for the verified scope. Mixed positivity on the actual cut and the manuscript numerical-dimension dictionary remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Actual Cartier representatives of pulled line bundles preserve every
mixed Euler difference, including the base translate. No dominant map is
required, and no meromorphic Cartier pullback along a closed immersion is used. -/
theorem cartierPulledModuleMixedEulerDifference_unit_eq_of_representations
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [Y.Over (Spec (CommRingCat.of K))] (p : Y ⟶ X)
    {D : List (CartierDivisor X)} {F : List (CartierDivisor Y)}
    (h : List.Forall₂ (fun H J => Nonempty ((Scheme.Modules.pullback p).obj H.sheaf ≅ J.sheaf)) D F)
    (E : CartierDivisor X) (G : CartierDivisor Y)
    (a : (Scheme.Modules.pullback p).obj E.sheaf ≅ G.sheaf) :
    cartierPulledModuleMixedEulerDifference K p (SheafOfModules.unit Y.ringCatSheaf) D E =
      cartierMixedEulerDifference K F G := by
  induction h generalizing E G with
  | nil =>
    exact moduleEulerChar_congr K (rightUnitor ((Scheme.Modules.pullback p).obj E.sheaf) ≪≫ a)
  | @cons H J D F hHJ hDF ih =>
    obtain ⟨b⟩ := hHJ
    change cartierPulledModuleMixedEulerDifference K p
        (SheafOfModules.unit Y.ringCatSheaf) D (E + H) -
      cartierPulledModuleMixedEulerDifference K p (SheafOfModules.unit Y.ringCatSheaf) D E =
        cartierMixedEulerDifference K F (G + J) - cartierMixedEulerDifference K F G
    exact congrArg₂ (· - ·)
      (ih (E + H) (G + J)
        ((Scheme.Modules.pullback p).mapIso (cartierTensorSheafIso E H).symm ≪≫
          cartierPullbackTensorIso E p H.sheaf ≪≫ tensorIso a b ≪≫ cartierTensorSheafIso G J))
      (ih E G a)


/-- The ordinary intersection of pulled Cartier bundles is the ordinary
intersection of ANY actual Cartier representatives on the integral source. -/
theorem cartierMixedIntersectionOn_eq_of_representations
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) {D : List (CartierDivisor X)} {F : List (CartierDivisor Y)}
    (h : List.Forall₂ (fun H J => Nonempty ((Scheme.Modules.pullback p).obj H.sheaf ≅ J.sheaf)) D F)
    (hdim : topologicalKrullDim Y = D.length) :
    cartierMixedIntersectionOn K p D hdim =
      cartierMixedIntersection K F (by simpa only [h.length_eq] using hdim) := by
  exact cartierPulledModuleMixedEulerDifference_unit_eq_of_representations K p h 0 0
    ((Scheme.Modules.pullback p).mapIso (cartierZeroSheafIso X) ≪≫
      Scheme.Modules.pullbackObjUnitIso p ≪≫ (cartierZeroSheafIso Y).symm)


/-- Arbitrary finite families of pulled Cartier line bundles have actual
Cartier representatives on an integral source, even for a nondominant map. -/
theorem exists_cartier_direction_representations
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (p : Y ⟶ X) (D : List (CartierDivisor X)) :
    ∃ F : List (CartierDivisor Y), List.Forall₂
      (fun H J => Nonempty ((Scheme.Modules.pullback p).obj H.sheaf ≅ J.sheaf)) D F := by
  induction D with
  | nil => exact ⟨[], .nil⟩
  | cons H D ih =>
    obtain ⟨J, hJ⟩ := cartierPullbackLineBundle_exists_cartierDivisor H p
    obtain ⟨F, hF⟩ := ih
    exact ⟨J :: F, .cons hJ hF⟩


/-- Thus every pulled ordinary intersection on an integral proper source
can be computed as an original ordinary Cartier intersection there. The
representatives and their sheaf isomorphisms are constructed internally. -/
theorem cartierMixedIntersectionOn_exists_original_representatives
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) (D : List (CartierDivisor X)) (hdim : topologicalKrullDim Y = D.length) :
    ∃ (F : List (CartierDivisor Y))
      (h : List.Forall₂ (fun H J => Nonempty ((Scheme.Modules.pullback p).obj H.sheaf ≅ J.sheaf)) D F),
      cartierMixedIntersectionOn K p D hdim =
        cartierMixedIntersection K F (by simpa only [h.length_eq] using hdim) := by
  obtain ⟨F, h⟩ := exists_cartier_direction_representations p D
  exact ⟨F, h, cartierMixedIntersectionOn_eq_of_representations K p h hdim⟩

end MixedFujita
